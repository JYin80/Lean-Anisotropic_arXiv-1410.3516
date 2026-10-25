import Mathlib

/-!
# Closed bipartite walks

Closed walks `i₁ μ₁ i₂ μ₂ … μ_k i₁` in the complete bipartite graph on `Fin K` and `Fin N`:
the multiplicity of an edge, the edge set, the vertex count, evenness, the expansion of
`tr (Y Yᵀ)^k` as a sum over walks, and the counts `|V| ≤ |E| + 1` and `|E| ≤ k` for even walks.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- path through `a, j 0, …, j (n-1), b` -/
private def walksPath {ι : Type*} {n : ℕ} (a : ι) (j : Fin n → ι) (b : ι) : Fin (n + 2) → ι :=
  Fin.snoc (Fin.cons a j : Fin (n + 1) → ι) b

private lemma walksPath_cons {ι : Type*} {n : ℕ} (a c : ι) (j : Fin n → ι) (b : ι) :
    walksPath a (Fin.cons c j : Fin (n + 1) → ι) b = Fin.cons a (walksPath c j b) := by
  unfold walksPath
  rw [Fin.cons_snoc_eq_snoc_cons]

private lemma walksPath_apply_castSucc {ι : Type*} {n : ℕ} (a : ι) (j : Fin n → ι) (b : ι)
    (t : Fin (n + 1)) : walksPath a j b t.castSucc = (Fin.cons a j : Fin (n + 1) → ι) t := by
  unfold walksPath
  exact Fin.snoc_castSucc (α := fun _ => ι) b _ t

private lemma walksPath_last {ι : Type*} {n : ℕ} (a : ι) (j : Fin n → ι) (b : ι) :
    walksPath a j b (Fin.last (n + 1)) = b := by
  unfold walksPath
  exact Fin.snoc_last (α := fun _ => ι) b _

/-- weight of a path -/
private def walksWeight {R ι : Type*} [CommSemiring R] {n : ℕ} (A : Matrix ι ι R)
    (p : Fin (n + 2) → ι) : R :=
  ∏ t : Fin (n + 1), A (p t.castSucc) (p t.succ)

private lemma walksWeight_cons {R ι : Type*} [CommSemiring R] {n : ℕ} (A : Matrix ι ι R)
    (a : ι) (p : Fin (n + 2) → ι) :
    walksWeight A (Fin.cons a p : Fin (n + 3) → ι) = A a (p 0) * walksWeight A p := by
  unfold walksWeight
  rw [Fin.prod_univ_succ]
  congr 1

private lemma walksPow_apply {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (n : ℕ) (a b : ι) :
    (A ^ (n + 1)) a b = ∑ j : Fin n → ι, walksWeight A (walksPath a j b) := by
  induction n generalizing a with
  | zero =>
    rw [pow_one, Fintype.sum_unique]
    unfold walksWeight
    rw [Fin.prod_univ_one, walksPath_apply_castSucc]
    exact congrArg (A a) (walksPath_last a (default : Fin 0 → ι) b).symm
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.consEquiv_apply, walksPath_cons, walksWeight_cons]
    congr 2

private lemma walksTrace_pow {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (n : ℕ) :
    trace (A ^ (n + 1)) =
      ∑ i : Fin (n + 1) → ι, ∏ t, A (i t) (i (finRotate (n + 1) t)) := by
  simp_rw [trace, diag_apply, walksPow_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.consEquiv_apply]
  unfold walksWeight
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [walksPath_apply_castSucc]
  congr 1
  induction t using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, walksPath_last, finRotate_last]
    simp
  | cast s =>
    rw [Fin.succ_castSucc, walksPath_apply_castSucc]
    simp [finRotate_apply, Fin.coeSucc_eq_succ]

/-- Trace expansion: `tr (Y Yᵀ)^k = ∑_{i,μ} ∏_t Y_{i_t μ_t} Y_{i_{t+1} μ_t}`. -/
theorem trace_pow_eq_sum_walks {k K N : ℕ} (hk : 1 ≤ k) (Y : Matrix (Fin K) (Fin N) ℝ) :
    trace ((Y * Yᵀ) ^ k) =
      ∑ i : Fin k → Fin K, ∑ μ : Fin k → Fin N,
        ∏ t, Y (i t) (μ t) * Y (i (finRotate k t)) (μ t) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [walksTrace_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Matrix.mul_apply, transpose_apply]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin N)))
    (fun t μ => Y (i t) μ * Y (i (finRotate (n + 1) t)) μ), Fintype.piFinset_univ]


/-- edge set of the first `n` steps of a walk given by sequences `x`, `y` -/
private def walksEdgesUpTo {α β : Type*} [DecidableEq α] [DecidableEq β] (x : ℕ → α) (y : ℕ → β)
    (n : ℕ) : Finset (α × β) :=
  (Finset.range n).image (fun t => (x t, y t)) ∪ (Finset.range n).image (fun t => (x (t + 1), y t))

private lemma walksEdgesUpTo_succ {α β : Type*} [DecidableEq α] [DecidableEq β] (x : ℕ → α)
    (y : ℕ → β) (n : ℕ) :
    walksEdgesUpTo x y (n + 1) =
      insert (x n, y n) (insert (x (n + 1), y n) (walksEdgesUpTo x y n)) := by
  ext e
  simp only [walksEdgesUpTo, Finset.range_add_one, Finset.image_insert, Finset.mem_union,
    Finset.mem_insert]
  tauto

private lemma walksEdgesUpTo_fst {α β : Type*} [DecidableEq α] [DecidableEq β] (x : ℕ → α)
    (y : ℕ → β) (n : ℕ) {e : α × β} (he : e ∈ walksEdgesUpTo x y n) :
    e.1 ∈ (Finset.range (n + 1)).image x := by
  simp only [walksEdgesUpTo, Finset.mem_union, Finset.mem_image, Finset.mem_range] at he ⊢
  rcases he with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨t, by omega, rfl⟩
  · exact ⟨t + 1, by omega, rfl⟩

private lemma walksEdgesUpTo_snd {α β : Type*} [DecidableEq α] [DecidableEq β] (x : ℕ → α)
    (y : ℕ → β) (n : ℕ) {e : α × β} (he : e ∈ walksEdgesUpTo x y n) :
    e.2 ∈ (Finset.range n).image y := by
  simp only [walksEdgesUpTo, Finset.mem_union, Finset.mem_image, Finset.mem_range] at he ⊢
  rcases he with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨t, ht, rfl⟩
  · exact ⟨t, ht, rfl⟩

private lemma walksChain_card {α β : Type*} [DecidableEq α] [DecidableEq β] (x : ℕ → α)
    (y : ℕ → β) (n : ℕ) :
    ((Finset.range (n + 1)).image x).card + ((Finset.range n).image y).card ≤
      (walksEdgesUpTo x y n).card + 1 := by
  induction n with
  | zero => simp [walksEdgesUpTo]
  | succ n ih =>
    have hV' : (Finset.range (n + 1 + 1)).image x =
        insert (x (n + 1)) ((Finset.range (n + 1)).image x) := by
      rw [Finset.range_add_one (n := n + 1), Finset.image_insert]
    have hW' : (Finset.range (n + 1)).image y = insert (y n) ((Finset.range n).image y) := by
      rw [Finset.range_add_one, Finset.image_insert]
    have hxn : x n ∈ (Finset.range (n + 1)).image x := Finset.mem_image.2 ⟨n, by simp, rfl⟩
    have hfst : ∀ e ∈ walksEdgesUpTo x y n, e.1 ∈ (Finset.range (n + 1)).image x :=
      fun e he => walksEdgesUpTo_fst x y n he
    have hsnd : ∀ e ∈ walksEdgesUpTo x y n, e.2 ∈ (Finset.range n).image y :=
      fun e he => walksEdgesUpTo_snd x y n he
    rw [hV', hW', walksEdgesUpTo_succ]
    generalize (Finset.range (n + 1)).image x = V at *
    generalize (Finset.range n).image y = W at *
    generalize walksEdgesUpTo x y n = E at *
    have hEsub : E ⊆ insert (x n, y n) (insert (x (n + 1), y n) E) := fun e he => by simp [he]
    by_cases h1 : y n ∈ W <;> by_cases h2 : x (n + 1) ∈ V
    · rw [Finset.insert_eq_of_mem h1, Finset.insert_eq_of_mem h2]
      have := Finset.card_le_card hEsub
      omega
    · have e2 : (x (n + 1), y n) ∉ E := fun h => h2 (hfst _ h)
      rw [Finset.insert_eq_of_mem h1, Finset.card_insert_of_notMem h2]
      have : (insert (x (n + 1), y n) E).card ≤
          (insert (x n, y n) (insert (x (n + 1), y n) E)).card := Finset.card_le_card
        (Finset.subset_insert _ _)
      rw [Finset.card_insert_of_notMem e2] at this
      omega
    · have e1 : (x n, y n) ∉ E := fun h => h1 (hsnd _ h)
      rw [Finset.insert_eq_of_mem h2, Finset.card_insert_of_notMem h1]
      have : (insert (x n, y n) E).card ≤
          (insert (x n, y n) (insert (x (n + 1), y n) E)).card :=
        Finset.card_le_card (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      rw [Finset.card_insert_of_notMem e1] at this
      omega
    · have e1 : (x n, y n) ∉ insert (x (n + 1), y n) E := by
        intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact h2 (by have := congrArg Prod.fst h; simp only at this; rw [← this]; exact hxn)
        · exact h1 (hsnd _ h)
      have e2 : (x (n + 1), y n) ∉ E := fun h => h2 (hfst _ h)
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2]
      omega

/-- Closed bipartite walk `i₁ μ₁ i₂ μ₂ … μ_k i₁`: multiplicity of the edge `{a, b}`. -/
def walkMult {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) (a : Fin K) (b : Fin N) : ℕ :=
  (Finset.univ.filter fun t => i t = a ∧ μ t = b).card +
    (Finset.univ.filter fun t => i (finRotate k t) = a ∧ μ t = b).card

/-- The set of edges of the walk. -/
def walkEdges {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) : Finset (Fin K × Fin N) :=
  Finset.univ.image (fun t => (i t, μ t)) ∪ Finset.univ.image (fun t => (i (finRotate k t), μ t))

/-- The number of distinct vertices of the walk. -/
def walkVerts {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) : ℕ :=
  (Finset.univ.image i).card + (Finset.univ.image μ).card

/-- Every edge of the walk is traversed at least twice. -/
def IsEvenWalk {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) : Prop :=
  ∀ a b, walkMult i μ a b ≠ 1

private lemma walks_ofNat_succ {k : ℕ} [NeZero k] (t : Fin k) :
    Fin.ofNat k (t.val + 1) = finRotate k t := by
  ext
  simp [finRotate_apply, Fin.val_add, Nat.add_mod]

private lemma walks_sum_fiber {k : ℕ} {α : Type*} [Fintype α] [DecidableEq α] (g : Fin k → α) :
    ∑ e : α, (Finset.univ.filter fun t => g t = e).card = k := by
  have := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin k))
    (Finset.univ : Finset α) g
  simpa using this

private lemma walks_sum_mult {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    ∑ e : Fin K × Fin N, walkMult i μ e.1 e.2 = 2 * k := by
  unfold walkMult
  rw [Finset.sum_add_distrib]
  have h1 := walks_sum_fiber (fun t => (i t, μ t))
  have h2 := walks_sum_fiber (fun t => (i (finRotate k t), μ t))
  simp only [Prod.ext_iff] at h1 h2
  rw [h1, h2]
  ring

/-- A closed walk has at most one vertex more than edges; an even walk has at most `k` edges. -/
theorem walkVerts_le {k K N : ℕ} (hk : 1 ≤ k) (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    walkVerts i μ ≤ (walkEdges i μ).card + 1 ∧
      (IsEvenWalk i μ → (walkEdges i μ).card ≤ k) := by
  have : NeZero k := ⟨by omega⟩
  constructor
  · set x : ℕ → Fin K := fun t => i (Fin.ofNat k t) with hx
    set y : ℕ → Fin N := fun t => μ (Fin.ofNat k t) with hy
    have hxi : ∀ s : Fin k, i s = x s.val := fun s => by simp [hx]
    have hyi : ∀ s : Fin k, μ s = y s.val := fun s => by simp [hy]
    have hV : Finset.univ.image i ⊆ (Finset.range (k + 1)).image x := by
      intro a ha
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 ha
      exact Finset.mem_image.2 ⟨s.val, Finset.mem_range.2 (by omega), (hxi s).symm⟩
    have hW : Finset.univ.image μ ⊆ (Finset.range k).image y := by
      intro a ha
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 ha
      exact Finset.mem_image.2 ⟨s.val, Finset.mem_range.2 s.2, (hyi s).symm⟩
    have hE : walksEdgesUpTo x y k ⊆ walkEdges i μ := by
      intro e he
      simp only [walksEdgesUpTo, Finset.mem_union, Finset.mem_image, Finset.mem_range] at he
      unfold walkEdges
      rw [Finset.mem_union]
      rcases he with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · left
        refine Finset.mem_image.2 ⟨⟨t, ht⟩, Finset.mem_univ _, ?_⟩
        exact Prod.ext (hxi ⟨t, ht⟩) (hyi ⟨t, ht⟩)
      · right
        refine Finset.mem_image.2 ⟨⟨t, ht⟩, Finset.mem_univ _, ?_⟩
        have := walks_ofNat_succ (⟨t, ht⟩ : Fin k)
        exact Prod.ext (by change _ = i (Fin.ofNat k (t + 1)); rw [this]) (hyi ⟨t, ht⟩)
    have h := walksChain_card x y k
    have h1 := Finset.card_le_card hV
    have h2 := Finset.card_le_card hW
    have h3 := Finset.card_le_card hE
    unfold walkVerts
    omega
  · intro hev
    have hmem : ∀ e ∈ walkEdges i μ, 2 ≤ walkMult i μ e.1 e.2 := by
      intro e he
      have hne := hev e.1 e.2
      have hpos : 0 < walkMult i μ e.1 e.2 := by
        unfold walkMult
        unfold walkEdges at he
        rcases Finset.mem_union.1 he with he | he
        · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 he
          have : 0 < (Finset.univ.filter fun s => i s = (i t, μ t).1 ∧ μ s = (i t, μ t).2).card :=
            Finset.card_pos.2 ⟨t, by simp⟩
          omega
        · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 he
          have : 0 < (Finset.univ.filter fun s => i (finRotate k s) = (i (finRotate k t), μ t).1 ∧
              μ s = (i (finRotate k t), μ t).2).card :=
            Finset.card_pos.2 ⟨t, by simp⟩
          omega
      omega
    have h1 := Finset.card_nsmul_le_sum (walkEdges i μ) (fun e => walkMult i μ e.1 e.2) 2 hmem
    have h2 := Finset.sum_le_sum_of_subset (f := fun e : Fin K × Fin N => walkMult i μ e.1 e.2)
      (Finset.subset_univ (walkEdges i μ))
    rw [walks_sum_mult] at h2
    simp only [smul_eq_mul] at h1
    omega

/-- Trace expansion at `k = 2`, `K = N = 2`, `Y = [[1, 2], [3, 4]]`: both sides equal `892`. -/
example :
    trace (((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 2; 3, 4])ᵀ) ^ 2) =
      ∑ i : Fin 2 → Fin 2, ∑ μ : Fin 2 → Fin 2,
        ∏ t, (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) (i t) (μ t) *
          (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) (i (finRotate 2 t)) (μ t) ∧
    trace (((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 2; 3, 4])ᵀ) ^ 2) = 892 := by
  refine ⟨trace_pow_eq_sum_walks (by norm_num) _, ?_⟩
  have hY : ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 2; 3, 4])ᵀ) =
      !![5, 11; 11, 25] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [hY, pow_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

/-- Walk `i = (0, 0)`, `μ = (0, 1)` with `k = 2`, `K = N = 2`: an even walk with `3` vertices
and `2` edges, so both bounds are attained. -/
example :
    IsEvenWalk (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2) ∧
      walkVerts (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2) = 3 ∧
      (walkEdges (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2)).card = 2 ∧
      walkVerts (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2) ≤
        (walkEdges (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2)).card + 1 ∧
      (walkEdges (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2)).card ≤ 2 := by
  have hev : IsEvenWalk (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2) := by
    unfold IsEvenWalk walkMult
    decide
  have h := walkVerts_le (by norm_num : 1 ≤ 2) (![0, 0] : Fin 2 → Fin 2) (![0, 1] : Fin 2 → Fin 2)
  refine ⟨hev, by unfold walkVerts; decide, by unfold walkEdges; decide, h.1, h.2 hev⟩

end Anisotropic
