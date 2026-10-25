import Mathlib

/-!
# The graph bound for sums over labellings

The combinatorial bound behind the moment expansions of the large deviation estimates for linear
and quadratic forms in independent centred entries, which the paper cites in Sections 5, 6 and 8.
Vertices are labelled by elements of a finite set `ι`; each 2-edge carries a nonnegative matrix,
each 1-edge a nonnegative vector, and every vertex has degree at least two. The sum over all
labellings of the product of the weights is at most the product of the Frobenius norms of the
matrices and the Euclidean norms of the vectors.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- Cauchy–Schwarz for a product of at least two nonnegative functions of one label:
`∑ₓ ∏_{k ∈ I} g_k(x) ≤ ∏_{k ∈ I} ‖g_k‖₂` when `I` has at least two elements. -/
private lemma graphBound_sum_prod_le {ι κ : Type*} [Fintype ι] (I : Finset κ) (hI : 2 ≤ I.card)
    (g : κ → ι → ℝ) (hg : ∀ k ∈ I, ∀ x, 0 ≤ g k x) :
    ∑ x, ∏ k ∈ I, g k x ≤ ∏ k ∈ I, Real.sqrt (∑ x, g k x ^ 2) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ I, ∃ b ∈ I, a ≠ b := Finset.one_lt_card.1 hI
  have hb' : b ∈ I.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have hsplit : ∀ h : κ → ℝ,
      ∏ k ∈ I, h k = h a * (h b * ∏ k ∈ (I.erase a).erase b, h k) := fun h => by
    rw [Finset.mul_prod_erase (I.erase a) h hb', Finset.mul_prod_erase I h ha]
  have hJ : ∀ k ∈ (I.erase a).erase b, k ∈ I :=
    fun k hk => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)
  calc ∑ x, ∏ k ∈ I, g k x
      ≤ ∑ x, g a x * g b x * ∏ k ∈ (I.erase a).erase b, Real.sqrt (∑ y, g k y ^ 2) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [hsplit (fun k => g k x), ← mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hg a ha x) (hg b hb x))
        refine Finset.prod_le_prod₀ (fun k hk => hg k (hJ k hk) x) fun k hk => ?_
        exact (Real.le_sqrt (hg k (hJ k hk) x)
          (Finset.sum_nonneg fun y _ => sq_nonneg _)).2
          (Finset.single_le_sum (f := fun y => g k y ^ 2) (fun y _ => sq_nonneg _)
            (Finset.mem_univ x))
    _ = (∑ x, g a x * g b x) * ∏ k ∈ (I.erase a).erase b, Real.sqrt (∑ y, g k y ^ 2) := by
        rw [Finset.sum_mul]
    _ ≤ (Real.sqrt (∑ x, g a x ^ 2) * Real.sqrt (∑ x, g b x ^ 2)) *
          ∏ k ∈ (I.erase a).erase b, Real.sqrt (∑ y, g k y ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
          (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
    _ = ∏ k ∈ I, Real.sqrt (∑ x, g k x ^ 2) := by
        rw [hsplit (fun k => Real.sqrt (∑ x, g k x ^ 2)), mul_assoc]

/-- The graph bound on `Fin (m + 1)` with 2-edges indexed by a finset `S2` and 1-edges indexed by
a finset `S1`, the degree of a vertex written as a sum of incidence indicators. -/
private lemma graphBound_fin_succ {ι : Type*} [Fintype ι] (m : ℕ) :
    ∀ (α β : Type) (S2 : Finset α) (S1 : Finset β) (src dst : α → Fin (m + 1))
      (at_ : β → Fin (m + 1)) (B : α → ι → ι → ℝ) (r : β → ι → ℝ),
      (∀ e ∈ S2, src e ≠ dst e) → (∀ e ∈ S2, ∀ i j, 0 ≤ B e i j) →
      (∀ f ∈ S1, ∀ i, 0 ≤ r f i) →
      (∀ w, 2 ≤ ∑ e ∈ S2, ((if src e = w then 1 else 0) + (if dst e = w then 1 else 0)) +
        ∑ f ∈ S1, (if at_ f = w then 1 else 0)) →
      ∑ v : Fin (m + 1) → ι, (∏ e ∈ S2, B e (v (src e)) (v (dst e))) *
          ∏ f ∈ S1, r f (v (at_ f)) ≤
        (∏ e ∈ S2, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) *
          ∏ f ∈ S1, Real.sqrt (∑ i, r f i ^ 2) := by
  induction m with
  | zero =>
    intro α β S2 S1 src dst at_ B r hloop hB hr hdeg
    classical
    have hsub : ∀ a b : Fin (0 + 1), a = b := fun a b => Fin.ext (by omega)
    have hS2 : S2 = ∅ :=
      Finset.eq_empty_of_forall_notMem fun e he => hloop e he (hsub _ _)
    subst hS2
    have hat : ∀ f, at_ f = 0 := fun f => hsub _ _
    have hcard : 2 ≤ S1.card := by
      have := hdeg 0
      simpa [hat] using this
    simp only [Finset.prod_empty, one_mul, hat]
    calc ∑ v : Fin (0 + 1) → ι, ∏ f ∈ S1, r f (v 0) = ∑ x, ∏ f ∈ S1, r f x :=
          Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ (fun v => rfl)
      _ ≤ _ := graphBound_sum_prod_le S1 hcard r hr
  | succ m ih =>
    intro α β S2 S1 src dst at_ B r hloop hB hr hdeg
    classical
    -- `pr` removes the vertex `0`, sending `j.succ` to `j`
    set pr : Fin (m + 2) → Fin (m + 1) := fun i => Fin.cases 0 id i with hpr_def
    have hpr_succ : ∀ j : Fin (m + 1), pr j.succ = j := fun j => rfl
    have hpr : ∀ i : Fin (m + 2), i ≠ 0 → (pr i).succ = i := by
      intro i hi
      cases i using Fin.cases with
      | zero => exact absurd rfl hi
      | succ j => rfl
    have hsucc_iff : ∀ i : Fin (m + 2), i ≠ 0 → ∀ u, (i = u.succ ↔ pr i = u) := by
      intro i hi u
      constructor
      · rintro rfl; rfl
      · rintro rfl; exact (hpr i hi).symm
    have hcons : ∀ (x : ι) (v' : Fin (m + 1) → ι) (i : Fin (m + 2)), i ≠ 0 →
        (Fin.cons x v' : Fin (m + 2) → ι) i = v' (pr i) := by
      intro x v' i hi
      cases i using Fin.cases with
      | zero => exact absurd rfl hi
      | succ j => rfl
    -- incidence with the vertex `0`, the other endpoint, and the folded matrix entry
    set inc : α → Prop := fun e => src e = 0 ∨ dst e = 0 with hinc
    set oth : α → Fin (m + 2) := fun e => if src e = 0 then dst e else src e with hoth
    set gf : α → ι → ι → ℝ := fun e y x => if src e = 0 then B e x y else B e y x with hgf
    have hgf_nonneg : ∀ e ∈ S2, ∀ y x, 0 ≤ gf e y x := by
      intro e he y x
      simp only [hgf]
      split_ifs
      · exact hB e he x y
      · exact hB e he y x
    have hoth_ne : ∀ e ∈ S2, inc e → oth e ≠ 0 := by
      intro e he hie
      simp only [hoth]
      split_ifs with hs
      · exact fun hd => hloop e he (hs.trans hd.symm)
      · exact hs
    -- the reduced configuration on `Fin (m + 1)`
    set S2' : Finset α := S2.filter (fun e => ¬ inc e) with hS2'
    set S1' : Finset (β ⊕ α) :=
      (S1.filter (fun f => ¬ at_ f = 0)).disjSum (S2.filter inc) with hS1'
    set at' : β ⊕ α → Fin (m + 1) := Sum.elim (fun f => pr (at_ f)) (fun e => pr (oth e))
      with hat'
    set r' : β ⊕ α → ι → ℝ :=
      Sum.elim r (fun e y => Real.sqrt (∑ x, gf e y x ^ 2)) with hr'
    have key := ih α (β ⊕ α) S2' S1' (fun e => pr (src e)) (fun e => pr (dst e)) at' B r'
      ?loop ?nonnegB ?nonnegr ?deg
    case loop =>
      intro e he hpe
      obtain ⟨he, hni⟩ := Finset.mem_filter.1 he
      have hs : src e ≠ 0 := fun h => hni (Or.inl h)
      have hd : dst e ≠ 0 := fun h => hni (Or.inr h)
      exact hloop e he (by rw [← hpr _ hs, ← hpr _ hd]; exact congrArg Fin.succ hpe)
    case nonnegB =>
      intro e he
      exact hB e (Finset.mem_filter.1 he).1
    case nonnegr =>
      intro k hk i
      rcases Finset.mem_disjSum.1 hk with ⟨f, hf, rfl⟩ | ⟨e, he, rfl⟩
      · exact hr f (Finset.mem_filter.1 hf).1 i
      · exact Real.sqrt_nonneg _
    case deg =>
      intro u
      have h := hdeg u.succ
      rw [Finset.sum_disjSum]
      rw [← Finset.sum_filter_add_sum_filter_not S2 inc,
        ← Finset.sum_filter_add_sum_filter_not S1 (fun f => at_ f = 0)] at h
      have e1 : ∑ e ∈ S2.filter (fun e => ¬ inc e),
          ((if src e = u.succ then 1 else 0) + (if dst e = u.succ then 1 else 0)) =
          ∑ e ∈ S2', ((if pr (src e) = u then 1 else 0) + (if pr (dst e) = u then 1 else 0)) := by
        refine Finset.sum_congr rfl fun e he => ?_
        have hni := (Finset.mem_filter.1 he).2
        have hs : src e ≠ 0 := fun h => hni (Or.inl h)
        have hd : dst e ≠ 0 := fun h => hni (Or.inr h)
        simp only [hsucc_iff _ hs u, hsucc_iff _ hd u]
      have e2 : ∑ e ∈ S2.filter inc,
          ((if src e = u.succ then 1 else 0) + (if dst e = u.succ then 1 else 0)) =
          ∑ e ∈ S2.filter inc, (if at' (Sum.inr e) = u then 1 else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        obtain ⟨he, hie⟩ := Finset.mem_filter.1 he
        simp only [hat', Sum.elim_inr, hoth]
        by_cases hs : src e = 0
        · have hd : dst e ≠ 0 := fun hd => hloop e he (hs.trans hd.symm)
          simp only [hs, ite_true, (Fin.succ_ne_zero u).symm, ite_false, zero_add,
            hsucc_iff _ hd u]
        · have hd : dst e = 0 := hie.resolve_left hs
          simp only [hs, hd, ite_false, (Fin.succ_ne_zero u).symm, add_zero, hsucc_iff _ hs u]
      have e3 : ∑ f ∈ S1.filter (fun f => at_ f = 0), (if at_ f = u.succ then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun f hf => ?_
        rw [(Finset.mem_filter.1 hf).2,
          ite_eq_right_iff.2 fun h => absurd h (Fin.succ_ne_zero u).symm]
      have e4 : ∑ f ∈ S1.filter (fun f => ¬ at_ f = 0), (if at_ f = u.succ then 1 else 0) =
          ∑ f ∈ S1.filter (fun f => ¬ at_ f = 0), (if at' (Sum.inl f) = u then 1 else 0) := by
        refine Finset.sum_congr rfl fun f hf => ?_
        simp only [hat', Sum.elim_inl, hsucc_iff _ (Finset.mem_filter.1 hf).2 u]
      rw [e2] at h
      omega
    -- split off the label of the vertex `0`
    have hsplit : ∀ F : (Fin (m + 2) → ι) → ℝ,
        ∑ v, F v = ∑ v' : Fin (m + 1) → ι, ∑ x : ι, F (Fin.cons x v') := by
      intro F
      rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    -- the items at the vertex `0`, as functions of its label
    set I : Finset (α ⊕ β) := (S2.filter inc).disjSum (S1.filter (fun f => at_ f = 0)) with hI_def
    set G : (Fin (m + 1) → ι) → α ⊕ β → ι → ℝ :=
      fun v' => Sum.elim (fun e x => gf e (v' (pr (oth e))) x) r with hG
    have hI : 2 ≤ I.card := by
      have h0 := hdeg 0
      rw [hI_def, Finset.card_disjSum, Finset.card_filter, Finset.card_filter]
      have : ∑ e ∈ S2, ((if src e = 0 then 1 else 0) + (if dst e = 0 then 1 else 0)) =
          ∑ e ∈ S2, (if inc e then 1 else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        have hl := hloop e he
        by_cases hs : src e = 0 <;> by_cases hd : dst e = 0
        · exact absurd (hs.trans hd.symm) hl
        · simp [hinc, hs, hd]
        · simp [hinc, hs, hd]
        · simp [hinc, hs, hd]
      rw [this] at h0
      exact h0
    have hG_nonneg : ∀ v', ∀ k ∈ I, ∀ x, 0 ≤ G v' k x := by
      intro v' k hk x
      rcases Finset.mem_disjSum.1 hk with ⟨e, he, rfl⟩ | ⟨f, hf, rfl⟩
      · exact hgf_nonneg e (Finset.mem_filter.1 he).1 _ _
      · exact hr f (Finset.mem_filter.1 hf).1 x
    set K : ℝ := ∏ f ∈ S1.filter (fun f => at_ f = 0), Real.sqrt (∑ i, r f i ^ 2) with hK
    have hstep : ∀ v' : Fin (m + 1) → ι,
        ∑ x : ι, (∏ e ∈ S2, B e ((Fin.cons x v' : Fin (m + 2) → ι) (src e))
            ((Fin.cons x v' : Fin (m + 2) → ι) (dst e))) *
          ∏ f ∈ S1, r f ((Fin.cons x v' : Fin (m + 2) → ι) (at_ f)) ≤
        K * ((∏ e ∈ S2', B e (v' (pr (src e))) (v' (pr (dst e)))) *
          ∏ k ∈ S1', r' k (v' (at' k))) := by
      intro v'
      set P : ℝ := ∏ e ∈ S2', B e (v' (pr (src e))) (v' (pr (dst e))) with hP
      set Q : ℝ := ∏ f ∈ S1.filter (fun f => ¬ at_ f = 0), r f (v' (pr (at_ f))) with hQ
      have hPQ : 0 ≤ P * Q :=
        mul_nonneg (Finset.prod_nonneg fun e he => hB e (Finset.mem_filter.1 he).1 _ _)
          (Finset.prod_nonneg fun f hf => hr f (Finset.mem_filter.1 hf).1 _)
      have hx : ∀ x : ι,
          (∏ e ∈ S2, B e ((Fin.cons x v' : Fin (m + 2) → ι) (src e))
            ((Fin.cons x v' : Fin (m + 2) → ι) (dst e))) *
          ∏ f ∈ S1, r f ((Fin.cons x v' : Fin (m + 2) → ι) (at_ f)) =
          (P * Q) * ∏ k ∈ I, G v' k x := by
        intro x
        rw [hI_def, Finset.prod_disjSum]
        simp only [hG, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.prod_filter_mul_prod_filter_not S2 inc,
          ← Finset.prod_filter_mul_prod_filter_not S1 (fun f => at_ f = 0)]
        have h1 : ∀ e ∈ S2.filter inc, B e ((Fin.cons x v' : Fin (m + 2) → ι) (src e))
            ((Fin.cons x v' : Fin (m + 2) → ι) (dst e)) = gf e (v' (pr (oth e))) x := by
          intro e he
          obtain ⟨he, hie⟩ := Finset.mem_filter.1 he
          simp only [hgf, hoth]
          by_cases hs : src e = 0
          · have hd : dst e ≠ 0 := fun hd => hloop e he (hs.trans hd.symm)
            simp only [hs, ↓reduceIte]
            rw [hcons x v' _ hd, Fin.cons_zero]
          · have hd : dst e = 0 := hie.resolve_left hs
            simp only [hs, ↓reduceIte]
            rw [hd, hcons x v' _ hs, Fin.cons_zero]
        have h2 : ∀ e ∈ S2.filter (fun e => ¬ inc e),
            B e ((Fin.cons x v' : Fin (m + 2) → ι) (src e))
              ((Fin.cons x v' : Fin (m + 2) → ι) (dst e)) =
            B e (v' (pr (src e))) (v' (pr (dst e))) := by
          intro e he
          have hni := (Finset.mem_filter.1 he).2
          rw [hcons x v' _ fun h => hni (Or.inl h), hcons x v' _ fun h => hni (Or.inr h)]
        have h3 : ∀ f ∈ S1.filter (fun f => at_ f = 0),
            r f ((Fin.cons x v' : Fin (m + 2) → ι) (at_ f)) = r f x := by
          intro f hf
          rw [(Finset.mem_filter.1 hf).2, Fin.cons_zero]
        have h4 : ∀ f ∈ S1.filter (fun f => ¬ at_ f = 0),
            r f ((Fin.cons x v' : Fin (m + 2) → ι) (at_ f)) = r f (v' (pr (at_ f))) := by
          intro f hf
          rw [hcons x v' _ (Finset.mem_filter.1 hf).2]
        rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_congr rfl h3,
          Finset.prod_congr rfl h4, hP, hQ]
        ring
      calc _ = ∑ x : ι, (P * Q) * ∏ k ∈ I, G v' k x := Finset.sum_congr rfl fun x _ => hx x
        _ = (P * Q) * ∑ x : ι, ∏ k ∈ I, G v' k x := (Finset.mul_sum _ _ _).symm
        _ ≤ (P * Q) * ∏ k ∈ I, Real.sqrt (∑ x, G v' k x ^ 2) :=
          mul_le_mul_of_nonneg_left (graphBound_sum_prod_le I hI (G v') (hG_nonneg v')) hPQ
        _ = _ := by
          rw [hI_def, Finset.prod_disjSum, hS1', Finset.prod_disjSum]
          simp only [hG, hr', hat', Sum.elim_inl, Sum.elim_inr]
          ring
    have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
    have hnorm : ∀ e ∈ S2.filter inc,
        Real.sqrt (∑ i, r' (Sum.inr e) i ^ 2) = Real.sqrt (∑ i, ∑ j, B e i j ^ 2) := by
      intro e _
      congr 1
      simp only [hr', Sum.elim_inr]
      rw [Finset.sum_congr rfl fun y _ =>
        Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg (gf e y x))]
      simp only [hgf]
      by_cases hs : src e = 0
      · simp only [hs, ↓reduceIte]
        exact Finset.sum_comm
      · simp only [hs, ↓reduceIte]
    calc _ = ∑ v' : Fin (m + 1) → ι, ∑ x : ι,
          (∏ e ∈ S2, B e ((Fin.cons x v' : Fin (m + 2) → ι) (src e))
            ((Fin.cons x v' : Fin (m + 2) → ι) (dst e))) *
          ∏ f ∈ S1, r f ((Fin.cons x v' : Fin (m + 2) → ι) (at_ f)) := hsplit _
      _ ≤ ∑ v' : Fin (m + 1) → ι, K * ((∏ e ∈ S2', B e (v' (pr (src e))) (v' (pr (dst e)))) *
          ∏ k ∈ S1', r' k (v' (at' k))) := Finset.sum_le_sum fun v' _ => hstep v'
      _ = K * ∑ v' : Fin (m + 1) → ι, (∏ e ∈ S2', B e (v' (pr (src e))) (v' (pr (dst e)))) *
          ∏ k ∈ S1', r' k (v' (at' k)) := (Finset.mul_sum _ _ _).symm
      _ ≤ K * ((∏ e ∈ S2', Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) *
          ∏ k ∈ S1', Real.sqrt (∑ i, r' k i ^ 2)) := mul_le_mul_of_nonneg_left key hK0
      _ = _ := by
        rw [hS1', Finset.prod_disjSum, Finset.prod_congr rfl hnorm]
        simp only [hr', Sum.elim_inl]
        rw [← Finset.prod_filter_mul_prod_filter_not S2 inc,
          ← Finset.prod_filter_mul_prod_filter_not S1 (fun f => at_ f = 0), hK, hS2']
        ring

/-- The graph bound: vertices `Fin n`, 2-edges `src e → dst e` without loops carrying
nonnegative matrices, 1-edges at `at f` carrying nonnegative vectors, every vertex of degree
at least two. The sum over all labellings is at most the product of the Frobenius and
Euclidean norms. -/
theorem graph_sum_le {ι : Type*} [Fintype ι] {n E F : ℕ} (src dst : Fin E → Fin n)
    (hloop : ∀ e, src e ≠ dst e) (B : Fin E → ι → ι → ℝ) (hB : ∀ e i j, 0 ≤ B e i j)
    (at_ : Fin F → Fin n) (r : Fin F → ι → ℝ) (hr : ∀ f i, 0 ≤ r f i)
    (hdeg : ∀ w, 2 ≤ (Finset.univ.filter (src · = w)).card +
      (Finset.univ.filter (dst · = w)).card + (Finset.univ.filter (at_ · = w)).card) :
    ∑ v : Fin n → ι, (∏ e, B e (v (src e)) (v (dst e))) * ∏ f, r f (v (at_ f)) ≤
      (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) := by
  cases n with
  | zero =>
    have : IsEmpty (Fin E) := ⟨fun e => (src e).elim0⟩
    have : IsEmpty (Fin F) := ⟨fun f => (at_ f).elim0⟩
    simp
  | succ m =>
    refine graphBound_fin_succ m (Fin E) (Fin F) Finset.univ Finset.univ src dst at_ B r
      (fun e _ => hloop e) (fun e _ => hB e) (fun f _ => hr f) fun w => ?_
    have h := hdeg w
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib] at h
    exact h

/-- The graph bound at a configuration on two vertices with one 2-edge `0 → 1` carrying
`!![1, 2; 3, 4]` and two 1-edges carrying `(1, 2)` at `0` and `(2, 1)` at `1`, every vertex of
degree exactly two. -/
example :
    ∑ v : Fin 2 → Fin 2,
        (∏ e : Fin 1, (fun (_ : Fin 1) (i j : Fin 2) => (!![(1 : ℝ), 2; 3, 4] : Matrix _ _ ℝ) i j)
          e (v (![0] e)) (v (![1] e))) *
        ∏ f : Fin 2, (![![(1 : ℝ), 2], ![2, 1]] : Fin 2 → Fin 2 → ℝ) f (v (![0, 1] f)) ≤
      (∏ e : Fin 1, Real.sqrt (∑ i, ∑ j,
          (fun (_ : Fin 1) (i j : Fin 2) => (!![(1 : ℝ), 2; 3, 4] : Matrix _ _ ℝ) i j) e i j ^ 2)) *
        ∏ f : Fin 2, Real.sqrt (∑ i, (![![(1 : ℝ), 2], ![2, 1]] : Fin 2 → Fin 2 → ℝ) f i ^ 2) := by
  refine graph_sum_le (n := 2) ![0] ![1] (by decide) _ ?_ ![0, 1] _ ?_ (by decide)
  · intro _ i j
    fin_cases i <;> fin_cases j <;> norm_num
  · intro f i
    fin_cases f <;> fin_cases i <;> norm_num

/-- The left-hand side of the graph bound at the configuration above equals `24`; the
right-hand side is `5 * √30`. -/
example : ∑ v : Fin 2 → Fin 2,
        (∏ e : Fin 1, (fun (_ : Fin 1) (i j : Fin 2) => (!![(1 : ℝ), 2; 3, 4] : Matrix _ _ ℝ) i j)
          e (v (![0] e)) (v (![1] e))) *
        ∏ f : Fin 2, (![![(1 : ℝ), 2], ![2, 1]] : Fin 2 → Fin 2 → ℝ) f (v (![0, 1] f)) = 24 := by
  rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, ← (Fin.consEquiv (fun _ => Fin 2)).sum_comp,
    Fintype.sum_prod_type, Fin.consEquiv]
  norm_num

end Anisotropic

#print axioms Anisotropic.graph_sum_le
