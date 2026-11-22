module

public import Anisotropic.Probability.NormBound.Walks

@[expose] public section

/-!
# Even closed walks with a given number of vertices

A step of the moment method in the proof of Lemma 4.8 (`lem:norm_XX`): the closed bipartite walks
`i₁ μ₁ i₂ μ₂ … μ_k i₁` of length `2k` in which every edge is traversed at least twice and which
visit `v` distinct vertices number at most `9^k (2k)^{6(k+1-v)} max(K,N)^v`.

A walk is encoded by its first vertex and one code per step: the label of the target when the
target is a new vertex; nothing when the step traverses, for the second time, the only edge at its
source that has been traversed exactly once; and an earlier visiting time of the target otherwise.
A potential function bounds the number of steps of the third kind by `6(k+1-v)`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

section WalkCode

open Finset

variable {α : Type*} [DecidableEq α]

/-- number of times `l < j` with `g l = f` -/
private def wcCnt (g : ℕ → α) (j : ℕ) (f : α) : ℕ :=
  ∑ l ∈ range j, if g l = f then 1 else 0

private lemma wcCnt_succ (g : ℕ → α) (j : ℕ) (f : α) :
    wcCnt g (j + 1) f = wcCnt g j f + if g j = f then 1 else 0 := by
  unfold wcCnt
  rw [sum_range_succ]

private lemma wcCnt_zero (g : ℕ → α) (f : α) : wcCnt g 0 f = 0 := by
  simp [wcCnt]

private lemma wcCnt_pos_iff (g : ℕ → α) (j : ℕ) (f : α) :
    0 < wcCnt g j f ↔ ∃ l < j, g l = f := by
  unfold wcCnt
  rw [sum_pos_iff]
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨l, mem_range.1 hl, ?_⟩
    by_contra h'
    simp [h'] at h
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, mem_range.2 hl, by simp⟩

/-- the times `j < n` at which `g j` occurs for the `(r+1)`-st time are as many as the values
occurring more than `r` times in `g 0, …, g (n-1)` -/
private lemma wc_sum_occ [Fintype α] (g : ℕ → α) (r n : ℕ) :
    ∑ j ∈ range n, (if wcCnt g j (g j) = r then 1 else 0) =
      ∑ f : α, if r < wcCnt g n f then 1 else 0 := by
  induction n with
  | zero => simp [wcCnt_zero]
  | succ n ih =>
    rw [sum_range_succ, ih]
    have h : ∀ f : α, (if r < wcCnt g (n + 1) f then 1 else 0) =
        (if r < wcCnt g n f then 1 else 0) +
          if g n = f then (if wcCnt g n f = r then 1 else 0) else 0 := by
      intro f
      rw [wcCnt_succ]
      split_ifs <;> omega
    simp_rw [h]
    rw [sum_add_distrib, sum_ite_eq]
    simp

variable [Fintype α]

/-- the edge traversed by step `l` -/
private def wcE (w : ℕ → α) (l : ℕ) : Sym2 α := s(w l, w (l + 1))

/-- number of edges at `y` traversed exactly once by the steps `< j` -/
private def wcOpen (w : ℕ → α) (j : ℕ) (y : α) : ℕ :=
  ∑ f : Sym2 α, if wcCnt (wcE w) j f = 1 ∧ y ∈ f then 1 else 0

/-- step `j` reaches a vertex not visited at the times `≤ j` -/
private def WcNew (w : ℕ → α) (j : ℕ) : Prop := wcCnt w (j + 1) (w (j + 1)) = 0

private instance (w : ℕ → α) (j : ℕ) : Decidable (WcNew w j) :=
  inferInstanceAs (Decidable (_ = _))

/-- step `j` traverses for the second time the only edge at `w j` traversed exactly once before -/
private def WcForced (w : ℕ → α) (j : ℕ) : Prop :=
  wcCnt (wcE w) j (wcE w j) = 1 ∧ wcOpen w j (w j) = 1

private instance (w : ℕ → α) (j : ℕ) : Decidable (WcForced w j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- potential at time `j` -/
private def wcPot (w : ℕ → α) (j : ℕ) : ℕ :=
  ∑ y : α, (wcOpen w j y - if y = w j then 1 else 2)

/-- indicator of a step to a new vertex -/
private def wcI (w : ℕ → α) (j : ℕ) : ℕ := if WcNew w j then 1 else 0

/-- indicator of a first traversal -/
private def wcNw (w : ℕ → α) (j : ℕ) : ℕ := if wcCnt (wcE w) j (wcE w j) = 0 then 1 else 0

/-- indicator of a second traversal -/
private def wcB1 (w : ℕ → α) (j : ℕ) : ℕ := if wcCnt (wcE w) j (wcE w j) = 1 then 1 else 0

/-- indicator of a third or later traversal -/
private def wcB2 (w : ℕ → α) (j : ℕ) : ℕ := if 2 ≤ wcCnt (wcE w) j (wcE w j) then 1 else 0

/-- indicator of a first traversal ending at a visited vertex -/
private def wcA (w : ℕ → α) (j : ℕ) : ℕ :=
  if wcCnt (wcE w) j (wcE w j) = 0 ∧ ¬ WcNew w j then 1 else 0

/-- indicator of a second traversal from a vertex with at least two edges traversed once -/
private def wcAmb (w : ℕ → α) (j : ℕ) : ℕ :=
  if wcCnt (wcE w) j (wcE w j) = 1 ∧ 2 ≤ wcOpen w j (w j) then 1 else 0

/-- indicator of a step that is neither to a new vertex nor forced -/
private def wcL (w : ℕ → α) (j : ℕ) : ℕ := if ¬ WcNew w j ∧ ¬ WcForced w j then 1 else 0

omit [Fintype α] in
private lemma wc_visit_of_cnt_pos {w : ℕ → α} {j : ℕ} {f : Sym2 α} {y : α}
    (hf : 0 < wcCnt (wcE w) j f) (hy : y ∈ f) : ∃ l ≤ j, w l = y := by
  obtain ⟨l, hl, rfl⟩ := (wcCnt_pos_iff _ _ _).1 hf
  rcases Sym2.mem_iff.1 hy with rfl | rfl
  · exact ⟨l, by omega, rfl⟩
  · exact ⟨l + 1, by omega, rfl⟩

omit [Fintype α] in
private lemma wcNew_ne {w : ℕ → α} {j l : ℕ} (h : WcNew w j) (hl : l ≤ j) :
    w l ≠ w (j + 1) := by
  intro he
  have : 0 < wcCnt w (j + 1) (w (j + 1)) := (wcCnt_pos_iff _ _ _).2 ⟨l, by omega, he⟩
  unfold WcNew at h
  omega

omit [Fintype α] in
private lemma wc_exists_visit {w : ℕ → α} {j : ℕ} (h : ¬ WcNew w j) :
    ∃ l, l ≤ j ∧ w l = w (j + 1) := by
  unfold WcNew at h
  obtain ⟨l, hl, he⟩ := (wcCnt_pos_iff _ _ _).1 (Nat.pos_of_ne_zero h)
  exact ⟨l, by omega, he⟩

omit [Fintype α] in
private lemma wcNew_cnt {w : ℕ → α} {j : ℕ} (h : WcNew w j) :
    wcCnt (wcE w) j (wcE w j) = 0 := by
  by_contra hne
  have hm : w (j + 1) ∈ wcE w j := by unfold wcE; exact Sym2.mem_mk_right _ _
  obtain ⟨l, hl, hw⟩ := wc_visit_of_cnt_pos (Nat.pos_of_ne_zero hne) hm
  exact wcNew_ne h hl hw

private lemma wcNew_open {w : ℕ → α} {j : ℕ} (h : WcNew w j) : wcOpen w j (w (j + 1)) = 0 := by
  unfold wcOpen
  refine sum_eq_zero fun f _ => ?_
  rw [ite_eq_right]
  rintro ⟨h1, hy⟩
  obtain ⟨l, hl, hw⟩ := wc_visit_of_cnt_pos (by omega : 0 < wcCnt (wcE w) j f) hy
  exact wcNew_ne h hl hw

private lemma wcOpen_pos {w : ℕ → α} {j : ℕ} (h : wcCnt (wcE w) j (wcE w j) = 1) :
    1 ≤ wcOpen w j (w j) := by
  unfold wcOpen
  have hm : w j ∈ wcE w j := by unfold wcE; exact Sym2.mem_mk_left _ _
  calc 1 = (if wcCnt (wcE w) j (wcE w j) = 1 ∧ w j ∈ wcE w j then 1 else 0) := by
        rw [ite_eq_left ⟨h, hm⟩]
    _ ≤ _ := single_le_sum (f := fun f => if wcCnt (wcE w) j f = 1 ∧ w j ∈ f then 1 else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ _)

/-- update of the number of edges traversed exactly once at `y` -/
private lemma wcOpen_succ (w : ℕ → α) (j : ℕ) (y : α) :
    wcOpen w (j + 1) y + (if wcCnt (wcE w) j (wcE w j) = 1 ∧ y ∈ wcE w j then 1 else 0) =
      wcOpen w j y + (if wcCnt (wcE w) j (wcE w j) = 0 ∧ y ∈ wcE w j then 1 else 0) := by
  have key : ∀ f : Sym2 α,
      (if wcCnt (wcE w) (j + 1) f = 1 ∧ y ∈ f then 1 else 0) +
          (if wcE w j = f then (if wcCnt (wcE w) j f = 1 ∧ y ∈ f then 1 else 0) else 0) =
        (if wcCnt (wcE w) j f = 1 ∧ y ∈ f then 1 else 0) +
          (if wcE w j = f then (if wcCnt (wcE w) j f = 0 ∧ y ∈ f then 1 else 0) else 0) := by
    intro f
    rw [wcCnt_succ]
    by_cases hy : y ∈ f
    · by_cases hf : wcE w j = f
      · simp only [hf, ite_true, hy, and_true]
        split_ifs <;> omega
      · simp only [hf, ite_false, hy, and_true, add_zero]
    · simp only [hy, and_false, ite_false, ite_self]
  have hs := sum_congr rfl (fun f (_ : f ∈ (univ : Finset (Sym2 α))) => key f)
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq, sum_ite_eq] at hs
  simpa only [wcOpen, mem_univ, ite_true] using hs

private lemma wcPot_step (w : ℕ → α) (j : ℕ) (hadj : w j ≠ w (j + 1)) :
    wcPot w (j + 1) + wcAmb w j ≤ wcPot w j + (2 * wcA w j + wcB2 w j) := by
  have hpt : ∀ y : α,
      (wcOpen w (j + 1) y - if y = w (j + 1) then 1 else 2) +
          (if y = w j then wcAmb w j else 0) ≤
        (wcOpen w j y - if y = w j then 1 else 2) +
          (if y = w (j + 1) then 2 * wcA w j + wcB2 w j else 0) := by
    intro y
    have hO := wcOpen_succ w j y
    have hmem : y ∈ wcE w j ↔ y = w j ∨ y = w (j + 1) := Sym2.mem_iff
    unfold wcAmb wcA wcB2
    by_cases hu : y = w j
    · have hx : ¬ y = w (j + 1) := hu ▸ hadj
      have hm : y ∈ wcE w j := hmem.2 (Or.inl hu)
      simp only [eq_true hm, and_true, eq_true hu, ite_true, eq_false hx, ite_false] at hO ⊢
      rw [← hu]
      split_ifs at hO ⊢ <;> omega
    · by_cases hx : y = w (j + 1)
      · have hm : y ∈ wcE w j := hmem.2 (Or.inr hx)
        simp only [eq_true hm, and_true, eq_false hu, ite_false, eq_true hx, ite_true] at hO ⊢
        by_cases hn : WcNew w j
        · have h0 := wcNew_open hn
          have hc := wcNew_cnt hn
          rw [← hx] at h0
          simp only [hn, not_true_eq_false, and_false, ite_false]
          split_ifs at hO ⊢ <;> omega
        · simp only [hn, not_false_eq_true, and_true]
          split_ifs at hO ⊢ <;> omega
      · have hm : y ∉ wcE w j := fun h => (hmem.1 h).elim hu hx
        simp only [hm, and_false, ite_false, hu, hx, add_zero] at hO ⊢
        omega
  have hs := sum_le_sum (fun y (_ : y ∈ (univ : Finset α)) => hpt y)
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq'] at hs
  simpa only [wcPot, mem_univ, ite_true] using hs

private lemma wc_amb_le (w : ℕ → α) (n : ℕ) (hadj : ∀ j < n, w j ≠ w (j + 1)) :
    ∑ j ∈ range n, wcAmb w j ≤ ∑ j ∈ range n, (2 * wcA w j + wcB2 w j) := by
  have key : ∀ m, m ≤ n →
      wcPot w m + ∑ j ∈ range m, wcAmb w j ≤ ∑ j ∈ range m, (2 * wcA w j + wcB2 w j) := by
    intro m
    induction m with
    | zero => intro _; simp [wcPot, wcOpen, wcCnt_zero]
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := wcPot_step w m (hadj m (by omega))
      rw [sum_range_succ, sum_range_succ]
      omega
  have := key n le_rfl
  omega

private lemma wcL_le (w : ℕ → α) (j : ℕ) : wcL w j ≤ wcA w j + wcB2 w j + wcAmb w j := by
  unfold wcL wcA wcB2 wcAmb WcForced
  by_cases hn : WcNew w j
  · simp [hn]
  · by_cases hc : wcCnt (wcE w) j (wcE w j) = 1
    · have := wcOpen_pos hc
      simp only [hn, not_false_eq_true, true_and, and_true]
      split_ifs <;> omega
    · simp only [hn, not_false_eq_true, and_true, hc, false_and, ite_false]
      split_ifs <;> omega

omit [Fintype α] in
private lemma wcI_add_wcA (w : ℕ → α) (j : ℕ) : wcI w j + wcA w j = wcNw w j := by
  unfold wcI wcA wcNw
  by_cases hn : WcNew w j
  · simp [hn, wcNew_cnt hn]
  · simp only [hn, ite_false, not_false_eq_true, and_true, zero_add]

omit [Fintype α] in
private lemma wcNw_add (w : ℕ → α) (j : ℕ) : wcNw w j + wcB1 w j + wcB2 w j = 1 := by
  unfold wcNw wcB1 wcB2
  split_ifs <;> omega

/-- the number of steps neither to a new vertex nor forced is at most `6(k+1-v)` -/
private lemma wc_L_le (w : ℕ → α) (k : ℕ) (hadj : ∀ j < 2 * k, w j ≠ w (j + 1))
    (hev : ∀ f, wcCnt (wcE w) (2 * k) f ≠ 1) :
    ∑ j ∈ range (2 * k), wcL w j ≤ 6 * (k + 1 - (∑ j ∈ range (2 * k), wcI w j + 1)) := by
  have h1 : ∑ j ∈ range (2 * k), wcL w j ≤
      ∑ j ∈ range (2 * k), (wcA w j + wcB2 w j + wcAmb w j) :=
    sum_le_sum fun j _ => wcL_le w j
  have h2 : ∑ j ∈ range (2 * k), (wcI w j + wcA w j) = ∑ j ∈ range (2 * k), wcNw w j :=
    sum_congr rfl fun j _ => wcI_add_wcA w j
  have h3 : ∑ j ∈ range (2 * k), (wcNw w j + wcB1 w j + wcB2 w j) =
      ∑ j ∈ range (2 * k), 1 :=
    sum_congr rfl fun j _ => wcNw_add w j
  have h4 := wc_amb_le w (2 * k) hadj
  have h5 : ∑ j ∈ range (2 * k), wcNw w j = ∑ j ∈ range (2 * k), wcB1 w j := by
    simp only [wcNw, wcB1]
    rw [wc_sum_occ (wcE w) 0 (2 * k), wc_sum_occ (wcE w) 1 (2 * k)]
    refine sum_congr rfl fun f _ => ?_
    have := hev f
    split_ifs <;> omega
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one, ← mul_sum] at h1 h2 h3 h4
  omega

/-- the code of step `j`: a label for a new vertex, `none` for a forced step, and otherwise the
first visiting time of the target -/
private def wcCode {L : Type*} (w : ℕ → α) (ℓ : α → L) (n : ℕ) (j : Fin n) :
    Option (L ⊕ Fin n) :=
  if WcNew w j then some (Sum.inl (ℓ (w (j + 1))))
  else if WcForced w j then none
  else if h : ∃ l, l ≤ (j : ℕ) ∧ w l = w (j + 1) then
    some (Sum.inr ⟨Nat.find h, lt_of_le_of_lt (Nat.find_spec h).1 j.2⟩)
  else none

private lemma wcCode_inl {L : Type*} {w : ℕ → α} {ℓ : α → L} {n : ℕ} {j : Fin n} {a : L}
    (h : wcCode w ℓ n j = some (Sum.inl a)) : WcNew w j ∧ ℓ (w (j + 1)) = a := by
  unfold wcCode at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq, Sum.inl.injEq] at h
    exact ⟨h1, h⟩
  all_goals simp at h

private lemma wcCode_none {L : Type*} {w : ℕ → α} {ℓ : α → L} {n : ℕ} {j : Fin n}
    (h : wcCode w ℓ n j = none) : WcForced w j := by
  unfold wcCode at h
  split_ifs at h with h1 h2 h3
  · exact h2
  · exact absurd (wc_exists_visit h1) h3

private lemma wcCode_inr {L : Type*} {w : ℕ → α} {ℓ : α → L} {n : ℕ} {j t : Fin n}
    (h : wcCode w ℓ n j = some (Sum.inr t)) : (t : ℕ) ≤ j ∧ w t = w (j + 1) := by
  unfold wcCode at h
  split_ifs at h with h1 h2 h3
  · simp at h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    rw [← h]
    exact Nat.find_spec h3

/-- indicator of a label code -/
private def wcLab {L T : Type*} : Option (L ⊕ T) → ℕ
  | some (Sum.inl _) => 1
  | _ => 0

/-- indicator of a time code -/
private def wcTgt {L T : Type*} : Option (L ⊕ T) → ℕ
  | some (Sum.inr _) => 1
  | _ => 0

private lemma wcLab_code {L : Type*} (w : ℕ → α) (ℓ : α → L) (n : ℕ) (j : Fin n) :
    wcLab (wcCode w ℓ n j) = wcI w j := by
  unfold wcCode wcI
  split_ifs <;> rfl

private lemma wcTgt_code {L : Type*} (w : ℕ → α) (ℓ : α → L) (n : ℕ) (j : Fin n) :
    wcTgt (wcCode w ℓ n j) = wcL w j := by
  unfold wcCode wcL
  by_cases h1 : WcNew w j
  · rw [ite_eq_left h1, ite_eq_right (fun h => h.1 h1)]
    rfl
  · by_cases h2 : WcForced w j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (fun h => h.2 h2)]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h2, dite_eq_left (wc_exists_visit h1), ite_eq_left ⟨h1, h2⟩]
      rfl

/-- if two walks agree up to time `j` and step `j` is forced in both, they agree at `j + 1` -/
private lemma wcForced_eq {w w' : ℕ → α} {j : ℕ} (hag : ∀ l ≤ j, w l = w' l)
    (h : WcForced w j) (h' : WcForced w' j) : w (j + 1) = w' (j + 1) := by
  have hE : ∀ l < j, wcE w l = wcE w' l := fun l hl => by
    unfold wcE
    rw [hag l (by omega), hag (l + 1) (by omega)]
  have hC : ∀ f, wcCnt (wcE w) j f = wcCnt (wcE w') j f := fun f => by
    unfold wcCnt
    exact sum_congr rfl fun l hl => by rw [hE l (mem_range.1 hl)]
  have hu : w j = w' j := hag j le_rfl
  have hS : ((univ : Finset (Sym2 α)).filter
      fun f => wcCnt (wcE w) j f = 1 ∧ w j ∈ f).card ≤ 1 := by
    have := h.2
    unfold wcOpen at this
    rw [card_filter]
    omega
  have m1 : wcE w j ∈ (univ : Finset (Sym2 α)).filter
      fun f => wcCnt (wcE w) j f = 1 ∧ w j ∈ f :=
    mem_filter.2 ⟨mem_univ _, h.1, by unfold wcE; exact Sym2.mem_mk_left _ _⟩
  have m2 : wcE w' j ∈ (univ : Finset (Sym2 α)).filter
      fun f => wcCnt (wcE w) j f = 1 ∧ w j ∈ f :=
    mem_filter.2 ⟨mem_univ _, by rw [hC]; exact h'.1,
      by rw [hu]; unfold wcE; exact Sym2.mem_mk_left _ _⟩
  have := card_le_one.1 hS _ m1 _ m2
  unfold wcE at this
  rw [hu] at this
  exact Sym2.congr_right.1 this

private lemma wc_one_le {x : ℝ} (hx : 1 ≤ x) {p a : ℕ} (h : p ≤ a) : 1 ≤ x ^ a * x⁻¹ ^ p := by
  have hx0 : x ≠ 0 := by positivity
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hx0),
    mul_one]
  exact one_le_pow₀ hx

/-- codes with at most `a` labels and at most `b` times number at most `3^n |L|^a |T|^b` -/
private lemma wc_card_codes {L T : Type*} [Fintype L] [Fintype T] (n a b : ℕ)
    (hL : 1 ≤ Fintype.card L) (hT : 1 ≤ Fintype.card T) :
    (((univ : Finset (Fin n → Option (L ⊕ T))).filter fun c =>
        ∑ j, wcLab (c j) ≤ a ∧ ∑ j, wcTgt (c j) ≤ b).card : ℝ) ≤
      3 ^ n * (Fintype.card L : ℝ) ^ a * (Fintype.card T : ℝ) ^ b := by
  set x : ℝ := (Fintype.card L : ℝ) with hxdef
  set y : ℝ := (Fintype.card T : ℝ) with hydef
  have hx : (1 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hL
  have hy : (1 : ℝ) ≤ y := by rw [hydef]; exact_mod_cast hT
  have hx0 : x ≠ 0 := by positivity
  have hy0 : y ≠ 0 := by positivity
  have hsum : ∑ o : Option (L ⊕ T), x⁻¹ ^ wcLab o * y⁻¹ ^ wcTgt o = 3 := by
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    simp only [wcLab, wcTgt, pow_one, pow_zero, mul_one, one_mul, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← hxdef, ← hydef, mul_inv_cancel₀ hx0, mul_inv_cancel₀ hy0]
    norm_num
  have hprod : ∀ c : Fin n → Option (L ⊕ T),
      ∏ j, (x⁻¹ ^ wcLab (c j) * y⁻¹ ^ wcTgt (c j)) =
        x⁻¹ ^ (∑ j, wcLab (c j)) * y⁻¹ ^ (∑ j, wcTgt (c j)) := by
    intro c
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum]
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n → Option (L ⊕ T)), F = (univ.filter fun c =>
      ∑ j, wcLab (c j) ≤ a ∧ ∑ j, wcTgt (c j) ≤ b) := ⟨_, rfl⟩
  rw [← hF, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have h1 : ∑ c ∈ F, (1 : ℝ) ≤
      ∑ c ∈ F, x ^ a * y ^ b * ∏ j, (x⁻¹ ^ wcLab (c j) * y⁻¹ ^ wcTgt (c j)) := by
    refine sum_le_sum fun c hc => ?_
    rw [hF] at hc
    obtain ⟨ha, hb⟩ := (mem_filter.1 hc).2
    rw [hprod]
    have := mul_le_mul (wc_one_le hx ha) (wc_one_le hy hb) zero_le_one (by positivity)
    linarith
  have h2 : ∑ c ∈ F, x ^ a * y ^ b * ∏ j, (x⁻¹ ^ wcLab (c j) * y⁻¹ ^ wcTgt (c j)) ≤
      ∑ c : Fin n → Option (L ⊕ T), x ^ a * y ^ b * ∏ j, (x⁻¹ ^ wcLab (c j) * y⁻¹ ^ wcTgt (c j)) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
  have h3 : ∑ c : Fin n → Option (L ⊕ T),
      x ^ a * y ^ b * ∏ j, (x⁻¹ ^ wcLab (c j) * y⁻¹ ^ wcTgt (c j)) = 3 ^ n * x ^ a * y ^ b := by
    rw [← mul_sum, ← Fintype.sum_pow (fun o : Option (L ⊕ T) => x⁻¹ ^ wcLab o * y⁻¹ ^ wcTgt o),
      hsum]
    ring
  linarith

end WalkCode

section WalkSeq

open Finset

variable {k K N : ℕ} [NeZero k]

/-- the vertex sequence `i₁, μ₁, i₂, μ₂, …` of the walk, periodic with period `2k` -/
private def wcW (i : Fin k → Fin K) (μ : Fin k → Fin N) (j : ℕ) : Fin K ⊕ Fin N :=
  if j % 2 = 0 then Sum.inl (i (Fin.ofNat k (j / 2))) else Sum.inr (μ (Fin.ofNat k (j / 2)))

private lemma wcW_even (i : Fin k → Fin K) (μ : Fin k → Fin N) (t : ℕ) :
    wcW i μ (2 * t) = Sum.inl (i (Fin.ofNat k t)) := by
  unfold wcW
  rw [ite_eq_left (by omega), show 2 * t / 2 = t by omega]

private lemma wcW_odd (i : Fin k → Fin K) (μ : Fin k → Fin N) (t : ℕ) :
    wcW i μ (2 * t + 1) = Sum.inr (μ (Fin.ofNat k t)) := by
  unfold wcW
  rw [ite_eq_right (by omega), show (2 * t + 1) / 2 = t by omega]

private lemma wc_ofNat_val (t : Fin k) : Fin.ofNat k t.val = t := by
  ext
  simp

private lemma wc_ofNat_succ (t : Fin k) : Fin.ofNat k (t.val + 1) = finRotate k t := by
  ext
  simp [finRotate_apply, Fin.val_add, Nat.add_mod]

private lemma wcW_adj (i : Fin k → Fin K) (μ : Fin k → Fin N) (j : ℕ) :
    wcW i μ j ≠ wcW i μ (j + 1) := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [wcW_even, wcW_odd]
    exact Sum.inl_ne_inr
  · rw [wcW_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, wcW_even]
    exact Sum.inr_ne_inl

private lemma wcW_period (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    wcW i μ (2 * k) = wcW i μ 0 := by
  rw [wcW_even, show (0 : ℕ) = 2 * 0 by rfl, wcW_even]
  congr 2
  ext
  simp

private lemma wc_sum_two_mul (g : ℕ → ℕ) (k : ℕ) :
    ∑ j ∈ range (2 * k), g j = ∑ t ∈ range k, (g (2 * t) + g (2 * t + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

private lemma wcCnt_mult (i : Fin k → Fin K) (μ : Fin k → Fin N) (a : Fin K) (b : Fin N) :
    wcCnt (wcE (wcW i μ)) (2 * k) s(Sum.inl a, Sum.inr b) = walkMult i μ a b := by
  unfold wcCnt walkMult
  rw [wc_sum_two_mul, ← Fin.sum_univ_eq_sum_range, sum_add_distrib, card_filter, card_filter]
  congr 1
  · refine sum_congr rfl fun t _ => ?_
    rw [wcE, wcW_even, wcW_odd, wc_ofNat_val]
    simp
  · refine sum_congr rfl fun t _ => ?_
    rw [wcE, wcW_odd, show 2 * (t : ℕ) + 1 + 1 = 2 * ((t : ℕ) + 1) by ring, wcW_even,
      wc_ofNat_val, wc_ofNat_succ]
    simp [and_comm]

private lemma wc_even (i : Fin k → Fin K) (μ : Fin k → Fin N) (hev : IsEvenWalk i μ)
    (f : Sym2 (Fin K ⊕ Fin N)) : wcCnt (wcE (wcW i μ)) (2 * k) f ≠ 1 := by
  intro h1
  obtain ⟨l, -, hlf⟩ := (wcCnt_pos_iff _ _ _).1 (by omega : 0 < wcCnt (wcE (wcW i μ)) (2 * k) f)
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' l
  · have hf : f = s(Sum.inl (i (Fin.ofNat k t)), Sum.inr (μ (Fin.ofNat k t))) := by
      rw [← hlf, wcE, wcW_even, wcW_odd]
    rw [hf, wcCnt_mult] at h1
    exact hev _ _ h1
  · have hf : f = s(Sum.inl (i (Fin.ofNat k (t + 1))), Sum.inr (μ (Fin.ofNat k t))) := by
      rw [← hlf, wcE, wcW_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, wcW_even, Sym2.eq_swap]
    rw [hf, wcCnt_mult] at h1
    exact hev _ _ h1

private lemma wc_verts (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    (∑ y : Fin K ⊕ Fin N, if 0 < wcCnt (wcW i μ) (2 * k) y then 1 else 0) = walkVerts i μ := by
  rw [Fintype.sum_sum_type]
  unfold walkVerts
  congr 1
  · rw [← card_filter]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_image, wcCnt_pos_iff]
    constructor
    · rintro ⟨l, hl, hw⟩
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' l
      · rw [wcW_even] at hw
        exact ⟨_, Sum.inl_injective hw⟩
      · rw [wcW_odd] at hw
        exact absurd hw Sum.inr_ne_inl
    · rintro ⟨t, rfl⟩
      refine ⟨2 * t, by omega, ?_⟩
      rw [wcW_even, wc_ofNat_val]
  · rw [← card_filter]
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_image, wcCnt_pos_iff]
    constructor
    · rintro ⟨l, hl, hw⟩
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' l
      · rw [wcW_even] at hw
        exact absurd hw Sum.inl_ne_inr
      · rw [wcW_odd] at hw
        exact ⟨_, Sum.inr_injective hw⟩
    · rintro ⟨t, rfl⟩
      refine ⟨2 * t + 1, by omega, ?_⟩
      rw [wcW_odd, wc_ofNat_val]

/-- the number of steps to a new vertex is `walkVerts - 1` -/
private lemma wc_I_add_one (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    ∑ j ∈ range (2 * k), wcI (wcW i μ) j + 1 = walkVerts i μ := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (NeZero.ne k)
  have h := wc_sum_occ (wcW i μ) 0 (2 * k + 1)
  rw [sum_range_succ', wcCnt_zero, ite_eq_left rfl] at h
  rw [← wc_verts]
  have e : ∀ y, (if 0 < wcCnt (wcW i μ) (2 * k + 1) y then 1 else 0) =
      (if 0 < wcCnt (wcW i μ) (2 * k) y then 1 else 0) := by
    intro y
    rw [wcCnt_succ, wcW_period]
    by_cases hy : wcW i μ 0 = y
    · have : 0 < wcCnt (wcW i μ) (2 * k) y := (wcCnt_pos_iff _ _ _).2 ⟨0, by omega, hy⟩
      split_ifs <;> omega
    · simp only [hy, ite_false, add_zero]
  simp only [e] at h
  rw [← h]
  rfl

/-- labels of the vertices in `Fin (max K N)` -/
private def wcLabel (K N : ℕ) : Fin K ⊕ Fin N → Fin (max K N) :=
  Sum.elim (Fin.castLE (le_max_left K N)) (Fin.castLE (le_max_right K N))

private lemma wcLabel_eq {i i' : Fin k → Fin K} {μ μ' : Fin k → Fin N} (j : ℕ)
    (h : wcLabel K N (wcW i μ j) = wcLabel K N (wcW i' μ' j)) : wcW i μ j = wcW i' μ' j := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [wcW_even, wcW_even] at h ⊢
    simp only [wcLabel, Sum.elim_inl] at h
    rw [Fin.castLE_injective _ h]
  · rw [wcW_odd, wcW_odd] at h ⊢
    simp only [wcLabel, Sum.elim_inr] at h
    rw [Fin.castLE_injective _ h]

/-- the encoding by the first vertex and the step codes is injective -/
private lemma wc_inj {i i' : Fin k → Fin K} {μ μ' : Fin k → Fin N} (h0 : i 0 = i' 0)
    (hc : wcCode (wcW i μ) (wcLabel K N) (2 * k) = wcCode (wcW i' μ') (wcLabel K N) (2 * k)) :
    i = i' ∧ μ = μ' := by
  have hall : ∀ j, j ≤ 2 * k → ∀ l ≤ j, wcW i μ l = wcW i' μ' l := by
    intro j
    induction j with
    | zero =>
      intro _ l hl
      obtain rfl : l = 0 := by omega
      rw [show (0 : ℕ) = 2 * 0 by rfl, wcW_even, wcW_even]
      simp only [Fin.ofNat_zero]
      rw [h0]
    | succ m ih =>
      intro hm l hl
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge l (m + 1) with hl' | hl'
      · exact ih' l (by omega)
      obtain rfl : l = m + 1 := by omega
      have hcm := congrFun hc ⟨m, by omega⟩
      rcases hcode : wcCode (wcW i μ) (wcLabel K N) (2 * k) ⟨m, by omega⟩ with _ | (a | t)
      · rw [hcode] at hcm
        exact wcForced_eq ih' (wcCode_none hcode) (wcCode_none hcm.symm)
      · rw [hcode] at hcm
        have h1 := wcCode_inl hcode
        have h2 := wcCode_inl hcm.symm
        exact wcLabel_eq _ (h1.2.trans h2.2.symm)
      · rw [hcode] at hcm
        have h1 := wcCode_inr hcode
        have h2 := wcCode_inr hcm.symm
        rw [← h1.2, ← h2.2]
        exact ih' t h1.1
  constructor
  · funext t
    have := hall (2 * k) le_rfl (2 * t) (by omega)
    rw [wcW_even, wcW_even, wc_ofNat_val] at this
    exact Sum.inl_injective this
  · funext t
    have := hall (2 * k) le_rfl (2 * t + 1) (by omega)
    rw [wcW_odd, wcW_odd, wc_ofNat_val] at this
    exact Sum.inr_injective this

end WalkSeq

open Classical in
/-- Even closed walks of length `2k` with `v` vertices number at most
`9^k (2k)^{6(k+1-v)} max(K,N)^v`. -/
theorem card_evenWalk_le {k K N : ℕ} (hk : 1 ≤ k) (v : ℕ) :
    (((Finset.univ : Finset ((Fin k → Fin K) × (Fin k → Fin N))).filter
        fun w => IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = v).card : ℝ) ≤
      9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * (k + 1 - v)) * (max K N : ℝ) ^ v := by
  have : NeZero k := ⟨by omega⟩
  set S := (Finset.univ : Finset ((Fin k → Fin K) × (Fin k → Fin N))).filter
    fun w => IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = v with hS
  have hRHS : (0 : ℝ) ≤ 9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * (k + 1 - v)) * (max K N : ℝ) ^ v := by
    have : (0 : ℝ) ≤ (max K N : ℝ) := le_max_of_le_left (Nat.cast_nonneg K)
    positivity
  rcases S.eq_empty_or_nonempty with hE | ⟨p, hp⟩
  · rw [hE, Finset.card_empty, Nat.cast_zero]
    exact hRHS
  have hp' := (Finset.mem_filter.1 hp).2
  have hv1 : 1 ≤ v := by
    rw [← hp'.2, ← wc_I_add_one]
    omega
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h => by
    subst h
    exact (p.1 0).elim0
  set T := (Finset.univ : Finset (Fin (2 * k) → Option (Fin (max K N) ⊕ Fin (2 * k)))).filter
    fun c => ∑ j, wcLab (c j) ≤ v - 1 ∧ ∑ j, wcTgt (c j) ≤ 6 * (k + 1 - v) with hT
  set U := (Finset.univ : Finset (Fin K)) ×ˢ T with hU
  have hmaps : Set.MapsTo (fun p : (Fin k → Fin K) × (Fin k → Fin N) =>
      (p.1 0, wcCode (wcW p.1 p.2) (wcLabel K N) (2 * k))) S U := by
    intro q hq
    have hq' := (Finset.mem_filter.1 hq).2
    have hI := wc_I_add_one q.1 q.2
    have hL := wc_L_le (wcW q.1 q.2) k (fun j _ => wcW_adj q.1 q.2 j)
      (wc_even q.1 q.2 hq'.1)
    refine Finset.mem_coe.2 <| Finset.mem_product.2
      ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · simp only [wcLab_code]
      rw [Fin.sum_univ_eq_sum_range (fun j => wcI (wcW q.1 q.2) j)]
      omega
    · simp only [wcTgt_code]
      rw [Fin.sum_univ_eq_sum_range (fun j => wcL (wcW q.1 q.2) j)]
      omega
  have hinj : Set.InjOn (fun p : (Fin k → Fin K) × (Fin k → Fin N) =>
      (p.1 0, wcCode (wcW p.1 p.2) (wcLabel K N) (2 * k))) S := by
    rintro ⟨i, μ⟩ - ⟨i', μ'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := wc_inj h.1 h.2
    rw [h1, h2]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [hU, Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  have hTc := wc_card_codes (L := Fin (max K N)) (T := Fin (2 * k)) (2 * k) (v - 1)
    (6 * (k + 1 - v)) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
  simp only [Fintype.card_fin] at hTc
  have hKM : (K : ℝ) ≤ (max K N : ℝ) := le_max_left _ _
  calc (S.card : ℝ) ≤ (K : ℝ) * (T.card : ℝ) := by exact_mod_cast hcard
    _ ≤ (max K N : ℝ) * (3 ^ (2 * k) * ((max K N : ℕ) : ℝ) ^ (v - 1) *
          ((2 * k : ℕ) : ℝ) ^ (6 * (k + 1 - v))) :=
        mul_le_mul hKM hTc (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg K) hKM)
    _ = 9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * (k + 1 - v)) * (max K N : ℝ) ^ v := by
      rw [Nat.cast_max, pow_mul]
      obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      norm_num
      ring

open Classical in
/-- At `k = 2`, `K = N = 2`, `v = 2`: the even walks with two vertices are the four walks
`i₁ μ₁ i₁ μ₁ i₁`, and the bound equals `9^2 · 4^6 · 2^2 = 1327104`. -/
example :
    ((Finset.univ : Finset ((Fin 2 → Fin 2) × (Fin 2 → Fin 2))).filter
        fun w => IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = 2).card = 4 ∧
    (((Finset.univ : Finset ((Fin 2 → Fin 2) × (Fin 2 → Fin 2))).filter
        fun w => IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = 2).card : ℝ) ≤
      9 ^ 2 * ((2 * 2 : ℕ) : ℝ) ^ (6 * (2 + 1 - 2)) * (max (2 : ℕ) (2 : ℕ) : ℝ) ^ 2 ∧
    9 ^ 2 * ((2 * 2 : ℕ) : ℝ) ^ (6 * (2 + 1 - 2)) * (max (2 : ℕ) (2 : ℕ) : ℝ) ^ 2 = 1327104 := by
  refine ⟨?_, card_evenWalk_le (by norm_num) 2, by norm_num⟩
  have : (@Finset.filter _ (fun w : (Fin 2 → Fin 2) × (Fin 2 → Fin 2) =>
      IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = 2) (fun w =>
        inferInstanceAs (Decidable ((∀ a b, walkMult w.1 w.2 a b ≠ 1) ∧ walkVerts w.1 w.2 = 2)))
      Finset.univ).card = 4 := by
    decide
  convert this

end Anisotropic
