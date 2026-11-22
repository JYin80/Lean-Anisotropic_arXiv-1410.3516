module

public import Anisotropic.Comparison.TaggedWords

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Degree counting (§8.5): Lemma 8.10, the tuple counts, (main_comb_est) with (sigma_leq_d 2) -/

private theorem degreeCount_sum_nMu {k : ℕ} (w : Word (k + 1)) :
    ∑ l : Fin (k + 2), nMu (factorX w l) (factorY w l) = k + 1 := by
  have h1 : ∀ l : Fin (k + 2), nMu (factorX w l) (factorY w l) =
      (if factorX w l = .M then 1 else 0) + (if factorY w l = .M then 1 else 0) := fun l => rfl
  simp only [h1, Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun l => if factorX w l = .M then 1 else 0),
    Fin.sum_univ_castSucc (fun l => if factorY w l = .M then 1 else 0)]
  have hx0 : factorX w 0 = .V := by simp [factorX]
  have hxs : ∀ j : Fin (k + 1), factorX w j.succ = Letter.ofS (w j) := by
    intro j; simp [factorX]
  have hyc : ∀ j : Fin (k + 1), factorY w j.castSucc = Letter.ofT (w j) := by
    intro j; simp [factorY, j.isLt]
  have hyl : factorY w (Fin.last (k + 1)) = .V := by simp [factorY]
  simp only [hx0, hxs, hyc, hyl]
  have : ∀ j : Fin (k + 1), ((if Letter.ofS (w j) = .M then 1 else 0) +
      (if Letter.ofT (w j) = .M then 1 else 0) : ℕ) = 1 := by
    intro j; cases w j <;> simp [Letter.ofS, Letter.ofT]
  have h2 : (∑ j : Fin (k + 1), (if Letter.ofS (w j) = .M then 1 else 0) +
      ∑ j : Fin (k + 1), (if Letter.ofT (w j) = .M then 1 else 0) : ℕ) = k + 1 := by
    rw [← Finset.sum_add_distrib]; simp [this]
  simpa using h2

/-- Lemma 8.10 for one word: `deg A(w, σ) ≡ n(w) + |σ|_v (mod 2)` when no factor vanishes
identically. -/
theorem tagDeg_parity (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (h : tagNZ n w σ = true) :
    tagDeg n w σ % 2 = (n + tagV σ) % 2 := by
  cases n with
  | zero =>
    have h0 : ∀ s : Fin 3, (if s = 0 then 0 else if s = 1 then 2 else 1) % 2 =
        (0 + if s = 2 then 1 else 0) % 2 := by decide
    have := h0 (σ 0)
    simp only [tagDeg, tagV, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    simpa using this
  | succ k =>
    have hnz : ∀ l : Fin (k + 2), zeroTab (factorX w l) (factorY w l) (σ l) = false := by
      intro l
      simp only [tagNZ, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at h
      exact h l
    have hVV : ∀ l : Fin (k + 2), ¬(factorX w l = .V ∧ factorY w l = .V) := by
      intro l ⟨hx, hy⟩
      by_cases hl : (l : ℕ) = 0
      · have : (l : ℕ) < k + 1 := by omega
        simp [factorY, this] at hy
        cases hw : w ⟨l, this⟩ <;> simp [hw, Letter.ofT] at hy
      · simp [factorX, hl] at hx
        cases hw : w ⟨(l : ℕ) - 1, by omega⟩ <;> simp [hw, Letter.ofS] at hx
    have hev : (∑ l : Fin (k + 2), (degTab (factorX w l) (factorY w l) (σ l) +
        nMu (factorX w l) (factorY w l) + (if σ l = 2 then 1 else 0))) % 2 = 0 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_eq_zero]
      · rfl
      · intro l _
        exact degTab_parity _ _ _ (hVV l) (hnz l)
    simp only [Finset.sum_add_distrib, degreeCount_sum_nMu] at hev
    have hv : tagV σ = ∑ l : Fin (k + 2), (if σ l = 2 then 1 else 0) := rfl
    simp only [tagDeg]
    omega


/-- `d_X = ∑_r deg A(w_r, σ_r)` (def_d_X). -/
def dXof {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) :
    ℕ := ∑ r, tagDeg (ns r) (ws r) (σs r)

/-- `d_v = ∑_r |σ_r|_v` (def_d_star). -/
def dVof {p : ℕ} {ns : Fin p → ℕ} (σs : ∀ r, Fin (ns r + 1) → Fin 3) : ℕ := ∑ r, tagV (σs r)

/-- `d_μ = ∑_r |σ_r|_μ` (def_d_star). -/
def dMuof {p : ℕ} {ns : Fin p → ℕ} (σs : ∀ r, Fin (ns r + 1) → Fin 3) : ℕ := ∑ r, tagMu (σs r)

/-- Lemma 8.10 (`lem:d odd`): if `d_v = 0` then `d_X` is odd (`∑_r n(w_r) = 3`, no zero bracket). -/
theorem dX_odd {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (hn : ∑ r, ns r = 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (hv : dVof σs = 0) :
    Odd (dXof ns ws σs) := by
  rw [Nat.odd_iff]
  have h1 : dXof ns ws σs % 2 = (∑ r, (tagDeg (ns r) (ws r) (σs r) % 2)) % 2 :=
    Finset.sum_nat_mod _ _ _
  have h2 : ∀ r, tagDeg (ns r) (ws r) (σs r) % 2 = (ns r + tagV (σs r)) % 2 :=
    fun r => tagDeg_parity _ _ _ (hnz r)
  have h3 : (∑ r, (ns r + tagV (σs r))) % 2 = (∑ r, ((ns r + tagV (σs r)) % 2)) % 2 :=
    Finset.sum_nat_mod _ _ _
  rw [h1]
  simp only [h2]
  rw [← h3, Finset.sum_add_distrib, hn]
  have : ∑ r, tagV (σs r) = 0 := hv
  omega

/-- The finite core of (main_comb_est), Lemma 8.10 and (sigma_leq_d 2) for the nonempty words
(`d_X^<, d_v^<, d_μ^<, f_i` of `q` words): `q + [d_X ≥ 3][d_v = 0] ≤ d_X + f_i ∧ 2 + [d_v ≥ 2]`,
`d_v = 0 ⇒ d_X` odd, `d_μ ≤ d_X + 3`, `f_i ≤ 3`, and `f_i ≤ 2` if `q = 1`. -/
def combOK (q dX dV dMu f : ℕ) : Bool :=
  decide (q + (if 3 ≤ dX ∧ dV = 0 then 1 else 0) ≤ dX + min f 2 + (if 2 ≤ dV then 1 else 0)) &&
    (dV != 0 || dX % 2 == 1) && decide (dMu ≤ dX + 3) && decide (f ≤ 3) &&
    (q != 1 || decide (f ≤ 2))

/-- The finite core for `q = 1` (one word with `n = 3`). -/
theorem combOK_q1 : ∀ w : Word 3, ∀ σ : Fin 4 → Fin 3, tagNZ 3 w σ = true →
    combOK 1 (tagDeg 3 w σ) (tagV σ) (tagMu σ) (tagF 3 w σ) = true := by decide

/-- The finite core for `q = 2` (words with `n = 1, 2`). -/
theorem combOK_q2 : ∀ w₁ : Word 1, ∀ σ₁ : Fin 2 → Fin 3, ∀ w₂ : Word 2, ∀ σ₂ : Fin 3 → Fin 3,
    tagNZ 1 w₁ σ₁ = true → tagNZ 2 w₂ σ₂ = true →
    combOK 2 (tagDeg 1 w₁ σ₁ + tagDeg 2 w₂ σ₂) (tagV σ₁ + tagV σ₂) (tagMu σ₁ + tagMu σ₂)
      (tagF 1 w₁ σ₁ + tagF 2 w₂ σ₂) = true := by decide

/-- The finite core for `q = 3` (three words with `n = 1`). -/
theorem combOK_q3 : ∀ w₁ : Word 1, ∀ σ₁ : Fin 2 → Fin 3, ∀ w₂ : Word 1, ∀ σ₂ : Fin 2 → Fin 3,
    ∀ w₃ : Word 1, ∀ σ₃ : Fin 2 → Fin 3,
    tagNZ 1 w₁ σ₁ = true → tagNZ 1 w₂ σ₂ = true → tagNZ 1 w₃ σ₃ = true →
    combOK 3 (tagDeg 1 w₁ σ₁ + tagDeg 1 w₂ σ₂ + tagDeg 1 w₃ σ₃) (tagV σ₁ + tagV σ₂ + tagV σ₃)
      (tagMu σ₁ + tagMu σ₂ + tagMu σ₃) (tagF 1 w₁ σ₁ + tagF 1 w₂ σ₂ + tagF 1 w₃ σ₃) = true := by
  decide

section MainComb

private theorem degreeCount_empty (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (h : n = 0) :
    tagF n w σ = 0 ∧ tagDeg n w σ + tagV σ = 2 * tagMu σ ∧ tagV σ ≤ tagMu σ := by
  subst h
  refine ⟨rfl, ?_⟩
  simp only [tagDeg, tagV, tagMu, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero]
  generalize σ 0 = s
  fin_cases s <;> simp

private theorem degreeCount_spec {q dX dV dMu f : ℕ} (h : combOK q dX dV dMu f = true) :
    q + (if 3 ≤ dX ∧ dV = 0 then 1 else 0) ≤ dX + min f 2 + (if 2 ≤ dV then 1 else 0) ∧
      dMu ≤ dX + 3 := by
  simp only [combOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

private theorem degreeCount_comm {q a b c d e f g h : ℕ} :
    combOK q (a + b) (c + d) (e + f) (g + h) = combOK q (b + a) (d + c) (f + e) (h + g) := by
  rw [add_comm a b, add_comm c d, add_comm e f, add_comm g h]

private theorem degreeCount_aux1 (n : ℕ) (hn : n = 3) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (h : tagNZ n w σ = true) :
    combOK 1 (tagDeg n w σ) (tagV σ) (tagMu σ) (tagF n w σ) = true := by
  subst hn; exact combOK_q1 w σ h

private theorem degreeCount_aux2 (n₁ n₂ : ℕ) (h₁ : n₁ = 1) (h₂ : n₂ = 2) (w₁ : Word n₁)
    (σ₁ : Fin (n₁ + 1) → Fin 3) (w₂ : Word n₂) (σ₂ : Fin (n₂ + 1) → Fin 3)
    (hz₁ : tagNZ n₁ w₁ σ₁ = true) (hz₂ : tagNZ n₂ w₂ σ₂ = true) :
    combOK 2 (tagDeg n₁ w₁ σ₁ + tagDeg n₂ w₂ σ₂) (tagV σ₁ + tagV σ₂) (tagMu σ₁ + tagMu σ₂)
      (tagF n₁ w₁ σ₁ + tagF n₂ w₂ σ₂) = true := by
  subst h₁ h₂; exact combOK_q2 w₁ σ₁ w₂ σ₂ hz₁ hz₂

private theorem degreeCount_aux3 (n₁ n₂ n₃ : ℕ) (h₁ : n₁ = 1) (h₂ : n₂ = 1) (h₃ : n₃ = 1)
    (w₁ : Word n₁) (σ₁ : Fin (n₁ + 1) → Fin 3) (w₂ : Word n₂) (σ₂ : Fin (n₂ + 1) → Fin 3)
    (w₃ : Word n₃) (σ₃ : Fin (n₃ + 1) → Fin 3)
    (hz₁ : tagNZ n₁ w₁ σ₁ = true) (hz₂ : tagNZ n₂ w₂ σ₂ = true) (hz₃ : tagNZ n₃ w₃ σ₃ = true) :
    combOK 3 (tagDeg n₁ w₁ σ₁ + tagDeg n₂ w₂ σ₂ + tagDeg n₃ w₃ σ₃)
      (tagV σ₁ + tagV σ₂ + tagV σ₃) (tagMu σ₁ + tagMu σ₂ + tagMu σ₃)
      (tagF n₁ w₁ σ₁ + tagF n₂ w₂ σ₂ + tagF n₃ w₃ σ₃) = true := by
  subst h₁ h₂ h₃; exact combOK_q3 w₁ σ₁ w₂ σ₂ w₃ σ₃ hz₁ hz₂ hz₃

/-- The finite statement applies to the nonempty words of a tuple with `∑ n_r = 3`. -/
private theorem degreeCount_core {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true)
    (hR : ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ns r = 3) :
    combOK (Finset.univ.filter fun r => 1 ≤ ns r).card
      (∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), tagDeg (ns r) (ws r) (σs r))
      (∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), tagV (σs r))
      (∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), tagMu (σs r))
      (∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), tagF (ns r) (ws r) (σs r)) = true := by
  set R := Finset.univ.filter (fun r : Fin p => 1 ≤ ns r) with hRdef
  have hmem : ∀ r, r ∈ R ↔ 1 ≤ ns r := fun r => by simp [hRdef]
  have hle : R.card • 1 ≤ ∑ r ∈ R, ns r :=
    Finset.card_nsmul_le_sum R ns 1 (fun x hx => (hmem x).1 hx)
  rw [hR, smul_eq_mul, mul_one] at hle
  have hpos : R.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hR
    simp at hR
  have hcases : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    rw [hc, ha]
    rw [ha, Finset.sum_singleton] at hR
    simp only [Finset.sum_singleton]
    exact degreeCount_aux1 _ hR _ _ (hnz a)
  · obtain ⟨x, y, hxy, ha⟩ := Finset.card_eq_two.1 hc
    have hx : 1 ≤ ns x := (hmem x).1 (by rw [ha]; simp)
    have hy : 1 ≤ ns y := (hmem y).1 (by rw [ha]; simp)
    rw [hc, ha]
    rw [ha, Finset.sum_pair hxy] at hR
    simp only [Finset.sum_pair hxy]
    have h12 : (ns x = 1 ∧ ns y = 2) ∨ (ns x = 2 ∧ ns y = 1) := by omega
    rcases h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact degreeCount_aux2 _ _ h1 h2 _ _ _ _ (hnz x) (hnz y)
    · rw [degreeCount_comm]
      exact degreeCount_aux2 _ _ h2 h1 _ _ _ _ (hnz y) (hnz x)
  · obtain ⟨x, y, z, hxy, hxz, hyz, ha⟩ := Finset.card_eq_three.1 hc
    have key : ∀ f : Fin p → ℕ, ∑ r ∈ ({x, y, z} : Finset (Fin p)), f r = f x + f y + f z := by
      intro f
      rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz, add_assoc]
    have hx : 1 ≤ ns x := (hmem x).1 (by rw [ha]; simp)
    have hy : 1 ≤ ns y := (hmem y).1 (by rw [ha]; simp)
    have hz : 1 ≤ ns z := (hmem z).1 (by rw [ha]; simp)
    rw [hc, ha]
    rw [ha, key] at hR
    simp only [key]
    exact degreeCount_aux3 _ _ _ (by omega) (by omega) (by omega) _ _ _ _ _ _
      (hnz x) (hnz y) (hnz z)

end MainComb

/-- (main_comb_est): `q + ∑_{r > q} |σ_r|_μ ≤ d_X − [d_X ≥ 3][d_v = 0] + [d_v ≥ 2] + f_i ∧ 2`,
and (sigma_leq_d 2) in the sharp form `d_μ ≤ d_X + 3`. -/
theorem main_comb_est {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (hn : ∑ r, ns r = 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) :
    (Finset.univ.filter fun r => 1 ≤ ns r).card +
        (∑ r ∈ Finset.univ.filter (fun r => ns r = 0), tagMu (σs r)) +
        (if 3 ≤ dXof ns ws σs ∧ dVof σs = 0 then 1 else 0) ≤
      dXof ns ws σs + (if 2 ≤ dVof σs then 1 else 0) +
        min (∑ r, tagF (ns r) (ws r) (σs r)) 2 ∧
    dMuof σs ≤ dXof ns ws σs + 3 := by
  have hE : Finset.univ.filter (fun r : Fin p => ¬ 1 ≤ ns r) =
      Finset.univ.filter (fun r : Fin p => ns r = 0) := by
    ext r; simp
  have hsplit : ∀ f : Fin p → ℕ, ∑ r, f r =
      ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), f r +
        ∑ r ∈ Finset.univ.filter (fun r => ns r = 0), f r := fun f => by
    rw [← hE]; exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => 1 ≤ ns r) f).symm
  have hemp : ∀ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0),
      tagF (ns r) (ws r) (σs r) = 0 ∧
        tagDeg (ns r) (ws r) (σs r) + tagV (σs r) = 2 * tagMu (σs r) ∧
        tagV (σs r) ≤ tagMu (σs r) := fun r hr =>
    degreeCount_empty _ _ _ (by simpa using hr)
  have hEn : ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), ns r = 0 :=
    Finset.sum_eq_zero fun r hr => by simpa using hr
  have hEf : ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagF (ns r) (ws r) (σs r) = 0 :=
    Finset.sum_eq_zero fun r hr => (hemp r hr).1
  have hEa : ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagDeg (ns r) (ws r) (σs r) +
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagV (σs r) =
      2 * ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagMu (σs r) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr => (hemp r hr).2.1
  have hEb : ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagV (σs r) ≤
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => ns r = 0), tagMu (σs r) :=
    Finset.sum_le_sum fun r hr => (hemp r hr).2.2
  have hR : ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ns r = 3 := by
    have := hsplit ns
    omega
  have hcore := degreeCount_spec (degreeCount_core ns ws σs hnz hR)
  have hX : dXof ns ws σs = _ := hsplit (fun r => tagDeg (ns r) (ws r) (σs r))
  have hV : dVof σs = _ := hsplit (fun r => tagV (σs r))
  have hM : dMuof σs = _ := hsplit (fun r => tagMu (σs r))
  have hF := hsplit (fun r => tagF (ns r) (ws r) (σs r))
  obtain ⟨hc1, hc2⟩ := hcore
  refine ⟨?_, by omega⟩
  split_ifs at hc1 ⊢ <;> omega

/-- The tight configuration of (main_comb_est): `w = 𝛍𝐢𝐢𝛍𝛍𝐢`, `σ = (2, 0, 1, 0)`:
`d_X = 0`, `d_v = 1`, `f_i = 1`, `q = 1`. -/
example : tagNZ 3 ![false, true, false] ![2, 0, 1, 0] = true ∧
    tagDeg 3 ![false, true, false] ![2, 0, 1, 0] = 0 ∧ tagV (n := 3) ![2, 0, 1, 0] = 1 ∧
    tagF 3 ![false, true, false] ![2, 0, 1, 0] = 1 ∧ tagMu (n := 3) ![2, 0, 1, 0] = 2 := by
  decide

/-- `tagDeg_parity` at the tight configuration. -/
example : tagDeg 3 ![false, true, false] ![2, 0, 1, 0] % 2 =
    (3 + tagV (n := 3) ![2, 0, 1, 0]) % 2 :=
  tagDeg_parity 3 _ _ (by decide)

/-- `main_comb_est` at `p = 1`, `ns = ![3]` and the tight configuration, with the values of the
counts: `q = 1`, `d_X = 0`, `d_v = 1`, `f_i = 1`, `d_μ = 2`. -/
example :
    let ws : ∀ r : Fin 1, Word (![3] r) :=
      fun _ j => ([false, true, false] : List Bool).getD j false
    let σs : ∀ r : Fin 1, Fin (![3] r + 1) → Fin 3 :=
      fun _ j => ([2, 0, 1, 0] : List (Fin 3)).getD j 0
    dXof ![3] ws σs = 0 ∧ dVof σs = 1 ∧ dMuof σs = 2 ∧
      (∑ r, tagF (![3] r) (ws r) (σs r)) = 1 ∧
    (Finset.univ.filter fun r : Fin 1 => 1 ≤ ![3] r).card = 1 ∧
      (Finset.univ.filter fun r : Fin 1 => 1 ≤ ![3] r).card +
          (∑ r ∈ Finset.univ.filter (fun r : Fin 1 => ![3] r = 0), tagMu (σs r)) +
          (if 3 ≤ dXof ![3] ws σs ∧ dVof σs = 0 then 1 else 0) ≤
        dXof ![3] ws σs + (if 2 ≤ dVof σs then 1 else 0) +
          min (∑ r, tagF (![3] r) (ws r) (σs r)) 2 ∧
      dMuof σs ≤ dXof ![3] ws σs + 3 := by
  intro ws σs
  have h := main_comb_est (p := 1) ![3] ws σs (by decide) (Fin.forall_fin_one.2 (by decide))
  refine ⟨by decide, by decide, by decide, by decide, by decide, h⟩

/-- `main_comb_est` with two empty words appended (`σ = 1, 2`): `d_X = 3`, `d_v = 2`,
`d_μ = 4`. -/
example :
    let ns : Fin 3 → ℕ := ![3, 0, 0]
    let ws : ∀ r : Fin 3, Word (ns r) := fun r j => (![[false, true, false], [], []] r).getD j false
    let σs : ∀ r : Fin 3, Fin (ns r + 1) → Fin 3 :=
      fun r j => (![[2, 0, 1, 0], [1], [2]] r).getD j 0
    dXof ns ws σs = 3 ∧ dVof σs = 2 ∧ dMuof σs = 4 ∧
      (Finset.univ.filter fun r : Fin 3 => 1 ≤ ns r).card +
          (∑ r ∈ Finset.univ.filter (fun r : Fin 3 => ns r = 0), tagMu (σs r)) +
          (if 3 ≤ dXof ns ws σs ∧ dVof σs = 0 then 1 else 0) ≤
        dXof ns ws σs + (if 2 ≤ dVof σs then 1 else 0) +
          min (∑ r, tagF (ns r) (ws r) (σs r)) 2 ∧
      dMuof σs ≤ dXof ns ws σs + 3 := by
  intro ns ws σs
  have h := main_comb_est ns ws σs (by decide) (fun r => by fin_cases r <;> decide)
  exact ⟨by decide, by decide, by decide, h⟩

/-- `dX_odd` at `p = 1`, `ns = ![3]`, `w = 𝛍𝐢𝐢𝛍𝛍𝐢` and `σ = (1, 1, 1, 1)` (`d_v = 0`,
`d_X = 5`). -/
example :
    let ws : ∀ r : Fin 1, Word (![3] r) :=
      fun _ j => ([false, true, false] : List Bool).getD j false
    let σs : ∀ r : Fin 1, Fin (![3] r + 1) → Fin 3 :=
      fun _ j => ([1, 1, 1, 1] : List (Fin 3)).getD j 0
    dVof σs = 0 ∧ dXof ![3] ws σs = 5 ∧ Odd (dXof ![3] ws σs) := by
  intro ws σs
  have hv : dVof σs = 0 := by decide
  exact ⟨hv, by decide, dX_odd ![3] ws σs (by decide) (Fin.forall_fin_one.2 (by decide)) hv⟩

/-- `combOK_q1` at the tight configuration. -/
example : combOK 1 (tagDeg 3 ![false, true, false] ![2, 0, 1, 0]) (tagV (n := 3) ![2, 0, 1, 0])
    (tagMu (n := 3) ![2, 0, 1, 0]) (tagF 3 ![false, true, false] ![2, 0, 1, 0]) = true :=
  combOK_q1 _ _ (by decide)

/-- `combOK_q2` at `n = 1, 2`. -/
example : combOK 2 (tagDeg 1 ![true] ![1, 1] + tagDeg 2 ![true, false] ![1, 1, 1])
    (tagV (n := 1) ![1, 1] + tagV (n := 2) ![1, 1, 1])
    (tagMu (n := 1) ![1, 1] + tagMu (n := 2) ![1, 1, 1])
    (tagF 1 ![true] ![1, 1] + tagF 2 ![true, false] ![1, 1, 1]) = true :=
  combOK_q2 _ _ _ _ (by decide) (by decide)

/-- `combOK_q3` at three words with `n = 1`. -/
example : combOK 3 (tagDeg 1 ![true] ![1, 1] + tagDeg 1 ![false] ![1, 1] + tagDeg 1 ![true] ![1, 1])
    (tagV (n := 1) ![1, 1] + tagV (n := 1) ![1, 1] + tagV (n := 1) ![1, 1])
    (tagMu (n := 1) ![1, 1] + tagMu (n := 1) ![1, 1] + tagMu (n := 1) ![1, 1])
    (tagF 1 ![true] ![1, 1] + tagF 1 ![false] ![1, 1] + tagF 1 ![true] ![1, 1]) = true :=
  combOK_q3 _ _ _ _ _ _ (by decide) (by decide) (by decide)

end Anisotropic
