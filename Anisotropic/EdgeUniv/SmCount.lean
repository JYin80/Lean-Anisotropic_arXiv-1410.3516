module

public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The smoothed counting function, the edge regime, and the deterministic bracket -/

/-- `𝒳 = ∑_α (1_{[E₁,E₂]} * θ_η)(λ_α)`, `θ_η(x) = η/(π(x² + η²))`
(equal to `(N/π) ∫_{E₁}^{E₂} Im m_N(y + iη) dy` for `Q_N`). -/
def smCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (η E₁ E₂ : ℝ) : ℝ :=
  ∑ j, (Real.arctan ((E₂ - specOf A j) / η) - Real.arctan ((E₁ - specOf A j) / η)) / Real.pi

/-- The smoothing scale `η = N^{-2/3-9ε}`. -/
def etaE (N : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (-2 / 3 - 9 * ε)

/-- The shift `ℓ = N^{-2/3-ε}`. -/
def ellE (N : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (-2 / 3 - ε)

/-- The upper end `E_L = a + 2 N^{-2/3+ε}` of the counting windows. -/
def edgeEL (N : ℕ) (a ε : ℝ) : ℝ := a + 2 * (N : ℝ) ^ (-2 / 3 + ε)

/-- The local regime at an upper edge `a` with `d` eigenvalues beyond it, at exponent `δ`:
exactly `d` eigenvalues `≥ a + N^{-2/3+δ}` and none in `[a + N^{-2/3+δ}, a + r₀)`; at least
`d + l` eigenvalues `≥ a - N^{-2/3+δ}`; at most `N^δ + C₀ N t^{3/2}` eigenvalues in
`[a - t, a + r₀)` for `t ≤ r₀`. -/
def EdgeRegime (N : ℕ) (a : ℝ) (d l : ℕ) (δ r₀ C₀ : ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  eigCount A (a + (N : ℝ) ^ (-2 / 3 + δ)) = d ∧ eigCount A (a + r₀) = d ∧
    d + l ≤ eigCount A (a - (N : ℝ) ^ (-2 / 3 + δ)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) r₀,
      (eigCount A (a - t) : ℝ) - d ≤ (N : ℝ) ^ δ + C₀ * N * t ^ (3 / 2 : ℝ)

open Polynomial in
private lemma charpoly_neg_eq_diagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (-A).charpoly = (diagonal (fun j => -hA.eigenvalues j)).charpoly := by
  have hs := hA.spectral_theorem
  have h1 : -A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun j => -hA.eigenvalues j) *
        star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply]
    simp [← diagonal_neg]
  rw [h1, charpoly_mul_comm, ← mul_assoc]
  simp


private lemma specOf_neg_perm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ e : Equiv.Perm (Fin n), specOf (-A) = fun j => -specOf A (e j) := by
  have hA' : (-A).IsHermitian := hA.neg
  have hD : (diagonal (fun j => -hA.eigenvalues j)).IsHermitian := isHermitian_diagonal _
  have h1 : hA'.eigenvalues = hD.eigenvalues :=
    (hA'.eigenvalues_eq_eigenvalues_iff hD).2 (charpoly_neg_eq_diagonal hA)
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal (fun j => -hA.eigenvalues j)
  refine ⟨e, ?_⟩
  rw [specOf_eq hA', h1, ← specOf_eq hD, he, specOf_eq hA]
  rfl

/-- The mirror identity `𝒳_{[E₁,E₂]}(-A) = 𝒳_{[-E₂,-E₁]}(A)`. -/
theorem smCount_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (η E₁ E₂ : ℝ) :
    smCount (-A) η E₁ E₂ = smCount A η (-E₂) (-E₁) := by
  obtain ⟨e, he⟩ := specOf_neg_perm hA
  unfold smCount
  rw [← Equiv.sum_comp e (fun j => (Real.arctan ((-E₁ - specOf A j) / η) -
    Real.arctan ((-E₂ - specOf A j) / η)) / Real.pi)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he]
  have h1 : (E₂ - -specOf A (e j)) / η = -((-E₂ - specOf A (e j)) / η) := by ring
  have h2 : (E₁ - -specOf A (e j)) / η = -((-E₁ - specOf A (e j)) / η) := by ring
  rw [h1, h2, Real.arctan_neg, Real.arctan_neg]
  ring


private lemma arctan_le_self' {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have h0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.2 ht
  have := Real.le_tan h0 (Real.arctan_lt_pi_div_two t)
  rwa [Real.tan_arctan] at this

private lemma pi_div_two_sub_arctan_le {x : ℝ} (hx : 0 < x) :
    Real.pi / 2 - Real.arctan x ≤ x⁻¹ := by
  rw [← Real.arctan_inv_of_pos hx]
  exact arctan_le_self' (inv_nonneg.2 hx.le)

private lemma arctan_sub_le {s W η : ℝ} (hη : 0 < η) (hs : 0 < s) (hW : 0 ≤ W) :
    Real.arctan ((s + W) / η) - Real.arctan (s / η) ≤ W * η / s ^ 2 := by
  have h1 : s / η * ((s + W) / η) > 0 := by positivity
  have key : Real.arctan ((s + W) / η) + Real.arctan (-(s / η)) =
      Real.arctan (((s + W) / η + -(s / η)) / (1 - (s + W) / η * (-(s / η)))) := by
    apply Real.arctan_add
    nlinarith
  rw [Real.arctan_neg] at key
  have e : ((s + W) / η + -(s / η)) / (1 - (s + W) / η * (-(s / η))) =
      W * η / (η ^ 2 + s * (s + W)) := by
    have hd : 0 < η ^ 2 + s * (s + W) := by positivity
    have e1 : 1 - (s + W) / η * (-(s / η)) = (η ^ 2 + s * (s + W)) / η ^ 2 := by
      field_simp
      ring
    have e2 : (s + W) / η + -(s / η) = W / η := by ring
    rw [e1, e2]
    field_simp
  rw [← sub_eq_add_neg, e] at key
  rw [key]
  refine (arctan_le_self' (by positivity)).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg η]

/-- One summand of `smCount`. -/
private def smTerm (η E₁ E₂ x : ℝ) : ℝ :=
  (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi

private lemma smCount_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (η E₁ E₂ : ℝ) :
    smCount A η E₁ E₂ = ∑ j, smTerm η E₁ E₂ (specOf A j) := rfl

private lemma smTerm_nonneg {η E₁ E₂ x : ℝ} (hη : 0 < η) (h : E₁ ≤ E₂) :
    0 ≤ smTerm η E₁ E₂ x := by
  unfold smTerm
  apply div_nonneg _ Real.pi_pos.le
  have : (E₁ - x) / η ≤ (E₂ - x) / η := by gcongr
  linarith [Real.arctan_mono this]

private lemma smTerm_le_one (η E₁ E₂ x : ℝ) : smTerm η E₁ E₂ x ≤ 1 := by
  unfold smTerm
  rw [div_le_one Real.pi_pos]
  linarith [Real.arctan_lt_pi_div_two ((E₂ - x) / η), Real.neg_pi_div_two_lt_arctan ((E₁ - x) / η)]

private lemma smTerm_ge {η E₁ E₂ x : ℝ} (hη : 0 < η) (hp : 0 < E₂ - x) (hq : 0 < x - E₁) :
    1 - η / (Real.pi * (E₂ - x)) - η / (Real.pi * (x - E₁)) ≤ smTerm η E₁ E₂ x := by
  unfold smTerm
  have h1 := pi_div_two_sub_arctan_le (x := (E₂ - x) / η) (by positivity)
  have h2 := pi_div_two_sub_arctan_le (x := (x - E₁) / η) (by positivity)
  have e : Real.arctan ((E₁ - x) / η) = - Real.arctan ((x - E₁) / η) := by
    rw [← Real.arctan_neg]; congr 1; ring
  rw [e]
  have i1 : ((E₂ - x) / η)⁻¹ = η / (E₂ - x) := by rw [inv_div]
  have i2 : ((x - E₁) / η)⁻¹ = η / (x - E₁) := by rw [inv_div]
  rw [i1] at h1
  rw [i2] at h2
  have e1 : η / (Real.pi * (E₂ - x)) = (η / (E₂ - x)) / Real.pi := by
    rw [div_div, mul_comm]
  have e2 : η / (Real.pi * (x - E₁)) = (η / (x - E₁)) / Real.pi := by
    rw [div_div, mul_comm]
  rw [e1, e2, le_div_iff₀ Real.pi_pos]
  have : (1 - η / (E₂ - x) / Real.pi - η / (x - E₁) / Real.pi) * Real.pi =
      Real.pi - η / (E₂ - x) - η / (x - E₁) := by
    field_simp
  rw [this]
  linarith

private lemma smTerm_le_below {η E₁ E₂ x : ℝ} (hη : 0 < η) (hx : x < E₁) (h : E₁ ≤ E₂) :
    smTerm η E₁ E₂ x ≤ η / (Real.pi * (E₁ - x)) ∧
      smTerm η E₁ E₂ x ≤ (E₂ - E₁) * η / (Real.pi * (E₁ - x) ^ 2) := by
  have hs : 0 < E₁ - x := by linarith
  have hW : 0 ≤ E₂ - E₁ := by linarith
  have e : (E₂ - x) / η = ((E₁ - x) + (E₂ - E₁)) / η := by ring
  have hsη : 0 < (E₁ - x) / η := by positivity
  constructor
  · unfold smTerm
    rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
    have h1 := pi_div_two_sub_arctan_le hsη
    have h2 := Real.arctan_lt_pi_div_two ((E₂ - x) / η)
    rw [inv_div] at h1
    have : (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) * (Real.pi * (E₁ - x))
        ≤ η * Real.pi := by
      have h3 : Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η) ≤ η / (E₁ - x) := by
        linarith
      calc _ ≤ η / (E₁ - x) * (Real.pi * (E₁ - x)) := by gcongr
        _ = η * Real.pi := by field_simp
    linarith
  · unfold smTerm
    have := arctan_sub_le (s := E₁ - x) (W := E₂ - E₁) hη hs hW
    rw [← e] at this
    rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
    have h4 : (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) * (Real.pi * (E₁ - x) ^ 2)
        ≤ (E₂ - E₁) * η / (E₁ - x) ^ 2 * (Real.pi * (E₁ - x) ^ 2) := by gcongr
    have h5 : (E₂ - E₁) * η / (E₁ - x) ^ 2 * (Real.pi * (E₁ - x) ^ 2) =
        (E₂ - E₁) * η * Real.pi := by
      field_simp
    linarith

private lemma smTerm_le_above {η E₁ E₂ x : ℝ} (hη : 0 < η) (h : E₁ ≤ E₂) (hx : E₂ < x) :
    smTerm η E₁ E₂ x ≤ (E₂ - E₁) * η / (Real.pi * (x - E₂) ^ 2) := by
  have hs : 0 < x - E₂ := by linarith
  have hW : 0 ≤ E₂ - E₁ := by linarith
  have := arctan_sub_le (s := x - E₂) (W := E₂ - E₁) hη hs hW
  unfold smTerm
  have e1 : Real.arctan ((E₂ - x) / η) = - Real.arctan ((x - E₂) / η) := by
    rw [← Real.arctan_neg]; congr 1; ring
  have e2 : Real.arctan ((E₁ - x) / η) = - Real.arctan (((x - E₂) + (E₂ - E₁)) / η) := by
    rw [← Real.arctan_neg]; congr 1; ring
  rw [e1, e2, div_le_div_iff₀ Real.pi_pos (by positivity)]
  have h4 : (Real.arctan (((x - E₂) + (E₂ - E₁)) / η) - Real.arctan ((x - E₂) / η)) *
      (Real.pi * (x - E₂) ^ 2) ≤ (E₂ - E₁) * η / (x - E₂) ^ 2 * (Real.pi * (x - E₂) ^ 2) := by
    gcongr
  have h5 : (E₂ - E₁) * η / (x - E₂) ^ 2 * (Real.pi * (x - E₂) ^ 2) = (E₂ - E₁) * η * Real.pi := by
    field_simp
  linarith


/-- The indices of the eigenvalues in `[E, F)`. -/
private def eigWin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E F : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => E ≤ specOf A j ∧ specOf A j < F

private lemma eigCount_eq_add_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {E F : ℝ} (hEF : E ≤ F) :
    eigCount A E = eigCount A F + (eigWin A E F).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun j => E ≤ specOf A j)
    (fun j => F ≤ specOf A j)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (Finset.univ.filter fun j => E ≤ specOf A j ∧ F ≤ specOf A j) =
      Finset.univ.filter fun j => F ≤ specOf A j := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hj => hj.2, fun hj => ⟨hEF.trans hj, hj⟩⟩
  have e2 : (Finset.univ.filter fun j => E ≤ specOf A j ∧ ¬ F ≤ specOf A j) = eigWin A E F := by
    ext j
    simp only [eigWin, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [e1, e2] at h
  unfold eigCount
  omega

private lemma bracket_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {η ℓ L r₀ C₀ Dδ Nr a E : ℝ} {d : ℕ}
    (hη : 0 < η) (hℓ : 0 < ℓ) (hL : 0 < L) (hLr : L ≤ r₀)
    (hC₀ : 0 ≤ C₀) (hNr : 0 ≤ Nr)
    (hgap : ∀ j, a + L ≤ specOf A j → a + r₀ ≤ specOf A j)
    (hd : eigCount A (a + r₀) = d) (hE : |E - a| ≤ L / 2)
    (hcnt : ∀ t ∈ Set.Icc (0 : ℝ) r₀,
      (eigCount A (a - t) : ℝ) - d ≤ Dδ + C₀ * Nr * t ^ (3 / 2 : ℝ)) :
    (eigCount A E : ℝ) - d ≤ smCount A η (E - ℓ) (a + 2 * L) +
      (η / ℓ + η / L) * (Dδ + C₀ * Nr * L ^ (3 / 2 : ℝ)) := by
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hrE : E ≤ a + r₀ := by linarith
  have hK : (eigCount A E : ℝ) - d = (eigWin A E (a + r₀)).card := by
    have := eigCount_eq_add_card A hrE
    rw [hd] at this
    rw [this]; push_cast; ring
  have hKb : ((eigWin A E (a + r₀)).card : ℝ) ≤ Dδ + C₀ * Nr * L ^ (3 / 2 : ℝ) := by
    have h1 : eigCount A E ≤ eigCount A (a - L / 2) := eigCount_antitone A (by linarith)
    have h2 := hcnt (L / 2) ⟨by positivity, by linarith⟩
    have h3 : (L / 2) ^ (3 / 2 : ℝ) ≤ L ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [← hK]
    have h4 : (eigCount A E : ℝ) ≤ eigCount A (a - L / 2) := by exact_mod_cast h1
    have h5 : C₀ * Nr * (L / 2) ^ (3 / 2 : ℝ) ≤ C₀ * Nr * L ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hC₀ hNr)
    linarith
  have hterm : ∀ j ∈ eigWin A E (a + r₀),
      1 - (η / ℓ + η / L) ≤ smTerm η (E - ℓ) (a + 2 * L) (specOf A j) := by
    intro j hj
    simp only [eigWin, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h1, h2⟩ := hj
    have h3 : specOf A j < a + L := by
      by_contra h
      exact absurd (hgap j (not_lt.1 h)) (not_le.2 h2)
    have := smTerm_ge (η := η) (E₁ := E - ℓ) (E₂ := a + 2 * L) (x := specOf A j) hη
      (by linarith) (by linarith)
    have a1 : η / (Real.pi * (a + 2 * L - specOf A j)) ≤ η / L :=
      div_le_div_of_nonneg_left hη.le hL (by nlinarith [Real.pi_gt_three])
    have a2 : η / (Real.pi * (specOf A j - (E - ℓ))) ≤ η / ℓ :=
      div_le_div_of_nonneg_left hη.le hℓ (by nlinarith [Real.pi_gt_three])
    linarith
  have hsum : ((eigWin A E (a + r₀)).card : ℝ) * (1 - (η / ℓ + η / L)) ≤
      smCount A η (E - ℓ) (a + 2 * L) := by
    rw [smCount_eq_sum]
    calc ((eigWin A E (a + r₀)).card : ℝ) * (1 - (η / ℓ + η / L))
        = ∑ j ∈ eigWin A E (a + r₀), (1 - (η / ℓ + η / L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ eigWin A E (a + r₀), smTerm η (E - ℓ) (a + 2 * L) (specOf A j) :=
        Finset.sum_le_sum hterm
      _ ≤ ∑ j, smTerm η (E - ℓ) (a + 2 * L) (specOf A j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => smTerm_nonneg hη (by linarith))
  have hpos : 0 ≤ η / ℓ + η / L := by positivity
  have hk0 : (0 : ℝ) ≤ (eigWin A E (a + r₀)).card := Nat.cast_nonneg _
  rw [hK]
  have := mul_le_mul_of_nonneg_left hKb hpos
  nlinarith

private lemma dyadic_ind {L u : ℝ} (hL : 0 < L) (hu : L ≤ u) :
    ∀ K : ℕ, u < 4 ^ (K + 1) * L →
      (L / u) ^ 2 ≤ ∑ k ∈ Finset.range (K + 1),
        (1 / 16 : ℝ) ^ k * (if u < 4 ^ (k + 1) * L then 1 else 0) := by
  have hu0 : 0 < u := hL.trans_le hu
  intro K
  induction K with
  | zero =>
    intro h
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
    have h1 : u < 4 ^ 1 * L := by simpa only [zero_add] using h
    simp only [h1, ↓reduceIte]
    have : L / u ≤ 1 := (div_le_one hu0).2 hu
    have h0 : 0 ≤ L / u := by positivity
    nlinarith
  | succ K ih =>
    intro h
    rw [Finset.sum_range_succ]
    by_cases hlt : u < 4 ^ (K + 1) * L
    · have := ih hlt
      have : 0 ≤ (1 / 16 : ℝ) ^ (K + 1) * (if u < 4 ^ (K + 1 + 1) * L then 1 else 0) := by
        positivity
      linarith
    · have hlt := not_lt.1 hlt
      simp only [h, ↓reduceIte]
      have hs : 0 ≤ ∑ k ∈ Finset.range (K + 1),
          (1 / 16 : ℝ) ^ k * (if u < 4 ^ (k + 1) * L then 1 else 0) :=
        Finset.sum_nonneg fun k _ => by positivity
      have h4 : (0 : ℝ) < 4 ^ (K + 1) := by positivity
      have hLu : L / u ≤ 1 / 4 ^ (K + 1) := by
        rw [div_le_div_iff₀ hu0 h4]
        nlinarith
      have h0 : 0 ≤ L / u := by positivity
      have : (L / u) ^ 2 ≤ (1 / 4 ^ (K + 1)) ^ 2 := by gcongr
      have e : (1 / 4 ^ (K + 1) : ℝ) ^ 2 = (1 / 16) ^ (K + 1) := by
        rw [div_pow, one_pow, ← pow_mul, mul_comm, pow_mul]
        simp [one_div, inv_pow]
        norm_num
      rw [e] at this
      linarith

private lemma four_pow_rpow (m : ℕ) : ((4 : ℝ) ^ m) ^ (3 / 2 : ℝ) = 8 ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h : (4 : ℝ) ^ ((m : ℝ) * (3 / 2)) = ((4 : ℝ) ^ (3 / 2 : ℝ)) ^ (m : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num)]
  rw [h, Real.rpow_natCast]
  congr 1
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma two_rpow_le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
  have h : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hp : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  nlinarith

/-- `(r + L/2)^{3/2} ≤ 3 r^{3/2}` for `r ≥ L`. -/
private lemma half_add_rpow_le {r L : ℝ} (hL : 0 < L) (hr : L ≤ r) :
    (r + L / 2) ^ (3 / 2 : ℝ) ≤ 3 * r ^ (3 / 2 : ℝ) := by
  have hr0 : 0 < r := hL.trans_le hr
  have h1 : (r + L / 2) ^ (3 / 2 : ℝ) ≤ (2 * r) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) hr0.le] at h1
  have := two_rpow_le
  have hp : 0 ≤ r ^ (3 / 2 : ℝ) := by positivity
  nlinarith


private lemma win_card_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {L r₀ C₀ Dδ Nr a E r : ℝ} {d : ℕ}
    (hd : eigCount A (a + r₀) = d) (hE : |E - a| ≤ L / 2) (hL : 0 < L) (hLr : L ≤ r₀)
    (hcnt : ∀ t ∈ Set.Icc (0 : ℝ) r₀,
      (eigCount A (a - t) : ℝ) - d ≤ Dδ + C₀ * Nr * t ^ (3 / 2 : ℝ))
    (hr : 0 ≤ r) (hrr : r + L / 2 ≤ r₀) :
    ((eigWin A (E - r) E).card : ℝ) ≤ Dδ + C₀ * Nr * (r + L / 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hrE : E ≤ a + r₀ := by linarith
  have h1 := eigCount_eq_add_card A (show E - r ≤ E by linarith)
  have h2 : eigCount A (a + r₀) ≤ eigCount A E := eigCount_antitone A hrE
  have h3 : eigCount A (E - r) ≤ eigCount A (a - (r + L / 2)) :=
    eigCount_antitone A (by linarith)
  have h4 := hcnt (r + L / 2) ⟨by positivity, hrr⟩
  have h5 : (eigCount A (E - r) : ℝ) ≤ eigCount A (a - (r + L / 2)) := by exact_mod_cast h3
  have h6 : (eigCount A (E - r) : ℝ) = eigCount A E + (eigWin A (E - r) E).card := by
    exact_mod_cast h1
  have h7 : (d : ℝ) ≤ eigCount A E := by rw [← hd]; exact_mod_cast h2
  linarith

private lemma far_bound {η L r₀ s W : ℝ} (hη : 0 < η) (hL : 0 < L) (hr₀ : 0 < r₀)
    (hs : r₀ / 8 ≤ s) (hW0 : 0 ≤ W) (hW : W ≤ 3 * L) :
    W * η / (Real.pi * s ^ 2) ≤ 64 * L * η / r₀ ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : r₀ ^ 2 ≤ 64 * s ^ 2 := by nlinarith
  have h2 : W * η * r₀ ^ 2 ≤ W * η * (64 * s ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hWπ : W ≤ Real.pi * L := by nlinarith [Real.pi_gt_three]
  have h3 : W * η * (64 * s ^ 2) ≤ Real.pi * L * η * (64 * s ^ 2) := by gcongr
  nlinarith

/-- The indicator of `E - r ≤ λ_j < E`. -/
private def winInd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E r : ℝ) (j : Fin n) : ℝ :=
  if E - r ≤ specOf A j ∧ specOf A j < E then 1 else 0

private lemma winInd_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E r : ℝ) (j : Fin n) :
    0 ≤ winInd A E r j := by
  unfold winInd; split_ifs <;> norm_num

private lemma winInd_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E r : ℝ) :
    ∑ j, winInd A E r j = ((eigWin A (E - r) E).card : ℝ) := by
  simp only [winInd, eigWin, Finset.sum_boole]

private lemma winInd_eq_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {E r : ℝ} {j : Fin n}
    (h1 : E - r ≤ specOf A j) (h2 : specOf A j < E) : winInd A E r j = 1 := by
  unfold winInd; simp only [h1, h2, and_self, ↓reduceIte]

private lemma dyadic_scale {L r₀ : ℝ} (hL : 0 < L) (hLr : 8 * L ≤ r₀) :
    ∃ K : ℕ, 4 ^ (K + 1) * L ≤ r₀ / 2 ∧ r₀ / 8 < 4 ^ (K + 1) * L := by
  have hx4 : 4 ≤ r₀ / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ r₀ / (2 * L))
    (by norm_num : (1 : ℝ) < 4)
  obtain ⟨K, rfl⟩ : ∃ K, m = K + 1 := by
    rcases m with _ | K
    · exfalso
      simp only [zero_add, pow_one] at hm2
      linarith
    · exact ⟨K, rfl⟩
  refine ⟨K, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hm1
    linarith
  · rw [div_lt_iff₀ (by positivity), pow_succ] at hm2
    nlinarith

private lemma lower_pt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {η ℓ L r₀ a E : ℝ} (K : ℕ)
    (hη : 0 < η) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) (hL : 0 < L) (hLr : 8 * L ≤ r₀)
    (hE : |E - a| ≤ L / 2) (hR2 : r₀ / 8 < 4 ^ (K + 1) * L) (j : Fin n)
    (hj : specOf A j < E ∨ a + r₀ ≤ specOf A j) :
    smTerm η (E + ℓ) (a + 2 * L) (specOf A j) ≤
      (η / ℓ) * winInd A E L j + (η / L) * ∑ k ∈ Finset.range (K + 1),
        (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j + 64 * L * η / r₀ ^ 2 := by
  have hr₀ : 0 < r₀ := by linarith
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hE12 : E + ℓ ≤ a + 2 * L := by linarith
  have hW0 : 0 ≤ (a + 2 * L) - (E + ℓ) := by linarith
  have hW3 : (a + 2 * L) - (E + ℓ) ≤ 3 * L := by linarith
  have h0 := winInd_nonneg A E L j
  have hS : 0 ≤ ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (winInd_nonneg _ _ _ _)
  have hLS : 0 ≤ (η / L) * ∑ k ∈ Finset.range (K + 1),
      (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j := mul_nonneg (by positivity) hS
  have hℓη : 0 ≤ (η / ℓ) * winInd A E L j := mul_nonneg (by positivity) h0
  rcases hj with hlt | hge
  · have hx : specOf A j < E + ℓ := by linarith
    obtain ⟨b1, b2⟩ := smTerm_le_below hη hx hE12
    by_cases hu : E + ℓ - specOf A j < L
    · have h1 : smTerm η (E + ℓ) (a + 2 * L) (specOf A j) ≤ η / ℓ :=
        b1.trans (div_le_div_of_nonneg_left hη.le hℓ (by nlinarith [Real.pi_gt_three]))
      have hi : winInd A E L j = 1 := winInd_eq_one A (by linarith) hlt
      rw [hi] at hℓη ⊢
      have : 0 ≤ 64 * L * η / r₀ ^ 2 := by positivity
      linarith
    · have hu' : L ≤ E + ℓ - specOf A j := not_lt.1 hu
      by_cases hu2 : E + ℓ - specOf A j < 4 ^ (K + 1) * L
      · have hdy := dyadic_ind hL hu' K hu2
        have hle : ∑ k ∈ Finset.range (K + 1),
            (1 / 16 : ℝ) ^ k * (if E + ℓ - specOf A j < 4 ^ (k + 1) * L then 1 else 0) ≤
            ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          split_ifs with hk
          · exact (winInd_eq_one A (by linarith) hlt).ge
          · exact winInd_nonneg _ _ _ _
        have h1 : smTerm η (E + ℓ) (a + 2 * L) (specOf A j) ≤
            (η / L) * (L / (E + ℓ - specOf A j)) ^ 2 := by
          refine b2.trans ?_
          have hu0 : 0 < E + ℓ - specOf A j := by linarith
          calc (a + 2 * L - (E + ℓ)) * η / (Real.pi * (E + ℓ - specOf A j) ^ 2)
              ≤ L * η / (E + ℓ - specOf A j) ^ 2 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                have hWπ : a + 2 * L - (E + ℓ) ≤ Real.pi * L := by
                  nlinarith [Real.pi_gt_three]
                calc (a + 2 * L - (E + ℓ)) * η * (E + ℓ - specOf A j) ^ 2
                    ≤ (Real.pi * L) * η * (E + ℓ - specOf A j) ^ 2 := by gcongr
                  _ = L * η * (Real.pi * (E + ℓ - specOf A j) ^ 2) := by ring
            _ = (η / L) * (L / (E + ℓ - specOf A j)) ^ 2 := by field_simp
        have h2 := mul_le_mul_of_nonneg_left (hdy.trans hle) (by positivity : 0 ≤ η / L)
        have : 0 ≤ 64 * L * η / r₀ ^ 2 := by positivity
        linarith
      · have hu2' : 4 ^ (K + 1) * L ≤ E + ℓ - specOf A j := not_lt.1 hu2
        have h1 := b2.trans (far_bound (L := L) (r₀ := r₀) (s := E + ℓ - specOf A j)
          hη hL hr₀ (by linarith) hW0 hW3)
        linarith
  · have hx : a + 2 * L < specOf A j := by linarith
    have b := smTerm_le_above hη hE12 hx
    have h1 := b.trans (far_bound (L := L) (r₀ := r₀) (s := specOf A j - (a + 2 * L))
      hη hL hr₀ (by linarith) hW0 hW3)
    linarith

private lemma dyadic_card_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {L r₀ C₀ Dδ Nr a E : ℝ} {d : ℕ} (K : ℕ)
    (hL : 0 < L) (hLr : 8 * L ≤ r₀) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ Dδ) (hNr : 0 ≤ Nr)
    (hd : eigCount A (a + r₀) = d) (hE : |E - a| ≤ L / 2)
    (hcnt : ∀ t ∈ Set.Icc (0 : ℝ) r₀,
      (eigCount A (a - t) : ℝ) - d ≤ Dδ + C₀ * Nr * t ^ (3 / 2 : ℝ))
    (hR1 : 4 ^ (K + 1) * L ≤ r₀ / 2) :
    ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k *
      ((eigWin A (E - 4 ^ (k + 1) * L) E).card : ℝ) ≤
      2 * Dδ + 48 * C₀ * Nr * L ^ (3 / 2 : ℝ) := by
  have hck : ∀ k ∈ Finset.range (K + 1), ((eigWin A (E - 4 ^ (k + 1) * L) E).card : ℝ) ≤
      Dδ + 24 * 8 ^ k * (C₀ * Nr * L ^ (3 / 2 : ℝ)) := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h4 : (4 : ℝ) ^ (k + 1) ≤ 4 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4' : (1 : ℝ) ≤ 4 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hrk : 4 ^ (k + 1) * L ≤ r₀ / 2 := (mul_le_mul_of_nonneg_right h4 hL.le).trans hR1
    have hLrk : L ≤ 4 ^ (k + 1) * L := by nlinarith
    have h := win_card_le A (r := 4 ^ (k + 1) * L) (C₀ := C₀) (Dδ := Dδ) (Nr := Nr) hd hE hL
      (by linarith) hcnt (by positivity) (by linarith)
    have h2 := half_add_rpow_le hL hLrk
    have h3 : (4 ^ (k + 1) * L) ^ (3 / 2 : ℝ) = 8 * 8 ^ k * L ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hL.le, four_pow_rpow, pow_succ]; ring
    have h5 : C₀ * Nr * (4 ^ (k + 1) * L + L / 2) ^ (3 / 2 : ℝ) ≤
        C₀ * Nr * (3 * (4 ^ (k + 1) * L) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₀ hNr)
    rw [h3] at h5
    have h6 : C₀ * Nr * (3 * (8 * 8 ^ k * L ^ (3 / 2 : ℝ))) =
        24 * 8 ^ k * (C₀ * Nr * L ^ (3 / 2 : ℝ)) := by ring
    linarith
  have hX : 0 ≤ C₀ * Nr * L ^ (3 / 2 : ℝ) := by positivity
  calc ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k *
        ((eigWin A (E - 4 ^ (k + 1) * L) E).card : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ k *
          (Dδ + 24 * (C₀ * Nr * L ^ (3 / 2 : ℝ))) := by
        apply Finset.sum_le_sum
        intro k hk
        have h1 := mul_le_mul_of_nonneg_left (hck k hk) (by positivity : (0 : ℝ) ≤ (1 / 16) ^ k)
        have h2 : (1 / 16 : ℝ) ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        have h3 : (1 / 16 : ℝ) ^ k * 8 ^ k = (1 / 2) ^ k := by
          rw [← mul_pow]; norm_num
        have h4 : (1 / 16 : ℝ) ^ k * (Dδ + 24 * 8 ^ k * (C₀ * Nr * L ^ (3 / 2 : ℝ))) ≤
            (1 / 2 : ℝ) ^ k * (Dδ + 24 * (C₀ * Nr * L ^ (3 / 2 : ℝ))) := by
          have : (1 / 16 : ℝ) ^ k * (Dδ + 24 * 8 ^ k * (C₀ * Nr * L ^ (3 / 2 : ℝ))) =
              (1 / 16 : ℝ) ^ k * Dδ +
                24 * (C₀ * Nr * L ^ (3 / 2 : ℝ)) * ((1 / 16 : ℝ) ^ k * 8 ^ k) := by
            ring
          rw [this, h3]
          have := mul_le_mul_of_nonneg_right h2 hD
          linarith
        exact h1.trans h4
    _ = (∑ k ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ k) *
          (Dδ + 24 * (C₀ * Nr * L ^ (3 / 2 : ℝ))) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * (Dδ + 24 * (C₀ * Nr * L ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by positivity)
    _ = 2 * Dδ + 48 * C₀ * Nr * L ^ (3 / 2 : ℝ) := by ring

private lemma bracket_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {η ℓ L r₀ C₀ Dδ Nr a E : ℝ} {d : ℕ}
    (hη : 0 < η) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) (hL : 0 < L) (hLr : 8 * L ≤ r₀)
    (hC₀ : 0 ≤ C₀) (hD : 0 ≤ Dδ) (hNr : 0 ≤ Nr)
    (hn : (n : ℝ) ≤ C₀ * Nr)
    (hd : eigCount A (a + r₀) = d) (hE : |E - a| ≤ L / 2)
    (hcnt : ∀ t ∈ Set.Icc (0 : ℝ) r₀,
      (eigCount A (a - t) : ℝ) - d ≤ Dδ + C₀ * Nr * t ^ (3 / 2 : ℝ)) :
    smCount A η (E + ℓ) (a + 2 * L) ≤ (eigCount A E : ℝ) - d +
      ((η / ℓ) * (Dδ + 3 * C₀ * Nr * L ^ (3 / 2 : ℝ)) +
        (η / L) * (2 * Dδ + 48 * C₀ * Nr * L ^ (3 / 2 : ℝ)) +
        C₀ * Nr * (64 * L * η / r₀ ^ 2)) := by
  have hr₀ : 0 < r₀ := by linarith
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hrE : E ≤ a + r₀ := by linarith
  have hE12 : E + ℓ ≤ a + 2 * L := by linarith
  have hK : (eigCount A E : ℝ) - d = (eigWin A E (a + r₀)).card := by
    have := eigCount_eq_add_card A hrE
    rw [hd] at this
    rw [this]; push_cast; ring
  obtain ⟨K, hR1, hR2⟩ := dyadic_scale hL hLr
  have hcf : 0 ≤ 64 * L * η / r₀ ^ 2 := by positivity
  have hS : ∀ j, 0 ≤ ∑ k ∈ Finset.range (K + 1),
      (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j :=
    fun j => Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (winInd_nonneg _ _ _ _)
  have hc0 : ((eigWin A (E - L) E).card : ℝ) ≤ Dδ + 3 * C₀ * Nr * L ^ (3 / 2 : ℝ) := by
    have h := win_card_le A (r := L) (C₀ := C₀) (Dδ := Dδ) (Nr := Nr) hd hE hL
      (by linarith) hcnt hL.le (by linarith)
    have h2 := half_add_rpow_le hL (le_refl L)
    have h3 : C₀ * Nr * (L + L / 2) ^ (3 / 2 : ℝ) ≤ C₀ * Nr * (3 * L ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₀ hNr)
    have h4 : C₀ * Nr * (3 * L ^ (3 / 2 : ℝ)) = 3 * C₀ * Nr * L ^ (3 / 2 : ℝ) := by ring
    linarith
  have hgeo := dyadic_card_sum A K hL hLr hC₀ hD hNr hd hE hcnt hR1
  have htot : ∑ j, ((η / ℓ) * winInd A E L j + (η / L) * ∑ k ∈ Finset.range (K + 1),
        (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j + 64 * L * η / r₀ ^ 2) ≤
      (η / ℓ) * (Dδ + 3 * C₀ * Nr * L ^ (3 / 2 : ℝ)) +
        (η / L) * (2 * Dδ + 48 * C₀ * Nr * L ^ (3 / 2 : ℝ)) +
        C₀ * Nr * (64 * L * η / r₀ ^ 2) := by
    have e1 : ∑ j, ((η / ℓ) * winInd A E L j + (η / L) * ∑ k ∈ Finset.range (K + 1),
        (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j + 64 * L * η / r₀ ^ 2) =
        (η / ℓ) * ((eigWin A (E - L) E).card : ℝ) +
        (η / L) * ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k *
          ((eigWin A (E - 4 ^ (k + 1) * L) E).card : ℝ) + n * (64 * L * η / r₀ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        winInd_sum, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, winInd_sum]
    rw [e1]
    have a1 := mul_le_mul_of_nonneg_left hc0 (by positivity : 0 ≤ η / ℓ)
    have a2 := mul_le_mul_of_nonneg_left hgeo (by positivity : 0 ≤ η / L)
    have a3 : (n : ℝ) * (64 * L * η / r₀ ^ 2) ≤ C₀ * Nr * (64 * L * η / r₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hn hcf
    linarith
  rw [smCount_eq_sum, ← Finset.sum_add_sum_compl (eigWin A E (a + r₀))]
  have s1 : ∑ j ∈ eigWin A E (a + r₀), smTerm η (E + ℓ) (a + 2 * L) (specOf A j) ≤
      ((eigWin A E (a + r₀)).card : ℝ) := by
    have := Finset.sum_le_card_nsmul (eigWin A E (a + r₀))
      (fun j => smTerm η (E + ℓ) (a + 2 * L) (specOf A j)) 1
      (fun j _ => smTerm_le_one _ _ _ _)
    simpa using this
  have s2 : ∑ j ∈ (eigWin A E (a + r₀))ᶜ, smTerm η (E + ℓ) (a + 2 * L) (specOf A j) ≤
      ∑ j, ((η / ℓ) * winInd A E L j + (η / L) * ∑ k ∈ Finset.range (K + 1),
        (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j + 64 * L * η / r₀ ^ 2) := by
    calc _ ≤ ∑ j ∈ (eigWin A E (a + r₀))ᶜ, ((η / ℓ) * winInd A E L j + (η / L) *
          ∑ k ∈ Finset.range (K + 1), (1 / 16 : ℝ) ^ k * winInd A E (4 ^ (k + 1) * L) j +
          64 * L * η / r₀ ^ 2) := by
          refine Finset.sum_le_sum fun j hj => lower_pt A K hη hℓ hℓL hL hLr hE hR2 j ?_
          have hj := Finset.mem_compl.1 hj
          simp only [eigWin, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le,
            not_lt] at hj
          rcases hj with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => by
          have := winInd_nonneg A E L j
          have := hS j
          positivity)
  rw [hK]
  linarith

private lemma err_arith {x ε δ C₀ r₀ η ℓ L : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (hδ : δ ≤ ε / 8)
    (hC₀ : 0 < C₀) (hr₀ : 0 < r₀)
    (hη : η = x ^ (-2 / 3 - 9 * ε)) (hℓ : ℓ = x ^ (-2 / 3 - ε)) (hL : L = x ^ (-2 / 3 + ε))
    (hc : 3 + 51 * C₀ + 64 * C₀ / r₀ ^ 2 ≤ x ^ (3 * ε / 2)) :
    (η / ℓ + η / L) * (x ^ δ + C₀ * x * L ^ (3 / 2 : ℝ)) ≤ x ^ (-5 * ε) ∧
    (η / ℓ) * (x ^ δ + 3 * C₀ * x * L ^ (3 / 2 : ℝ)) +
      (η / L) * (2 * x ^ δ + 48 * C₀ * x * L ^ (3 / 2 : ℝ)) +
      C₀ * x * (64 * L * η / r₀ ^ 2) ≤ x ^ (-5 * ε) := by
  have x0 : 0 < x := by linarith
  have e1 : η / ℓ = x ^ (-8 * ε) := by
    rw [hη, hℓ, ← Real.rpow_sub x0]; congr 1; ring
  have e2 : η / L = x ^ (-10 * ε) := by
    rw [hη, hL, ← Real.rpow_sub x0]; congr 1; ring
  have e3 : x * L ^ (3 / 2 : ℝ) = x ^ (3 * ε / 2) := by
    rw [hL, ← Real.rpow_mul x0.le]
    calc x * x ^ ((-2 / 3 + ε) * (3 / 2)) = x ^ (1 : ℝ) * x ^ ((-2 / 3 + ε) * (3 / 2)) := by
          rw [Real.rpow_one]
      _ = x ^ (3 * ε / 2) := by rw [← Real.rpow_add x0]; congr 1; ring
  have e4 : x * L * η = x ^ (-1 / 3 - 8 * ε) := by
    rw [hL, hη]
    calc x * x ^ (-2 / 3 + ε) * x ^ (-2 / 3 - 9 * ε)
        = x ^ (1 : ℝ) * x ^ (-2 / 3 + ε) * x ^ (-2 / 3 - 9 * ε) := by rw [Real.rpow_one]
      _ = x ^ (-1 / 3 - 8 * ε) := by
        rw [← Real.rpow_add x0, ← Real.rpow_add x0]; congr 1; ring
  have hq : 0 ≤ x ^ (-13 * ε / 2) := by positivity
  have b1 : x ^ (-8 * ε) * x ^ δ ≤ x ^ (-13 * ε / 2) := by
    rw [← Real.rpow_add x0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have b2 : x ^ (-8 * ε) * x ^ (3 * ε / 2) = x ^ (-13 * ε / 2) := by
    rw [← Real.rpow_add x0]; congr 1; ring
  have b3 : x ^ (-10 * ε) * x ^ δ ≤ x ^ (-13 * ε / 2) := by
    rw [← Real.rpow_add x0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have b4 : x ^ (-10 * ε) * x ^ (3 * ε / 2) ≤ x ^ (-13 * ε / 2) := by
    rw [← Real.rpow_add x0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have b5 : x ^ (-1 / 3 - 8 * ε) ≤ x ^ (-13 * ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have fin : x ^ (3 * ε / 2) * x ^ (-13 * ε / 2) = x ^ (-5 * ε) := by
    rw [← Real.rpow_add x0]; congr 1; ring
  have hd0 : 0 ≤ 64 * C₀ / r₀ ^ 2 := by positivity
  set q := x ^ (-13 * ε / 2) with hqdef
  set P := η / ℓ with hP
  set Q := η / L with hQ
  set Y := x * L ^ (3 / 2 : ℝ) with hY
  set D := x ^ δ with hD
  have hPY : P * Y = q := by rw [e1, e3]; exact b2
  have hPD : P * D ≤ q := by rw [e1]; exact b1
  have hQD : Q * D ≤ q := by rw [e2]; exact b3
  have hQY : Q * Y ≤ q := by rw [e2, e3]; exact b4
  have hxLη : x * L * η ≤ q := by rw [e4]; exact b5
  have hcq : (3 + 51 * C₀ + 64 * C₀ / r₀ ^ 2) * q ≤ x ^ (-5 * ε) := by
    rw [← fin]; exact mul_le_mul_of_nonneg_right hc hq
  have eU : (P + Q) * (D + C₀ * x * L ^ (3 / 2 : ℝ)) =
      P * D + C₀ * (P * Y) + Q * D + C₀ * (Q * Y) := by
    rw [hY]; ring
  have eL : P * (D + 3 * C₀ * x * L ^ (3 / 2 : ℝ)) + Q * (2 * D + 48 * C₀ * x * L ^ (3 / 2 : ℝ)) +
      C₀ * x * (64 * L * η / r₀ ^ 2) =
      P * D + 3 * C₀ * (P * Y) + 2 * (Q * D) + 48 * C₀ * (Q * Y) +
        (64 * C₀ / r₀ ^ 2) * (x * L * η) := by
    rw [hY]; ring
  constructor
  · rw [eU]
    have := mul_le_mul_of_nonneg_left hQY hC₀.le
    rw [hPY] at *
    nlinarith
  · rw [eL]
    have h1 := mul_le_mul_of_nonneg_left hQY (by positivity : 0 ≤ 48 * C₀)
    have h2 := mul_le_mul_of_nonneg_left hxLη hd0
    rw [hPY]
    nlinarith


private lemma bracket_eventually (ε C₀ r₀ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hr₀ : 0 < r₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ (N : ℝ) ∧ 8 * (N : ℝ) ^ (-2 / 3 + ε) ≤ r₀ ∧
      3 + 51 * C₀ + 64 * C₀ / r₀ ^ 2 ≤ (N : ℝ) ^ (3 * ε / 2) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have t1 : ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) := hnat.eventually_ge_atTop 1
  have t2 : ∀ᶠ N : ℕ in atTop, 8 * (N : ℝ) ^ (-2 / 3 + ε) ≤ r₀ := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-(2 / 3 - ε))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h1 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 / 3 - ε)) < r₀ / 8 :=
      (h0.comp hnat).eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1] with N hN
    have : (-2 / 3 + ε : ℝ) = -(2 / 3 - ε) := by ring
    rw [this]
    linarith
  have t3 : ∀ᶠ N : ℕ in atTop, 3 + 51 * C₀ + 64 * C₀ / r₀ ^ 2 ≤ (N : ℝ) ^ (3 * ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 3 * ε / 2)).comp hnat).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (t1.and (t2.and t3))
  exact ⟨N₀, fun N hN => by
    obtain ⟨a, b, c⟩ := hN₀ N hN
    exact ⟨a, b, c⟩⟩

/-- Deterministic bracketing of the eigenvalue count by the smoothed count:
`𝒳_{[E+ℓ, E_L]} - N^{-5ε} ≤ #{λ ∈ [E, E_L]} ≤ 𝒳_{[E-ℓ, E_L]} + N^{-5ε}` in the edge regime. -/
theorem smCount_bracket (l : ℕ) (ε C₀ r₀ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hC₀ : 0 < C₀)
    (hr₀ : 0 < r₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n d : ℕ) (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsHermitian →
      (n : ℝ) ≤ C₀ * N → EdgeRegime N a d l (ε / (8 * (l + 1))) r₀ C₀ A →
      ∀ E, |E - a| ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2 →
        smCount A (etaE N ε) (E + ellE N ε) (edgeEL N a ε) - (N : ℝ) ^ (-5 * ε) ≤
            (eigCount A E : ℝ) - d ∧
          (eigCount A E : ℝ) - d ≤
            smCount A (etaE N ε) (E - ellE N ε) (edgeEL N a ε) + (N : ℝ) ^ (-5 * ε) := by
  obtain ⟨N₀, hN₀⟩ := bracket_eventually ε C₀ r₀ hε hε1 hr₀
  refine ⟨N₀, fun N hN n d a A _ hn hreg E hE => ?_⟩
  obtain ⟨hx1, hLr, hc⟩ := hN₀ N hN
  obtain ⟨h1, h2, _, h4⟩ := hreg
  have x0 : (0 : ℝ) < N := by linarith
  have hδ0 : 0 < ε / (8 * ((l : ℝ) + 1)) := by positivity
  have hδ8 : ε / (8 * ((l : ℝ) + 1)) ≤ ε / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hL : 0 < (N : ℝ) ^ (-2 / 3 + ε) := Real.rpow_pos_of_pos x0 _
  have hη : 0 < etaE N ε := Real.rpow_pos_of_pos x0 _
  have hℓ : 0 < ellE N ε := Real.rpow_pos_of_pos x0 _
  have hℓL : ellE N ε ≤ (N : ℝ) ^ (-2 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hgL : (N : ℝ) ^ (-2 / 3 + ε / (8 * ((l : ℝ) + 1))) ≤ (N : ℝ) ^ (-2 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hgap : ∀ j, a + (N : ℝ) ^ (-2 / 3 + ε) ≤ specOf A j → a + r₀ ≤ specOf A j := by
    intro j hj
    have hsub : (Finset.univ.filter fun i => a + r₀ ≤ specOf A i) ⊆
        (Finset.univ.filter fun i => a + (N : ℝ) ^ (-2 / 3 + ε / (8 * ((l : ℝ) + 1))) ≤
          specOf A i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      linarith
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have e1 : (Finset.univ.filter fun i => a + (N : ℝ) ^ (-2 / 3 + ε / (8 * ((l : ℝ) + 1))) ≤
          specOf A i).card = d := h1
      have e2 : (Finset.univ.filter fun i => a + r₀ ≤ specOf A i).card = d := h2
      omega)
    have : j ∈ Finset.univ.filter fun i => a + (N : ℝ) ^ (-2 / 3 + ε / (8 * ((l : ℝ) + 1))) ≤
        specOf A i := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      linarith
    rw [← heq] at this
    simpa using this
  have hD : 0 ≤ (N : ℝ) ^ (ε / (8 * ((l : ℝ) + 1))) := by positivity
  have hLr' : (N : ℝ) ^ (-2 / 3 + ε) ≤ r₀ := by linarith
  have hLr8 : 8 * (N : ℝ) ^ (-2 / 3 + ε) ≤ r₀ := hLr
  have hup := bracket_upper A (η := etaE N ε) (ℓ := ellE N ε) (L := (N : ℝ) ^ (-2 / 3 + ε))
    (r₀ := r₀) (C₀ := C₀) (Dδ := (N : ℝ) ^ (ε / (8 * ((l : ℝ) + 1)))) (Nr := (N : ℝ)) (a := a)
    (E := E) (d := d) hη hℓ hL hLr' hC₀.le x0.le hgap h2 hE h4
  have hlo := bracket_lower A (η := etaE N ε) (ℓ := ellE N ε) (L := (N : ℝ) ^ (-2 / 3 + ε))
    (r₀ := r₀) (C₀ := C₀) (Dδ := (N : ℝ) ^ (ε / (8 * ((l : ℝ) + 1)))) (Nr := (N : ℝ)) (a := a)
    (E := E) (d := d) hη hℓ hℓL hL hLr8 hC₀.le hD x0.le hn h2 hE h4
  obtain ⟨ar1, ar2⟩ := err_arith (x := (N : ℝ)) (ε := ε) (δ := ε / (8 * ((l : ℝ) + 1)))
    (C₀ := C₀) (r₀ := r₀) (η := etaE N ε) (ℓ := ellE N ε) (L := (N : ℝ) ^ (-2 / 3 + ε))
    hx1 hε hδ8 hC₀ hr₀ rfl rfl rfl hc
  have hEL : edgeEL N a ε = a + 2 * (N : ℝ) ^ (-2 / 3 + ε) := rfl
  rw [hEL]
  constructor
  · linarith
  · linarith

end Anisotropic
