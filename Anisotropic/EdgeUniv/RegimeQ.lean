import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.Stability.EdgeTaylor
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.EdgeUniv.SmCount
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.Models
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Rigidity.Counting
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Gap
import Anisotropic.Rigidity.GaussCount

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The edge regime for `Q` -/

/-- The window radius `r₀(τ) = min(τ'(τ)/2, τ/2)` of the edge regime of `Q`. -/
def edgeR0 (τ : ℝ) : ℝ := min (edgeTau' τ / 2) (τ / 2)

/-- The local-count constant `C₀(τ) = 1 + 4/(3π √c₂)` of the edge regime of `Q`. -/
def edgeKc (τ : ℝ) : ℝ := 1 + 4 / (3 * Real.pi * Real.sqrt (edgec2 τ))


/-! ### Elementary facts on the constants -/

private lemma rq_edgeTau'_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau' τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  unfold edgeTau' edgeTau0
  positivity

private lemma rq_edgeC2_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeC2 τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  unfold edgeC2
  positivity

private lemma rq_edgeR0_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeR0 τ :=
  lt_min (half_pos (rq_edgeTau'_pos hτ)) (half_pos hτ)

private lemma rq_edgeR0_le_tau {τ : ℝ} : edgeR0 τ ≤ τ / 2 := min_le_right _ _

private lemma rq_edgeR0_le_tau' {τ : ℝ} : edgeR0 τ ≤ edgeTau' τ / 2 := min_le_left _ _

private lemma rq_neg_one_pow_odd {k : ℕ} (hk : k % 2 = 1) : (-1 : ℝ) ^ (k + 1) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
  simp

private lemma rq_neg_one_pow_even {k : ℕ} (hk : k % 2 = 0) : (-1 : ℝ) ^ (k + 1) = -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
  rw [pow_succ, pow_mul]
  simp

/-! ### Eigenvalue counting for `Q` and `-Q` -/

private lemma rq_QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Xm (show Sig.IsHermitian from hSig.isHermitian)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

open Polynomial in
private lemma rq_charpoly_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
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

private lemma rq_specOf_neg_perm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ e : Equiv.Perm (Fin n), specOf (-A) = fun j => -specOf A (e j) := by
  have hA' : (-A).IsHermitian := hA.neg
  have hD : (diagonal (fun j => -hA.eigenvalues j)).IsHermitian := isHermitian_diagonal _
  have h1 : hA'.eigenvalues = hD.eigenvalues :=
    (hA'.eigenvalues_eq_eigenvalues_iff hD).2 (rq_charpoly_neg hA)
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal (fun j => -hA.eigenvalues j)
  refine ⟨e, ?_⟩
  rw [specOf_eq hA', h1, ← specOf_eq hD, he, specOf_eq hA]
  rfl

/-- The number of eigenvalues of `A` that are `≤ x`. -/
private def rqLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j => specOf A j ≤ x).card

/-- The number of eigenvalues of `A` that are `> x`. -/
private def rqGt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j => x < specOf A j).card

private lemma rq_eigCount_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (E : ℝ) : eigCount (-A) E = rqLe A (-E) := by
  obtain ⟨e, he⟩ := rq_specOf_neg_perm hA
  unfold eigCount rqLe
  rw [he]
  refine Finset.card_equiv e ?_
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> linarith

private lemma rq_le_add_gt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    rqLe A x + rqGt A x = n := by
  unfold rqLe rqGt
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j => specOf A j ≤ x)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at this
  exact this

private lemma rq_gt_le_eigCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    rqGt A x ≤ eigCount A x := by
  unfold rqGt eigCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.le

private lemma rq_eigCount_le_gt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {x y : ℝ} (hxy : x < y) :
    eigCount A y ≤ rqGt A x := by
  unfold rqGt eigCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith

/-! ### Integrals of the square-root profile -/

private lemma rq_integral_sqrt (t : ℝ) :
    ∫ x in (0 : ℝ)..t, Real.sqrt x = 2 / 3 * t ^ (3 / 2 : ℝ) := by
  have h : ∀ x : ℝ, Real.sqrt x = x ^ (1 / 2 : ℝ) := fun x => Real.sqrt_eq_rpow x
  simp_rw [h]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  norm_num
  ring

private lemma rq_integral_sqrt_left (a t : ℝ) (ht : 0 ≤ t) :
    ∫ u in Set.Ico (a - t) a, Real.sqrt (a - u) = 2 / 3 * t ^ (3 / 2 : ℝ) := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_sub_left (fun x => Real.sqrt x) a]
  simp only [sub_self, sub_sub_cancel]
  exact rq_integral_sqrt t

private lemma rq_integral_sqrt_right (a t : ℝ) (ht : 0 ≤ t) :
    ∫ u in Set.Ico a (a + t), Real.sqrt (u - a) = 2 / 3 * t ^ (3 / 2 : ℝ) := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_sub_right (fun x => Real.sqrt x) a]
  simp only [sub_self, add_sub_cancel_left]
  exact rq_integral_sqrt t

/-! ### The mass of the band side of an edge -/

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rq_varrho_apply (N : ℕ) (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma rq_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) =
      varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- If `ρ ≥ g ≥ 0` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≥ N ∫_{[x,y)} g`. -/
private lemma rq_nClass_sub_ge {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) {g : ℝ → ℝ} (hgi : IntegrableOn g (Set.Ico x y))
    (hg0 : ∀ u ∈ Set.Ico x y, 0 ≤ g u) (hρ : ∀ u ∈ Set.Ico x y, g u ≤ rhoDens N σ u) :
    N * ∫ u in Set.Ico x y, g u ≤ nClass N σ x - nClass N σ y := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rq_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ico x y)] g :=
    (ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ hg0)
  have hge : ENNReal.ofReal (∫ u in Set.Ico x y, g u) ≤ varrho N σ (Set.Ico x y) := by
    rw [rq_varrho_apply N σ measurableSet_Ico hsub, ofReal_integral_eq_lintegral_ofReal hgi hnn]
    exact setLIntegral_mono' measurableSet_Ico fun u hu => ENNReal.ofReal_le_ofReal (hρ u hu)
  have h0 : 0 ≤ ∫ u in Set.Ico x y, g u := setIntegral_nonneg measurableSet_Ico hg0
  have h1 : ∫ u in Set.Ico x y, g u ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal h0] at this
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)

/-- If `0 ≤ ρ ≤ g` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≤ N ∫_{[x,y)} g`. -/
private lemma rq_nClass_sub_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) {g : ℝ → ℝ} (hgi : IntegrableOn g (Set.Ico x y))
    (hg0 : ∀ u ∈ Set.Ico x y, 0 ≤ g u) (hρ : ∀ u ∈ Set.Ico x y, rhoDens N σ u ≤ g u) :
    nClass N σ x - nClass N σ y ≤ N * ∫ u in Set.Ico x y, g u := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rq_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ico x y)] g :=
    (ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ hg0)
  have hle : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (∫ u in Set.Ico x y, g u) := by
    rw [rq_varrho_apply N σ measurableSet_Ico hsub, ofReal_integral_eq_lintegral_ofReal hgi hnn]
    exact setLIntegral_mono' measurableSet_Ico fun u hu => ENNReal.ofReal_le_ofReal (hρ u hu)
  have h0 : 0 ≤ ∫ u in Set.Ico x y, g u := setIntegral_nonneg measurableSet_Ico hg0
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ ∫ u in Set.Ico x y, g u := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal h0] at this
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)

/-- The density near a regular edge, on the band side. -/
private lemma rq_rho_bounds {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {E : ℝ}
    (hE : |E - edgeVal N σ k| ≤ edgeTau0 τ)
    (hs : (-1 : ℝ) ^ (k + 1) * (E - edgeVal N σ k) ≤ 0) :
    Real.sqrt |E - edgeVal N σ k| / (Real.pi * Real.sqrt (edgeC2 τ)) ≤ rhoDens N σ E ∧
      rhoDens N σ E ≤ 2 * Real.sqrt |E - edgeVal N σ k| / (Real.pi * Real.sqrt (edgec2 τ)) := by
  obtain ⟨h1, h2⟩ := (rhoDens_edge hda hk hE).1 hs
  have hC : 0 < Real.sqrt (edgeC2 τ) := Real.sqrt_pos.2 (rq_edgeC2_pos hτ)
  have hc : 0 < Real.sqrt (edgec2 τ) := Real.sqrt_pos.2 (edgec2_pos hτ)
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [Real.sqrt_div (abs_nonneg _)] at h1 h2
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc Real.sqrt |E - edgeVal N σ k| = Real.sqrt |E - edgeVal N σ k| / Real.sqrt (edgeC2 τ) *
          Real.sqrt (edgeC2 τ) := by field_simp
      _ ≤ Real.pi * rhoDens N σ E * Real.sqrt (edgeC2 τ) := by gcongr
      _ = _ := by ring
  · rw [le_div_iff₀ (by positivity)]
    calc rhoDens N σ E * (Real.pi * Real.sqrt (edgec2 τ)) =
          Real.pi * rhoDens N σ E * Real.sqrt (edgec2 τ) := by ring
      _ ≤ 2 * (Real.sqrt |E - edgeVal N σ k| / Real.sqrt (edgec2 τ)) * Real.sqrt (edgec2 τ) := by
          gcongr
      _ = _ := by field_simp

/-- Mass bounds on the band side of an odd edge: `n(a_k − t) − n(a_k) ≍ N t^{3/2}`. -/
private lemma rq_mass_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hk : RegularEdge τ N σ k)
    (hodd : k % 2 = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ edgeTau0 τ) (ht2 : t < edgeVal N σ k) :
    2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) * (N * t ^ (3 / 2 : ℝ)) ≤
        nClass N σ (edgeVal N σ k - t) - nClass N σ (edgeVal N σ k) ∧
      nClass N σ (edgeVal N σ k - t) - nClass N σ (edgeVal N σ k) ≤
        4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) * (N * t ^ (3 / 2 : ℝ)) := by
  set a := edgeVal N σ k with ha
  have hC : 0 < Real.sqrt (edgeC2 τ) := Real.sqrt_pos.2 (rq_edgeC2_pos hτ)
  have hc : 0 < Real.sqrt (edgec2 τ) := Real.sqrt_pos.2 (edgec2_pos hτ)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : 0 < a - t := by linarith
  have hxy : a - t ≤ a := by linarith
  have hcont : Continuous fun u : ℝ => Real.sqrt (a - u) :=
    Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
  have hdens : ∀ u ∈ Set.Ico (a - t) a,
      Real.sqrt (a - u) / (Real.pi * Real.sqrt (edgeC2 τ)) ≤ rhoDens N σ u ∧
        rhoDens N σ u ≤ 2 * Real.sqrt (a - u) / (Real.pi * Real.sqrt (edgec2 τ)) := by
    intro u hu
    have hab : |u - a| = a - u := by rw [abs_of_nonpos (by linarith [hu.2])]; ring
    have := rq_rho_bounds hτ hda hk (E := u) (by rw [hab]; linarith [hu.1]) (by
      rw [rq_neg_one_pow_odd hodd, one_mul]; linarith [hu.2])
    rwa [hab] at this
  constructor
  · have hint : IntegrableOn (fun u => 1 / (Real.pi * Real.sqrt (edgeC2 τ)) * Real.sqrt (a - u))
        (Set.Ico (a - t) a) :=
      ((continuous_const.mul hcont).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
    have := rq_nClass_sub_ge (σ := σ) hda.nonneg hN hx hxy hint (fun u hu => by positivity)
      (fun u hu => by
        have := (hdens u hu).1
        calc 1 / (Real.pi * Real.sqrt (edgeC2 τ)) * Real.sqrt (a - u)
            = Real.sqrt (a - u) / (Real.pi * Real.sqrt (edgeC2 τ)) := by ring
          _ ≤ _ := this)
    rw [integral_const_mul, rq_integral_sqrt_left a t ht0] at this
    calc 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) * (N * t ^ (3 / 2 : ℝ))
        = N * (1 / (Real.pi * Real.sqrt (edgeC2 τ)) * (2 / 3 * t ^ (3 / 2 : ℝ))) := by
          field_simp
      _ ≤ _ := this
  · have hint : IntegrableOn (fun u => 2 / (Real.pi * Real.sqrt (edgec2 τ)) * Real.sqrt (a - u))
        (Set.Ico (a - t) a) :=
      ((continuous_const.mul hcont).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
    have := rq_nClass_sub_le (σ := σ) hda.nonneg hN hx hxy hint (fun u hu => by positivity)
      (fun u hu => by
        have := (hdens u hu).2
        calc rhoDens N σ u ≤ 2 * Real.sqrt (a - u) / (Real.pi * Real.sqrt (edgec2 τ)) := this
          _ = 2 / (Real.pi * Real.sqrt (edgec2 τ)) * Real.sqrt (a - u) := by ring)
    rw [integral_const_mul, rq_integral_sqrt_left a t ht0] at this
    calc _ ≤ _ := this
      _ = 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) * (N * t ^ (3 / 2 : ℝ)) := by
          field_simp
          ring

/-- Mass bounds on the band side of an even edge: `n(a_k) − n(a_k + t) ≍ N t^{3/2}`. -/
private lemma rq_mass_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hk : RegularEdge τ N σ k)
    (hev : k % 2 = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ edgeTau0 τ) :
    2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) * (N * t ^ (3 / 2 : ℝ)) ≤
        nClass N σ (edgeVal N σ k) - nClass N σ (edgeVal N σ k + t) ∧
      nClass N σ (edgeVal N σ k) - nClass N σ (edgeVal N σ k + t) ≤
        4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) * (N * t ^ (3 / 2 : ℝ)) := by
  set a := edgeVal N σ k with ha
  have hC : 0 < Real.sqrt (edgeC2 τ) := Real.sqrt_pos.2 (rq_edgeC2_pos hτ)
  have hc : 0 < Real.sqrt (edgec2 τ) := Real.sqrt_pos.2 (edgec2_pos hτ)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : 0 < a := lt_of_lt_of_le (by linarith [hk.2.2.1] : (0 : ℝ) < τ) hk.2.2.1
  have hxy : a ≤ a + t := by linarith
  have hcont : Continuous fun u : ℝ => Real.sqrt (u - a) :=
    Real.continuous_sqrt.comp (continuous_id.sub continuous_const)
  have hdens : ∀ u ∈ Set.Ico a (a + t),
      Real.sqrt (u - a) / (Real.pi * Real.sqrt (edgeC2 τ)) ≤ rhoDens N σ u ∧
        rhoDens N σ u ≤ 2 * Real.sqrt (u - a) / (Real.pi * Real.sqrt (edgec2 τ)) := by
    intro u hu
    have hab : |u - a| = u - a := abs_of_nonneg (by linarith [hu.1])
    have := rq_rho_bounds hτ hda hk (E := u) (by rw [hab]; linarith [hu.2]) (by
      rw [rq_neg_one_pow_even hev]; linarith [hu.1])
    rwa [hab] at this
  constructor
  · have hint : IntegrableOn (fun u => 1 / (Real.pi * Real.sqrt (edgeC2 τ)) * Real.sqrt (u - a))
        (Set.Ico a (a + t)) :=
      ((continuous_const.mul hcont).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
    have := rq_nClass_sub_ge (σ := σ) hda.nonneg hN hx hxy hint (fun u hu => by positivity)
      (fun u hu => by
        have := (hdens u hu).1
        calc 1 / (Real.pi * Real.sqrt (edgeC2 τ)) * Real.sqrt (u - a)
            = Real.sqrt (u - a) / (Real.pi * Real.sqrt (edgeC2 τ)) := by ring
          _ ≤ _ := this)
    rw [integral_const_mul, rq_integral_sqrt_right a t ht0] at this
    calc 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) * (N * t ^ (3 / 2 : ℝ))
        = N * (1 / (Real.pi * Real.sqrt (edgeC2 τ)) * (2 / 3 * t ^ (3 / 2 : ℝ))) := by
          field_simp
      _ ≤ _ := this
  · have hint : IntegrableOn (fun u => 2 / (Real.pi * Real.sqrt (edgec2 τ)) * Real.sqrt (u - a))
        (Set.Ico a (a + t)) :=
      ((continuous_const.mul hcont).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
    have := rq_nClass_sub_le (σ := σ) hda.nonneg hN hx hxy hint (fun u hu => by positivity)
      (fun u hu => by
        have := (hdens u hu).2
        calc rhoDens N σ u ≤ 2 * Real.sqrt (u - a) / (Real.pi * Real.sqrt (edgec2 τ)) := this
          _ = 2 / (Real.pi * Real.sqrt (edgec2 τ)) * Real.sqrt (u - a) := by ring)
    rw [integral_const_mul, rq_integral_sqrt_right a t ht0] at this
    calc _ ≤ _ := this
      _ = 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) * (N * t ^ (3 / 2 : ℝ)) := by
          field_simp
          ring

/-! ### The edge values and the support of `ϱ` around a regular edge -/

private lemma rq_edgeVal_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (edgeVal_succ_le N σ hσ hN hS (by omega) (by omega)).trans (ih (by omega))

/-- The edges `l ≠ k` next to an odd regular edge `k`: below `a_k − τ`, or above `a_{k-1}`. -/
private lemma rq_edge_dich_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hodd : k % 2 = 1) {l : ℕ}
    (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands N σ) (hlk : l ≠ k) :
    edgeVal N σ l ≤ edgeVal N σ k - τ ∨ (3 ≤ k ∧ edgeVal N σ (k - 1) ≤ edgeVal N σ l) := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  rcases lt_or_gt_of_ne hlk with hlt | hgt
  · right
    exact ⟨by omega, rq_edgeVal_anti N σ hσ hN hS hl1 (by omega) (by omega)⟩
  · left
    have h1 := rq_edgeVal_anti N σ hσ hN hS hk1 hgt.le hl2
    have h2 := hsep l hl1 hl2 hlk
    rw [abs_of_nonneg (by linarith)] at h2
    linarith

/-- The edges `l ≠ k` next to an even regular edge `k`: above `a_k + τ`, or below `a_{k+1}`. -/
private lemma rq_edge_dich_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) {l : ℕ}
    (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands N σ) (hlk : l ≠ k) :
    edgeVal N σ k + τ ≤ edgeVal N σ l ∨
      (k < 2 * numBands N σ ∧ edgeVal N σ l ≤ edgeVal N σ (k + 1)) := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  rcases lt_or_gt_of_ne hlk with hlt | hgt
  · left
    have h1 := rq_edgeVal_anti N σ hσ hN hS hl1 hlt.le hk2
    have h2 := hsep l hl1 hl2 hlk
    rw [abs_of_nonpos (by linarith)] at h2
    linarith
  · right
    exact ⟨by omega, rq_edgeVal_anti N σ hσ hN hS (by omega) (by omega) hl2⟩

/-- A point of `supp ϱ` next to an odd regular edge `k`: at most `a_k`, or at least `a_{k-1}`. -/
private lemma rq_supp_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hτ : 0 < τ) (hodd : k % 2 = 1) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) :
    y ≤ edgeVal N σ k ∨ (3 ≤ k ∧ edgeVal N σ (k - 1) ≤ y) := by
  obtain ⟨hk1, hk2, hka, -, -⟩ := hk
  by_cases hy0 : y ≤ 0
  · left; linarith
  push Not at hy0
  obtain ⟨j, hj1, hj2, hyj⟩ := (mem_support_varrho_iff N σ hσ hN hS hy0).1 hy
  by_cases hkj : k ≤ 2 * j - 1
  · left
    exact hyj.2.trans (rq_edgeVal_anti N σ hσ hN hS hk1 hkj (by omega))
  · right
    refine ⟨by omega, ?_⟩
    exact (rq_edgeVal_anti N σ hσ hN hS (by omega) (by omega) (by omega)).trans hyj.1

/-- A point of `supp ϱ` next to an even regular edge `k`: at least `a_k`, at most `a_{k+1}`, or
nonpositive. -/
private lemma rq_supp_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hev : k % 2 = 0) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) :
    edgeVal N σ k ≤ y ∨ (k < 2 * numBands N σ ∧ y ≤ edgeVal N σ (k + 1)) ∨ y ≤ 0 := by
  obtain ⟨hk1, hk2, hka, -, -⟩ := hk
  by_cases hy0 : y ≤ 0
  · right; right; exact hy0
  push Not at hy0
  obtain ⟨j, hj1, hj2, hyj⟩ := (mem_support_varrho_iff N σ hσ hN hS hy0).1 hy
  by_cases hkj : 2 * j ≤ k
  · left
    exact (rq_edgeVal_anti N σ hσ hN hS (by omega) hkj hk2).trans hyj.1
  · right; left
    exact ⟨by omega, hyj.2.trans (rq_edgeVal_anti N σ hσ hN hS (by omega) (by omega) (by omega))⟩

/-! ### The classical counting function at the edge -/

private lemma rq_nClass_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hda : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hodd : k % 2 = 1) :
    nClass N σ (edgeVal N σ k) = (edgeD N σ k : ℝ) := by
  obtain ⟨hk1, hk2, -⟩ := hk
  have h := (nClass_edgeVal hda (k := (k + 1) / 2) (by omega) (by omega)).1
  have e : 2 * ((k + 1) / 2) - 1 = k := by omega
  rw [e] at h
  simp only [edgeD, hodd, ↓reduceIte]
  exact h

private lemma rq_nClass_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hda : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hev : k % 2 = 0) (hτ : 0 < τ) :
    nClass N σ (edgeVal N σ k) = (cumCount N σ ((k + 1) / 2) : ℝ) := by
  obtain ⟨hk1, hk2, hka, -⟩ := hk
  have h := (nClass_edgeVal hda (k := (k + 1) / 2) (by omega) (by omega)).2
  have e : 2 * ((k + 1) / 2) = k := by omega
  rw [e] at h
  exact h (by linarith)

/-! ### The edge regime from the counting estimates: odd edges -/

private lemma rq_det_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hk : RegularEdge τ N σ k) (hodd : k % 2 = 1)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) (Q : Matrix (Fin N) (Fin N) ℝ)
    (ht₀ : (N : ℝ) ^ (-2 / 3 + δ) ≤ edgeR0 τ)
    (hnum : (l : ℝ) + (N : ℝ) ^ (δ / 2) ≤ 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) *
      ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ)))
    (hcnt : ∀ E ∈ Set.Icc (edgeVal N σ k - edgeTau' τ) (edgeVal N σ k + edgeTau' τ),
      |(eigCount Q E : ℝ) - nClass N σ E| ≤ (N : ℝ) ^ (δ / 2))
    (hmid₁ : eigCount Q (edgeVal N σ k + (N : ℝ) ^ (-2 / 3 + δ)) = edgeD N σ k)
    (hmid₂ : eigCount Q (edgeVal N σ k + edgeR0 τ) = edgeD N σ k) :
    EdgeRegime N (edgeVal N σ k) (edgeD N σ k) l δ (edgeR0 τ) (edgeKc τ) Q := by
  have hτ' := rq_edgeTau'_pos hτ
  have hr0 := rq_edgeR0_pos hτ
  have hr0a := rq_edgeR0_le_tau' (τ := τ)
  have hr0b := rq_edgeR0_le_tau (τ := τ)
  have hak : τ ≤ edgeVal N σ k := hk.2.2.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0pos : 0 ≤ (N : ℝ) ^ (-2 / 3 + δ) := (Real.rpow_pos_of_pos hNpos _).le
  have htau0 : edgeTau0 τ = 4 * edgeTau' τ := by unfold edgeTau'; ring
  have hnc := rq_nClass_odd hda hk hodd
  refine ⟨hmid₁, hmid₂, ?_, ?_⟩
  · -- at least `d + l` eigenvalues above `a - N^{-2/3+δ}`
    have hw := hcnt (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ))
      ⟨by linarith, by linarith⟩
    have hm := (rq_mass_odd hτ hda hN hk hodd ht0pos (by rw [htau0]; linarith)
      (by linarith)).1
    rw [abs_le] at hw
    have : ((edgeD N σ k + l : ℕ) : ℝ) ≤ eigCount Q (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ)) := by
      push_cast
      linarith [hw.1]
    exact_mod_cast this
  · intro t ht
    have hw := hcnt (edgeVal N σ k - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hm := (rq_mass_odd hτ hda hN hk hodd ht.1 (by rw [htau0]; linarith [ht.2])
      (by linarith [ht.2])).2
    rw [abs_le] at hw
    have h1 : (N : ℝ) ^ (δ / 2) ≤ (N : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : 0 ≤ (N : ℝ) * t ^ (3 / 2 : ℝ) := by
      have := Real.rpow_nonneg ht.1 (3 / 2 : ℝ)
      positivity
    have hK : edgeKc τ = 1 + 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) := rfl
    have hKnn : 0 ≤ 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) := by positivity
    rw [hK]
    nlinarith [hw.2, hm, h1, h2, hKnn]

/-! ### The edge regime from the counting estimates: even edges -/

private lemma rq_det_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hk : RegularEdge τ N σ k) (hev : k % 2 = 0)
    (hcN : cumCount N σ ((k + 1) / 2) ≤ N)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.IsHermitian)
    (ht₀ : (N : ℝ) ^ (-2 / 3 + δ) ≤ edgeR0 τ)
    (hnum : (l : ℝ) + (N : ℝ) ^ (δ / 2) ≤ 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) *
      ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ)))
    (hcnt : ∀ E ∈ Set.Icc (edgeVal N σ k - edgeTau' τ) (edgeVal N σ k + edgeTau' τ),
      |(eigCount Q E : ℝ) - nClass N σ E| ≤ (N : ℝ) ^ (δ / 2))
    (hmid₁ : rqGt Q (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ)) = cumCount N σ ((k + 1) / 2))
    (hmid₂ : rqGt Q (edgeVal N σ k - edgeR0 τ) = cumCount N σ ((k + 1) / 2)) :
    EdgeRegime N (-edgeVal N σ k) (N - cumCount N σ ((k + 1) / 2)) l δ (edgeR0 τ) (edgeKc τ)
      (-Q) := by
  have hτ' := rq_edgeTau'_pos hτ
  have hr0 := rq_edgeR0_pos hτ
  have hr0a := rq_edgeR0_le_tau' (τ := τ)
  have hr0b := rq_edgeR0_le_tau (τ := τ)
  have hak : τ ≤ edgeVal N σ k := hk.2.2.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0pos : 0 ≤ (N : ℝ) ^ (-2 / 3 + δ) := (Real.rpow_pos_of_pos hNpos _).le
  have htau0 : edgeTau0 τ = 4 * edgeTau' τ := by unfold edgeTau'; ring
  have hnc := rq_nClass_even hda hk hev hτ
  set c := cumCount N σ ((k + 1) / 2) with hc
  set a := edgeVal N σ k with ha
  have hcast : ((N - c : ℕ) : ℝ) = (N : ℝ) - c := Nat.cast_sub hcN
  have hle : ∀ x, rqLe Q x = N - rqGt Q x := fun x => by
    have := rq_le_add_gt Q x
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rq_eigCount_neg hQ, show -(-a + (N : ℝ) ^ (-2 / 3 + δ)) = a - (N : ℝ) ^ (-2 / 3 + δ) by
      ring, hle, hmid₁]
  · rw [rq_eigCount_neg hQ, show -(-a + edgeR0 τ) = a - edgeR0 τ by ring, hle, hmid₂]
  · rw [rq_eigCount_neg hQ, show -(-a - (N : ℝ) ^ (-2 / 3 + δ)) = a + (N : ℝ) ^ (-2 / 3 + δ) by
      ring, hle]
    have hw := hcnt (a + (N : ℝ) ^ (-2 / 3 + δ)) ⟨by linarith, by linarith⟩
    have hm := (rq_mass_even hτ hda hN hk hev ht0pos (by rw [htau0]; linarith)).1
    rw [abs_le] at hw
    have h1 : rqGt Q (a + (N : ℝ) ^ (-2 / 3 + δ)) ≤ eigCount Q (a + (N : ℝ) ^ (-2 / 3 + δ)) :=
      rq_gt_le_eigCount _ _
    have h2 : (rqGt Q (a + (N : ℝ) ^ (-2 / 3 + δ)) : ℝ) + l ≤ c := by
      have h1' : (rqGt Q (a + (N : ℝ) ^ (-2 / 3 + δ)) : ℝ) ≤
          eigCount Q (a + (N : ℝ) ^ (-2 / 3 + δ)) := by exact_mod_cast h1
      linarith [hw.2]
    have h3 : rqGt Q (a + (N : ℝ) ^ (-2 / 3 + δ)) + l ≤ c := by exact_mod_cast h2
    have h4 := rq_le_add_gt Q (a + (N : ℝ) ^ (-2 / 3 + δ))
    omega
  · intro t ht
    rw [rq_eigCount_neg hQ, show -(-a - t) = a + t by ring, hle, hcast]
    have hKnn : 0 ≤ 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) := by positivity
    have h1 : (N : ℝ) ^ (δ / 2) ≤ (N : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    set K := 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) with hK
    have hKc : edgeKc τ = 1 + K := rfl
    have hrg : (((N - rqGt Q (a + t) : ℕ) : ℝ)) = (N : ℝ) - rqGt Q (a + t) := by
      have : rqGt Q (a + t) ≤ N := by
        have := rq_le_add_gt Q (a + t)
        omega
      exact Nat.cast_sub this
    rw [hrg]
    -- for every `s ∈ (0, τ'/2]`
    have key : ∀ s ∈ Set.Ioo (0 : ℝ) (edgeTau' τ / 2),
        (c : ℝ) - rqGt Q (a + t) ≤ (N : ℝ) ^ (δ / 2) + K * ((N : ℝ) * (t + s) ^ (3 / 2 : ℝ)) := by
      intro s hs
      have hw := hcnt (a + t + s) ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
      have hm := (rq_mass_even hτ hda hN hk hev (t := t + s) (by linarith [ht.1, hs.1])
        (by rw [htau0]; linarith [ht.2, hs.2])).2
      rw [abs_le] at hw
      have hg : (eigCount Q (a + t + s) : ℝ) ≤ rqGt Q (a + t) := by
        exact_mod_cast rq_eigCount_le_gt Q (show a + t < a + t + s by linarith [hs.1])
      rw [show a + (t + s) = a + t + s by ring] at hm
      linarith [hw.1]
    have hlim : Tendsto (fun s : ℝ => (N : ℝ) ^ (δ / 2) + K * ((N : ℝ) * (t + s) ^ (3 / 2 : ℝ)))
        (𝓝[>] 0) (𝓝 ((N : ℝ) ^ (δ / 2) + K * ((N : ℝ) * (t + 0) ^ (3 / 2 : ℝ)))) := by
      have hcont : ContinuousAt (fun s : ℝ => (N : ℝ) ^ (δ / 2) +
          K * ((N : ℝ) * (t + s) ^ (3 / 2 : ℝ))) 0 := by
        refine continuousAt_const.add (continuousAt_const.mul (continuousAt_const.mul ?_))
        have h := Real.continuousAt_rpow_const (t + 0) (3 / 2 : ℝ) (Or.inr (by norm_num))
        exact h.comp (f := fun s : ℝ => t + s) (x := 0) (continuousAt_const.add continuousAt_id)
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev' : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        (c : ℝ) - rqGt Q (a + t) ≤ (N : ℝ) ^ (δ / 2) + K * ((N : ℝ) * (t + s) ^ (3 / 2 : ℝ)) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hτ')) key
    have hfin := ge_of_tendsto hlim hev'
    rw [add_zero] at hfin
    have h2 : 0 ≤ (N : ℝ) * t ^ (3 / 2 : ℝ) := by
      have := Real.rpow_nonneg ht.1 (3 / 2 : ℝ)
      positivity
    rw [hKc]
    nlinarith [hfin, h1, h2, hKnn]

/-! ### The thresholds in `N` -/

private lemma rq_rpow_ge {b e x : ℝ} (hb : 0 < b) (he : 0 < e) (hx : b ^ (1 / e) ≤ x) :
    b ≤ x ^ e := by
  calc b = (b ^ (1 / e)) ^ e := by
        rw [← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
    _ ≤ x ^ e := Real.rpow_le_rpow (Real.rpow_nonneg hb.le _) hx he.le

/-- For `N` large: `N^{-2/3+δ} ≤ r₀`, and `l + N^{δ/2} ≤ c N · (N^{-2/3+δ})^{3/2}` with the
lower mass constant `c`. -/
private lemma rq_numeric (τ : ℝ) (l : ℕ) (δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ) (hδ1 : δ < 2 / 3) :
    ∃ N₅ : ℕ, 3 ≤ N₅ ∧ ∀ N : ℕ, N₅ ≤ N →
      (N : ℝ) ^ (-2 / 3 + δ) ≤ edgeR0 τ ∧
        (l : ℝ) + (N : ℝ) ^ (δ / 2) ≤ 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) *
          ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ)) := by
  have hr0 := rq_edgeR0_pos hτ
  have hC : 0 < Real.sqrt (edgeC2 τ) := Real.sqrt_pos.2 (rq_edgeC2_pos hτ)
  have hπ : 0 < Real.pi := Real.pi_pos
  set cc : ℝ := 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) with hcc
  have hcc0 : 0 < cc := by positivity
  set e : ℝ := 2 / 3 - δ with he
  have he0 : 0 < e := by linarith
  refine ⟨max 3 (max ⌈(edgeR0 τ)⁻¹ ^ (1 / e)⌉₊ ⌈((l + 1 : ℝ) / cc) ^ (1 / δ)⌉₊), le_max_left _ _,
    fun N hN => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : ⌈(edgeR0 τ)⁻¹ ^ (1 / e)⌉₊ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN2 : ⌈((l + 1 : ℝ) / cc) ^ (1 / δ)⌉₊ ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by linarith
  have hb1 : (edgeR0 τ)⁻¹ ^ (1 / e) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN1)
  have hb2 : ((l + 1 : ℝ) / cc) ^ (1 / δ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN2)
  constructor
  · have h1 := rq_rpow_ge (inv_pos.2 hr0) he0 hb1
    have h2 : (N : ℝ) ^ (-2 / 3 + δ) = ((N : ℝ) ^ e)⁻¹ := by
      rw [← Real.rpow_neg hNpos.le]; congr 1; rw [he]; ring
    rw [h2, inv_le_comm₀ (Real.rpow_pos_of_pos hNpos _) hr0]
    exact h1
  · have h1 := rq_rpow_ge (div_pos (by positivity : (0 : ℝ) < l + 1) hcc0) hδ hb2
    have h2 : (N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ) =
        (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ δ := by
      rw [← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      have : (N : ℝ) * (N : ℝ) ^ ((-2 / 3 + δ) * (3 / 2)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ ((-2 / 3 + δ) * (3 / 2)) := by rw [Real.rpow_one]
      rw [this, ← Real.rpow_add hNpos]
      congr 1; ring
    rw [h2]
    have hp1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hNr1 (by linarith)
    have h3 : (l : ℝ) + 1 ≤ (N : ℝ) ^ δ * cc := (div_le_iff₀ hcc0).1 h1
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ (δ / 2))
    have h5 : 0 ≤ ((N : ℝ) ^ (δ / 2) - 1) * l :=
      mul_nonneg (by linarith) (Nat.cast_nonneg l)
    nlinarith [h4, h5]

/-! ### High-probability events and deterministic consequences -/

private lemma rq_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : HighProbAt N D A) (hAB : A ⊆ B) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 hAB)).trans h

private lemma rq_hp_inter3 {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B C : Set Ω}
    (hN : 3 ≤ N) (hA : HighProbAt N (D + 1) A) (hB : HighProbAt N (D + 1) B)
    (hC : HighProbAt N (D + 1) C) : HighProbAt N D (A ∩ B ∩ C) := by
  unfold HighProbAt at *
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hsub : (A ∩ B ∩ C)ᶜ ⊆ (Aᶜ ∪ Bᶜ) ∪ Cᶜ := by
    intro ω h
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union] at h ⊢
    tauto
  have hx0 : 0 ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hpos.le _
  calc ℙ (A ∩ B ∩ C)ᶜ ≤ ℙ ((Aᶜ ∪ Bᶜ) ∪ Cᶜ) := measure_mono hsub
    _ ≤ ℙ Aᶜ + ℙ Bᶜ + ℙ Cᶜ :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) +
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := add_le_add (add_le_add hA hB) hC
    _ = ENNReal.ofReal (3 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hx0 hx0, ← ENNReal.ofReal_add (by positivity) hx0]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
          rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hpos, Real.rpow_neg_one]
        rw [this]
        have h0 : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hpos.le _
        rw [← mul_assoc, mul_comm 3, mul_assoc]
        have : 3 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hpos]; exact hN'
        nlinarith

private lemma rq_eigCount_eq_of_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {α g E : ℝ}
    (hnone : ∀ j, specOf A j ∉ Set.Icc α g) (hαE : α ≤ E) (hEg : E ≤ g) :
    eigCount A E = eigCount A g := by
  refine le_antisymm ?_ (eigCount_antitone A hEg)
  unfold eigCount
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  by_contra h
  exact hnone j ⟨by linarith, (not_le.1 h).le⟩

private lemma rq_gt_eq_of_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {g u v : ℝ}
    (hnone : ∀ j, specOf A j ∉ Set.Icc g u) (hgv : g ≤ v) (hvu : v ≤ u) :
    rqGt A v = eigCount A g := by
  unfold rqGt eigCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; linarith
  · intro h
    by_contra h'
    exact hnone j ⟨h, by linarith [not_lt.1 h']⟩

private lemma rq_le_infDist {S : Set ℝ} (hS : S.Nonempty) {w t : ℝ}
    (h : ∀ y ∈ S, t ≤ |w - y|) : t ≤ Metric.infDist w S :=
  (Metric.le_infDist hS).2 fun y hy => by rw [Real.dist_eq]; exact h y hy

private lemma rq_ak_mem_supp {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hτ : 0 < τ) :
    edgeVal N σ k ∈ (varrho N σ).support := by
  obtain ⟨hk1, hk2, hka, -⟩ := hk
  have hpos : 0 < edgeVal N σ k := by linarith
  rw [mem_support_varrho_iff N σ hσ hN hS hpos]
  refine ⟨(k + 1) / 2, by omega, by omega, ?_⟩
  have hlt := edgeVal_band_lt N σ hσ hN hS (k := (k + 1) / 2) (by omega) (by omega)
  by_cases hodd : k % 2 = 1
  · have e : 2 * ((k + 1) / 2) - 1 = k := by omega
    rw [e] at hlt ⊢
    exact ⟨hlt.le, le_rfl⟩
  · have e : 2 * ((k + 1) / 2) = k := by omega
    rw [e] at hlt ⊢
    exact ⟨le_rfl, hlt.le⟩

private lemma rq_edgeVal_nonneg {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hN : 0 < N) (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ 2 * numBands N σ) : 0 ≤ edgeVal N σ k :=
  (edgeVal_mem_Icc N σ hda.nonneg hN hS hda.pos hda.phi_lower hda.phi_upper hda.bound_Sigma
    hk1 hk).1

/-- Assumption 2.1 under (T_diag) gives the density assumptions for `specOf Σ`, positivity of
its entries, `M > 0` and a positive value among them. -/
private lemma rq_basic {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) (hτ : 0 < τ) :
    DensityAssumptions τ N (specOf Sig) ∧ (∀ i, 0 < specOf Sig i) ∧ 0 < M ∧
      (posVals (specOf Sig)).Nonempty := by
  have hdm := hm.diagModel_specOf
  have hM : 0 < M := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := hm.ratio_ge
    rw [h0] at this
    simp at this
    linarith
  refine ⟨hdm.densityAssumptions hτ, hdm.pos, hM, ?_⟩
  exact ⟨specOf Sig ⟨0, hM⟩, Finset.mem_filter.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hdm.pos _⟩⟩

private lemma rq_cumCount_top {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (hN : 0 < N) (hM : 0 < M) (hp : 1 ≤ numBands N σ) :
    cumCount N σ (numBands N σ) = min M N := by
  have h1 := (cumCount_spec hda (k := numBands N σ) hp le_rfl).1
  have h2 := (Ni_sum N σ hσ hN hM).2
  have : ((cumCount N σ (numBands N σ) : ℕ) : ℝ) = ((min M N : ℕ) : ℝ) := by
    rw [h1, h2, Nat.cast_min, min_comm]
  exact_mod_cast this

/-- Consecutive edges `a_{k-1}`, `a_k` at an odd regular edge `k ≥ 3`. -/
private lemma rq_gap_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hk3 : 3 ≤ k) :
    edgeVal N σ k + τ ≤ edgeVal N σ (k - 1) := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  have h1 := rq_edgeVal_anti N σ hσ hN hS (i := k - 1) (j := k) (by omega) (by omega) hk2
  have h2 := hsep (k - 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonpos (by linarith)] at h2
  linarith

/-- Consecutive edges `a_k`, `a_{k+1}` at an even regular edge `k < 2p`. -/
private lemma rq_gap_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hk : RegularEdge τ N σ k) (hkp : k < 2 * numBands N σ) :
    edgeVal N σ (k + 1) + τ ≤ edgeVal N σ k := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  have h1 := rq_edgeVal_anti N σ hσ hN hS (i := k) (j := k + 1) hk1 (by omega) (by omega)
  have h2 := hsep (k + 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonneg (by linarith)] at h2
  linarith

/-! ### The events for the gap above an odd edge and below an even edge -/

private lemma rq_event_odd (τ : ℝ) (C : ℕ → ℝ) (D : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k → k % 2 = 1 →
      ∃ g : ℝ, edgeVal N (specOf Sig) k + τ / 2 ≤ g ∧
        (∀ y ∈ (varrho N (specOf Sig)).support,
          y ≤ edgeVal N (specOf Sig) k ∨ g + τ / 2 ≤ y) ∧
        (∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → l ≠ k →
          edgeVal N (specOf Sig) l ≤ edgeVal N (specOf Sig) k - τ ∨
            g + τ / 2 ≤ edgeVal N (specOf Sig) l) ∧
        HighProbAt N D {ω | eigCount (QN Sig (X ω)) g = edgeD N (specOf Sig) k} := by
  obtain ⟨N₁, h₁⟩ := prop_counting τ C τ D hτ hτ
  obtain ⟨N₂, h₂⟩ := gap_outside τ C (τ / 4) (τ / 2) D hτ (by positivity) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN Ω _ _ M Sig X k hm hk hodd => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : 0 < N := hN1
  obtain ⟨hda, hσpos, hM0, hS⟩ := rq_basic hm hτ
  have hσ := hda.nonneg
  have hak : τ ≤ edgeVal N (specOf Sig) k := hk.2.2.1
  by_cases hk1 : k = 1
  · subst hk1
    have hsupp : ∀ y ∈ (varrho N (specOf Sig)).support, y ≤ edgeVal N (specOf Sig) 1 := by
      intro y hy
      rcases rq_supp_odd hσ hN0 hS hk hτ hodd hy with h | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨edgeVal N (specOf Sig) 1 + τ / 2, le_rfl, fun y hy => Or.inl (hsupp y hy), ?_, ?_⟩
    · intro l hl1 hl2 hlk
      rcases rq_edge_dich_odd hσ hN0 hS hk hodd hl1 hl2 hlk with h | ⟨h, -⟩
      · exact Or.inl h
      · omega
    · have hev := h₂ N (le_of_max_le_right (le_of_max_le_left hN)) M Sig X hm
      refine rq_hp_mono hev fun ω hω => ?_
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h0 : edgeD N (specOf Sig) 1 = 0 := by simp [edgeD, cumCount]
      rw [h0]
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ hj => ?_)
      have hj' : edgeVal N (specOf Sig) 1 + τ / 2 ≤ specOf (QN Sig (X ω)) j := hj
      have hlt := hω j (by linarith)
      have hge : τ / 2 ≤ Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support :=
        rq_le_infDist ⟨_, rq_ak_mem_supp hσ hN0 hS hk hτ⟩ fun y hy => by
          have := hsupp y hy
          rw [abs_of_nonneg (by linarith)]
          linarith
      linarith
  · have hk3 : 3 ≤ k := by
      have := hk.1
      omega
    set kh := (k + 1) / 2 - 1 with hkh
    have hkh1 : 1 ≤ kh := by omega
    have hkhp : kh < numBands N (specOf Sig) := by have := hk.2.1; omega
    have e1 : 2 * kh = k - 1 := by omega
    have e2 : 2 * kh + 1 = k := by omega
    have hgap := rq_gap_odd hσ hN0 hS hk hk3
    have hgm : gapMid N (specOf Sig) kh =
        (edgeVal N (specOf Sig) (k - 1) + edgeVal N (specOf Sig) k) / 2 := by
      unfold gapMid
      rw [e2, e1]
    have hev := h₁ N (le_of_max_le_left (le_of_max_le_left hN)) M Sig X kh hm hkh1 hkhp
      (by rw [e1]; linarith) (by rw [e2, e1]; linarith)
    refine ⟨gapMid N (specOf Sig) kh, ?_, ?_, ?_, ?_⟩
    · rw [hgm]; linarith
    · intro y hy
      rcases rq_supp_odd hσ hN0 hS hk hτ hodd hy with h | ⟨-, h⟩
      · exact Or.inl h
      · right; rw [hgm]; linarith
    · intro l hl1 hl2 hlk
      rcases rq_edge_dich_odd hσ hN0 hS hk hodd hl1 hl2 hlk with h | ⟨-, h⟩
      · exact Or.inl h
      · right; rw [hgm]; linarith
    · have hd : edgeD N (specOf Sig) k = cumCount N (specOf Sig) kh := by
        simp [edgeD, hodd, hkh]
      rw [hd]
      exact hev

private lemma rq_event_even (τ : ℝ) (C : ℕ → ℝ) (D : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k → k % 2 = 0 →
      ∃ g : ℝ, τ / 2 ≤ g ∧ g + τ / 2 ≤ edgeVal N (specOf Sig) k ∧
        (∀ y ∈ (varrho N (specOf Sig)).support,
          edgeVal N (specOf Sig) k ≤ y ∨ y + τ / 2 ≤ g) ∧
        (∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → l ≠ k →
          edgeVal N (specOf Sig) k + τ ≤ edgeVal N (specOf Sig) l ∨
            edgeVal N (specOf Sig) l + τ / 2 ≤ g) ∧
        HighProbAt N D {ω | eigCount (QN Sig (X ω)) g =
          cumCount N (specOf Sig) ((k + 1) / 2)} := by
  obtain ⟨N₁, h₁⟩ := prop_counting τ C τ D hτ hτ
  obtain ⟨N₂, h₂⟩ := bottom_count τ C τ D hτ hτ
  refine ⟨max (max N₁ N₂) 1, fun N hN Ω _ _ M Sig X k hm hk hev => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : 0 < N := hN1
  obtain ⟨hda, hσpos, hM0, hS⟩ := rq_basic hm hτ
  have hσ := hda.nonneg
  have hak : τ ≤ edgeVal N (specOf Sig) k := hk.2.2.1
  have hk1 : 1 ≤ k := hk.1
  have hk2 : k ≤ 2 * numBands N (specOf Sig) := hk.2.1
  by_cases hkp : k < 2 * numBands N (specOf Sig)
  · set kh := (k + 1) / 2 with hkh
    have hkh1 : 1 ≤ kh := by omega
    have hkhp : kh < numBands N (specOf Sig) := by omega
    have e1 : 2 * kh = k := by omega
    have e2 : 2 * kh + 1 = k + 1 := by omega
    have hgap := rq_gap_even hσ hN0 hS hk hkp
    have hnn := rq_edgeVal_nonneg hda hN0 hS (k := k + 1) (by omega) (by omega)
    have hgm : gapMid N (specOf Sig) kh =
        (edgeVal N (specOf Sig) k + edgeVal N (specOf Sig) (k + 1)) / 2 := by
      unfold gapMid
      rw [e2, e1]
    have hevt := h₁ N (le_of_max_le_left (le_of_max_le_left hN)) M Sig X kh hm hkh1 hkhp
      (by rw [e1]; exact hak) (by rw [e2, e1]; linarith)
    refine ⟨gapMid N (specOf Sig) kh, ?_, ?_, ?_, ?_, hevt⟩
    · rw [hgm]; linarith
    · rw [hgm]; linarith
    · intro y hy
      rcases rq_supp_even hσ hN0 hS hk hev hy with h | ⟨-, h⟩ | h
      · exact Or.inl h
      · right; rw [hgm]; linarith
      · right; rw [hgm]; linarith
    · intro l hl1 hl2 hlk
      rcases rq_edge_dich_even hσ hN0 hS hk hl1 hl2 hlk with h | ⟨-, h⟩
      · exact Or.inl h
      · right; rw [hgm]; linarith
  · have hkp' : k = 2 * numBands N (specOf Sig) := by omega
    have hp1 : 1 ≤ numBands N (specOf Sig) := by omega
    have hevt := h₂ N (le_of_max_le_right (le_of_max_le_left hN)) M Sig X hm
      (by rw [← hkp']; exact hak)
    have hcum : cumCount N (specOf Sig) ((k + 1) / 2) = min M N := by
      have : (k + 1) / 2 = numBands N (specOf Sig) := by omega
      rw [this]
      exact rq_cumCount_top hda hσpos hN0 hM0 hp1
    rw [← hkp'] at hevt
    refine ⟨edgeVal N (specOf Sig) k / 2, by linarith, by linarith, ?_, ?_, ?_⟩
    · intro y hy
      rcases rq_supp_even hσ hN0 hS hk hev hy with h | ⟨h, -⟩ | h
      · exact Or.inl h
      · exact absurd h hkp
      · right; linarith
    · intro l hl1 hl2 hlk
      rcases rq_edge_dich_even hσ hN0 hS hk hl1 hl2 hlk with h | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd h hkp
    · rw [hcum]
      exact hevt

/-! ### The edge regime on the good event -/

private lemma rq_omega_odd {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hN2 : 2 ≤ N) (hS : (posVals σ).Nonempty)
    (hk : RegularEdge τ N σ k) (hodd : k % 2 = 1)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) (Q : Matrix (Fin N) (Fin N) ℝ) (g : ℝ)
    (hg1 : edgeVal N σ k + τ / 2 ≤ g)
    (hgs : ∀ y ∈ (varrho N σ).support, y ≤ edgeVal N σ k ∨ g + τ / 2 ≤ y)
    (ht₀ : (N : ℝ) ^ (-2 / 3 + δ) ≤ edgeR0 τ)
    (hnum : (l : ℝ) + (N : ℝ) ^ (δ / 2) ≤ 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) *
      ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ)))
    (hcnt : ∀ E ∈ Set.Icc (edgeVal N σ k - edgeTau' τ) (edgeVal N σ k + edgeTau' τ),
      |(eigCount Q E : ℝ) - nClass N σ E| ≤ (N : ℝ) ^ (δ / 2))
    (hgap : ∀ j, specOf Q j ∈ Set.Icc (edgeVal N σ k + (N : ℝ) ^ (-2 / 3 + δ)) g →
      Metric.infDist (specOf Q j) (varrho N σ).support < (N : ℝ) ^ (-2 / 3 + δ / 2))
    (hP : eigCount Q g = edgeD N σ k) :
    EdgeRegime N (edgeVal N σ k) (edgeD N σ k) l δ (edgeR0 τ) (edgeKc τ) Q := by
  have hr0 := rq_edgeR0_pos hτ
  have hr0b := rq_edgeR0_le_tau (τ := τ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have ht0pos : 0 ≤ (N : ℝ) ^ (-2 / 3 + δ) := (Real.rpow_pos_of_pos hNpos _).le
  have hlt : (N : ℝ) ^ (-2 / 3 + δ / 2) < (N : ℝ) ^ (-2 / 3 + δ) :=
    Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
  have hsupp : (varrho N σ).support.Nonempty := ⟨_, rq_ak_mem_supp hda.nonneg hN hS hk hτ⟩
  have hnone : ∀ j, specOf Q j ∉ Set.Icc (edgeVal N σ k + (N : ℝ) ^ (-2 / 3 + δ)) g := by
    intro j hj
    have h1 := hgap j hj
    have h2 : (N : ℝ) ^ (-2 / 3 + δ) ≤ Metric.infDist (specOf Q j) (varrho N σ).support := by
      refine rq_le_infDist hsupp fun y hy => ?_
      rcases hgs y hy with h | h
      · rw [abs_of_nonneg (by linarith [hj.1])]
        linarith [hj.1]
      · rw [abs_of_nonpos (by linarith [hj.2])]
        linarith [hj.2]
    linarith
  have hm₁ : eigCount Q (edgeVal N σ k + (N : ℝ) ^ (-2 / 3 + δ)) = edgeD N σ k := by
    rw [rq_eigCount_eq_of_gap Q hnone le_rfl (by linarith), hP]
  have hm₂ : eigCount Q (edgeVal N σ k + edgeR0 τ) = edgeD N σ k := by
    rw [rq_eigCount_eq_of_gap Q hnone (by linarith) (by linarith), hP]
  exact rq_det_odd hτ hda hN hk hodd l δ hδ Q ht₀ hnum hcnt hm₁ hm₂

private lemma rq_omega_even {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hτ : 0 < τ)
    (hda : DensityAssumptions τ N σ) (hN : 0 < N) (hN2 : 2 ≤ N) (hS : (posVals σ).Nonempty)
    (hk : RegularEdge τ N σ k) (hev : k % 2 = 0)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.IsHermitian) (g : ℝ)
    (hg1 : g + τ / 2 ≤ edgeVal N σ k)
    (hgs : ∀ y ∈ (varrho N σ).support, edgeVal N σ k ≤ y ∨ y + τ / 2 ≤ g)
    (ht₀ : (N : ℝ) ^ (-2 / 3 + δ) ≤ edgeR0 τ)
    (hnum : (l : ℝ) + (N : ℝ) ^ (δ / 2) ≤ 2 / (3 * Real.pi * Real.sqrt (edgeC2 τ)) *
      ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ)) ^ (3 / 2 : ℝ)))
    (hcnt : ∀ E ∈ Set.Icc (edgeVal N σ k - edgeTau' τ) (edgeVal N σ k + edgeTau' τ),
      |(eigCount Q E : ℝ) - nClass N σ E| ≤ (N : ℝ) ^ (δ / 2))
    (hgap : ∀ j, specOf Q j ∈ Set.Icc g (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ)) →
      Metric.infDist (specOf Q j) (varrho N σ).support < (N : ℝ) ^ (-2 / 3 + δ / 2))
    (hP : eigCount Q g = cumCount N σ ((k + 1) / 2)) :
    EdgeRegime N (-edgeVal N σ k) (N - cumCount N σ ((k + 1) / 2)) l δ (edgeR0 τ) (edgeKc τ)
      (-Q) := by
  have hr0 := rq_edgeR0_pos hτ
  have hr0b := rq_edgeR0_le_tau (τ := τ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have ht0pos : 0 ≤ (N : ℝ) ^ (-2 / 3 + δ) := (Real.rpow_pos_of_pos hNpos _).le
  have hlt : (N : ℝ) ^ (-2 / 3 + δ / 2) < (N : ℝ) ^ (-2 / 3 + δ) :=
    Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
  have hsupp : (varrho N σ).support.Nonempty := ⟨_, rq_ak_mem_supp hda.nonneg hN hS hk hτ⟩
  have hnone : ∀ j, specOf Q j ∉ Set.Icc g (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ)) := by
    intro j hj
    have h1 := hgap j hj
    have h2 : (N : ℝ) ^ (-2 / 3 + δ) ≤ Metric.infDist (specOf Q j) (varrho N σ).support := by
      refine rq_le_infDist hsupp fun y hy => ?_
      rcases hgs y hy with h | h
      · rw [abs_of_nonpos (by linarith [hj.2])]
        linarith [hj.2]
      · rw [abs_of_nonneg (by linarith [hj.1])]
        linarith [hj.1]
    linarith
  have hcN : cumCount N σ ((k + 1) / 2) ≤ N := by
    rw [← hP]
    unfold eigCount
    calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
      _ = N := by simp
  have hm₁ : rqGt Q (edgeVal N σ k - (N : ℝ) ^ (-2 / 3 + δ)) = cumCount N σ ((k + 1) / 2) := by
    rw [rq_gt_eq_of_gap Q hnone (by linarith) le_rfl, hP]
  have hm₂ : rqGt Q (edgeVal N σ k - edgeR0 τ) = cumCount N σ ((k + 1) / 2) := by
    rw [rq_gt_eq_of_gap Q hnone (by linarith) (by linarith), hP]
  exact rq_det_even hτ hda hN hk hev hcN l δ hδ Q hQ ht₀ hnum hcnt hm₁ hm₂

/-- The edge regime for `(-1)^{k+1} Q_N` at a regular edge `k` (from `count_edge`, `gap_window`,
`gap_outside`, `prop_counting`, `bottom_count`, `rhoDens_edge`). -/
theorem edgeRegime_Q (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (δ D : ℝ) (hτ : 0 < τ) (hδ : 0 < δ)
    (hδ1 : δ < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      HighProbAt N D {ω | EdgeRegime N (edgeSign k * edgeVal N (specOf Sig) k)
        (edgeD N (specOf Sig) k) l δ (edgeR0 τ) (edgeKc τ) (edgeSign k • QN Sig (X ω))} := by
  obtain ⟨N₅, hN₅3, hnumN⟩ := rq_numeric τ l δ hτ hδ hδ1
  obtain ⟨N₁, h₁⟩ := count_edge τ C (δ / 2) (D + 1) hτ (half_pos hδ)
  obtain ⟨N₂, h₂⟩ := gap_window τ C (δ / 2) (D + 1) (τ / 2) hτ (half_pos hδ) (by linarith)
    (half_pos hτ)
  obtain ⟨N₃, h₃⟩ := rq_event_odd τ C (D + 1) hτ
  obtain ⟨N₄, h₄⟩ := rq_event_even τ C (D + 1) hτ
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) N₅, fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hN5 : N₅ ≤ N := le_of_max_le_right hN
  have hNa : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hNb : max N₁ N₂ ≤ N := le_of_max_le_left hNa
  have hNc : max N₃ N₄ ≤ N := le_of_max_le_right hNa
  have hN1 : N₁ ≤ N := le_of_max_le_left hNb
  have hN2 : N₂ ≤ N := le_of_max_le_right hNb
  have hN3' : N₃ ≤ N := le_of_max_le_left hNc
  have hN4 : N₄ ≤ N := le_of_max_le_right hNc
  have hN3 : 3 ≤ N := hN₅3.trans hN5
  have hN0 : 0 < N := by omega
  obtain ⟨hda, hσpos, hM0, hS⟩ := rq_basic hm hτ
  obtain ⟨ht₀, hnum⟩ := hnumN N hN5
  have hce := h₁ N hN1 M Sig X k hm hk
  have hr0 := rq_edgeR0_pos hτ
  have hr0b := rq_edgeR0_le_tau (τ := τ)
  have hak : τ ≤ edgeVal N (specOf Sig) k := hk.2.2.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have ht0pos : 0 ≤ (N : ℝ) ^ (-2 / 3 + δ) := (Real.rpow_pos_of_pos hNpos _).le
  by_cases hodd : k % 2 = 1
  · obtain ⟨g, hg1, hgs, hge, hP⟩ := h₃ N hN3' M Sig X k hm hk hodd
    set W : Set ℝ := Set.Icc (edgeVal N (specOf Sig) k + (N : ℝ) ^ (-2 / 3 + δ)) g with hW
    have hWsub : W ⊆ Set.Ici (τ / 2) := fun w hw => by
      simp only [Set.mem_Ici]
      linarith [hw.1]
    have hreg : ∀ l', 1 ≤ l' → l' ≤ 2 * numBands N (specOf Sig) →
        Metric.infDist (edgeVal N (specOf Sig) l') W ≤ τ / 4 →
          RegularEdge (τ / 2) N (specOf Sig) l' := by
      intro l' hl1 hl2 hd
      by_cases hlk : l' = k
      · subst hlk; exact regularEdge_mono hk (by linarith)
      · exfalso
        have hne : W.Nonempty := ⟨_, le_rfl, by linarith⟩
        have := rq_le_infDist hne (t := τ / 2) (w := edgeVal N (specOf Sig) l') fun w hw => by
          rcases hge l' hl1 hl2 hlk with h | h
          · rw [abs_of_nonpos (by linarith [hw.1])]
            linarith [hw.1]
          · rw [abs_of_nonneg (by linarith [hw.2])]
            linarith [hw.2]
        linarith
    have hgw := h₂ N hN2 M Sig X W hm hWsub hreg
    refine rq_hp_mono (rq_hp_inter3 hN3 hce hgw hP) ?_
    rintro ω ⟨⟨hc, hg⟩, hp⟩
    have hs : edgeSign k = 1 := by simp [edgeSign, hodd]
    change EdgeRegime N (edgeSign k * edgeVal N (specOf Sig) k) (edgeD N (specOf Sig) k) l δ
      (edgeR0 τ) (edgeKc τ) (edgeSign k • QN Sig (X ω))
    rw [hs, one_mul, one_smul]
    exact rq_omega_odd hτ hda hN0 (by omega) hS hk hodd l δ hδ _ g hg1 hgs ht₀ hnum hc hg hp
  · have hev : k % 2 = 0 := by omega
    obtain ⟨g, hg0, hg1, hgs, hge, hP⟩ := h₄ N hN4 M Sig X k hm hk hev
    set W : Set ℝ := Set.Icc g (edgeVal N (specOf Sig) k - (N : ℝ) ^ (-2 / 3 + δ)) with hW
    have hWsub : W ⊆ Set.Ici (τ / 2) := fun w hw => by
      simp only [Set.mem_Ici]
      linarith [hw.1]
    have hreg : ∀ l', 1 ≤ l' → l' ≤ 2 * numBands N (specOf Sig) →
        Metric.infDist (edgeVal N (specOf Sig) l') W ≤ τ / 4 →
          RegularEdge (τ / 2) N (specOf Sig) l' := by
      intro l' hl1 hl2 hd
      by_cases hlk : l' = k
      · subst hlk; exact regularEdge_mono hk (by linarith)
      · exfalso
        have hne : W.Nonempty := ⟨_, le_rfl, by linarith⟩
        have := rq_le_infDist hne (t := τ / 2) (w := edgeVal N (specOf Sig) l') fun w hw => by
          rcases hge l' hl1 hl2 hlk with h | h
          · rw [abs_of_nonneg (by linarith [hw.2])]
            linarith [hw.2]
          · rw [abs_of_nonpos (by linarith [hw.1])]
            linarith [hw.1]
        linarith
    have hgw := h₂ N hN2 M Sig X W hm hWsub hreg
    refine rq_hp_mono (rq_hp_inter3 hN3 hce hgw hP) ?_
    rintro ω ⟨⟨hc, hg⟩, hp⟩
    have hs : edgeSign k = -1 := by simp [edgeSign, hodd]
    have hd : edgeD N (specOf Sig) k = N - cumCount N (specOf Sig) ((k + 1) / 2) := by
      simp [edgeD, hodd]
    change EdgeRegime N (edgeSign k * edgeVal N (specOf Sig) k) (edgeD N (specOf Sig) k) l δ
      (edgeR0 τ) (edgeKc τ) (edgeSign k • QN Sig (X ω))
    rw [hs, hd, neg_one_mul, neg_one_smul]
    exact rq_omega_even hτ hda hN0 (by omega) hS hk hev l δ hδ _
      (rq_QN_isHermitian hm.sigma.posDef (X ω)) g hg1 hgs ht₀ hnum hc hg hp

/-- The edge-regime hypotheses of `edge_reduction` at the Marchenko–Pastur point, for the
Rademacher and the Gaussian ensemble, with every hypothesis of `edgeRegime_Q` discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    HighProbAt (2 * n) 1 {ω | EdgeRegime (2 * n)
      (edgeSign 1 * edgeVal (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1)
      (edgeD (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) 1 ((1 / 200) / (8 * (1 + 1)))
      (edgeR0 (1 / 5)) (edgeKc (1 / 5)) (edgeSign 1 • QN (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω))} ∧
    HighProbAt (2 * n) 1 {ω | EdgeRegime (2 * n)
      (edgeSign 1 * edgeVal (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1)
      (edgeD (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) 1 ((1 / 200) / (8 * (1 + 1)))
      (edgeR0 (1 / 5)) (edgeKc (1 / 5))
      (edgeSign 1 • QN (1 : Matrix (Fin n) (Fin n) ℝ) (gaussX n (2 * n) ω))} := by
  obtain ⟨N₁, h₁⟩ := edgeRegime_Q (1 / 5) (fun _ => 1) 1 ((1 / 200) / (8 * (1 + 1))) 1
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨N₂, h₂⟩ := edgeRegime_Q (1 / 5) gaussMoment 1 ((1 / 200) / (8 * (1 + 1))) 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max N₁ N₂, fun n hn hN => ?_⟩
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  have hm := isModel_radXn hn
  have hg : IsModel (1 / 5) gaussMoment n (2 * n) (1 : Matrix (Fin n) (Fin n) ℝ)
      (gaussX n (2 * n)) := isModel_gaussX (by omega) hm.ratio_ge hm.ratio_le hm.sigma
  exact ⟨h₁ (2 * n) (le_of_max_le_left hN) n 1 (radXn n) 1 hm hk,
    h₂ (2 * n) (le_of_max_le_right hN) n 1 (gaussX n (2 * n)) 1 hg hk⟩

/-- The window radius and the local-count constant are positive at `τ = 1/5`. -/
example : 0 < edgeR0 (1 / 5) ∧ 0 < edgeKc (1 / 5) := by
  refine ⟨rq_edgeR0_pos (by norm_num), ?_⟩
  have h := edgec2_pos (show (0 : ℝ) < 1 / 5 by norm_num)
  unfold edgeKc
  positivity

end Anisotropic
