import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.Ordering
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.GeneralT.Edges
import Anisotropic.GeneralT.Limit
import Anisotropic.GeneralT.Masses
import Anisotropic.GeneralT.Model
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Local
import Anisotropic.Rigidity.Main
import Anisotropic.Rigidity.MinMax

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorems 3.12, 3.14 (iii) and 3.15 (iii) for a general `T` -/

/-- `λ_{k,i}` for a general `T`: the eigenvalues of `Xᵀ Tᵀ T X` (whose nonzero eigenvalues are
those of `Q = T X Xᵀ Tᵀ`), relabelled with the band counts of `Σ = T Tᵀ`. -/
def lamBandT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ)
    (k i : ℕ) : ℝ :=
  sortedEig (QN (Tᵀ * T) Xm) (cumCount N (specOf (T * Tᵀ)) (k - 1) + i)

/-! ## Auxiliary facts -/

section RigidityTAux

/-- `τ ≤ 1` under Assumption 2.1 for a general `T`. -/
private lemma rigT_tau_le_one {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hm : IsModelT τ C M K N T X) : τ ≤ 1 := by
  have h1 := hm.ratio_ge
  have h2 := hm.ratio_le
  by_contra hc
  push Not at hc
  have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
  linarith

/-- `τ'(τ) ≤ τ/2` for `0 < τ ≤ 1`. -/
private lemma rigT_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  rw [heq]
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  nlinarith

/-- `0 < τ'_gen(τ) ≤ τ/32` for `0 < τ ≤ 1`. -/
private lemma rigT_tauGen {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < tauGen τ ∧ tauGen τ ≤ τ / 32 := by
  have he := tauE_pos hτ
  have he4 : tauE τ ≤ τ / 4 := min_le_right _ _
  have h := rigT_edgeTau'_le he (by linarith)
  refine ⟨by unfold tauGen; have := edgeTau'_pos he; positivity, ?_⟩
  unfold tauGen
  linarith

/-- Weyl's inequality for the sorted eigenvalues, one side: `λ_j(A) ≤ λ_j(B) + ‖A − B‖`. -/
private lemma rigT_sortedEig_le {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (j : ℕ) : sortedEig A j ≤ sortedEig B j + ‖A - B‖ := by
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · have h1 : sortedEig A j - ‖A - B‖ ≤ sortedEig B j := by
      rw [sortedEig_ge_iff hB hj.1 hj.2]
      have hw := eigCount_weyl hA hB le_rfl (sortedEig A j - ‖A - B‖)
      rw [sub_add_cancel] at hw
      exact le_trans ((sortedEig_ge_iff hA hj.1 hj.2 _).1 le_rfl) hw
    linarith
  · have hA0 : sortedEig A j = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    have hB0 : sortedEig B j = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    rw [hA0, hB0]
    simp

/-- Weyl's inequality for the sorted eigenvalues: `|λ_j(A) − λ_j(B)| ≤ ‖A − B‖`. -/
private lemma rigT_abs_sortedEig_sub {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : ℕ) :
    |sortedEig A j - sortedEig B j| ≤ ‖A - B‖ := by
  rw [abs_le]
  have h1 := rigT_sortedEig_le hA hB j
  have h2 := rigT_sortedEig_le hB hA j
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- `Q_N = Xᵀ S X` is symmetric for symmetric `S`. -/
private lemma rigT_QN_herm {K : ℕ} {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.IsHermitian)
    (Xm : Matrix (Fin K) (Fin N) ℝ) : (QN S Xm).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Xm hS
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- `Tᵀ T` is symmetric. -/
private lemma rigT_TtT_herm {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) : (Tᵀ * T).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian

/-- The projection `P₀` on `ker S`, by spectral calculus. -/
private def rigTP0 {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) S

/-- `Ŝ + κ P₀ = Ŝ + κ • P₀` for `Ŝ = Tᵀ T`. -/
private lemma rigT_regS_eq {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) :
    regS κ (Tᵀ * T) = Tᵀ * T + κ • rigTP0 (Tᵀ * T) := by
  have hS : (Tᵀ * T).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (Tᵀ * T)) := fun f => by
    rw [hS.1.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  unfold regS rigTP0
  have h1 : cfc (fun x : ℝ => if 0 < x then x else κ) (Tᵀ * T) =
      cfc (fun x : ℝ => (if 0 < x then x else 0) + κ * (if 0 < x then (0 : ℝ) else 1))
        (Tᵀ * T) :=
    cfc_congr fun x _ => by split_ifs <;> ring
  have hid : cfc (id : ℝ → ℝ) (Tᵀ * T) = Tᵀ * T := cfc_id ℝ (Tᵀ * T) hS.1
  rw [h1, cfc_add (a := Tᵀ * T) (fun x : ℝ => if 0 < x then x else 0)
      (fun x : ℝ => κ * (if 0 < x then (0 : ℝ) else 1)) (hcont _) (hcont _),
    cfc_const_mul κ (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) (Tᵀ * T) (hcont _)]
  congr 1
  rw [cfc_congr (g := id) fun x hx => ?_]
  · exact hid
  · have : 0 ≤ x := by
      rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hS.eigenvalues_nonneg i
    split_ifs with h
    · rfl
    · simp only [id]
      linarith

/-- `‖Q_N(Ŝ + κ P₀) − Q_N(Ŝ)‖ → 0` as `κ ↓ 0`. -/
private lemma rigT_norm_QN_regS {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ‖QN (regS κ (Tᵀ * T)) Xm - QN (Tᵀ * T) Xm‖ < δ := by
  set B := Xmᵀ * rigTP0 (Tᵀ * T) * Xm with hB
  have heq : ∀ κ : ℝ, QN (regS κ (Tᵀ * T)) Xm - QN (Tᵀ * T) Xm = κ • B := fun κ => by
    unfold QN
    rw [rigT_regS_eq, Matrix.mul_add, Matrix.add_mul, hB, Matrix.mul_smul, Matrix.smul_mul]
    abel
  have hpos : 0 < δ / (‖B‖ + 1) := by positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hpos)] with κ hκ
  rw [heq, norm_smul]
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hκ
  rw [Real.norm_eq_abs]
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  calc |κ| * ‖B‖ ≤ δ / (‖B‖ + 1) * ‖B‖ := mul_le_mul_of_nonneg_right hκ.le hB0
    _ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- The eigenvalues of `Ŝ + κ P₀` are nonnegative for `κ > 0`. -/
private lemma rigT_specOf_regS_nonneg {K : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (T : Matrix (Fin M) (Fin K) ℝ) : ∀ i, 0 ≤ specOf (regS κ (Tᵀ * T)) i := fun i => by
  have h := regS_posDef hκ T
  rw [specOf_eq h.isHermitian]
  exact (h.eigenvalues_pos i).le

/-- (phi_bounded) and (Sigma_gap) give `N > 0` and some positive `σ i`. -/
private lemma rigT_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
  refine ⟨hN, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
    have : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at this
    simp at this
  have hgap := h.Sigma_gap
  have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul, hall]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
    simp [Set.indicator_of_mem h0]
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [happ, hM', ENNReal.toReal_one] at hgap
  linarith

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rigT_varrho_apply (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `ρ` is continuous on `(0, ∞)`. -/
private lemma rigT_continuousOn_rhoDens (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => mExt N σ x) (Set.Ioi 0) :=
    (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩)
  exact (Complex.continuous_im.comp_continuousOn h1).div_const _

/-- `n` is nonincreasing. -/
private lemma rigT_nClass_anti {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    Antitone (nClass N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ici_subset_Ici.mpr hxy))) (Nat.cast_nonneg N)

/-- `n ≤ N`. -/
private lemma rigT_nClass_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E : ℝ) :
    nClass N σ E ≤ N := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  unfold nClass
  have h1 : (varrho N σ (Set.Ici E)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) N)
  linarith

private lemma rigT_nClass_lip {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      nClass N σ x - nClass N σ y ≤ K * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    ((rigT_continuousOn_rhoDens (N := N) σ hσ).mono hsub)
  refine ⟨N * max B 0, by positivity, fun x hx y hy hxy => ?_⟩
  have hsplit : varrho N σ (Set.Ici x) = varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  have hIco : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (max B 0 * (y - x)) := by
    have hsub' : Set.Ico x y ⊆ Set.Icc a b := fun z hz => ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩
    rw [rigT_varrho_apply σ measurableSet_Ico (hsub'.trans hsub)]
    calc ∫⁻ z in Set.Ico x y, ENNReal.ofReal (rhoDens N σ z)
        ≤ ∫⁻ z in Set.Ico x y, ENNReal.ofReal (max B 0) := by
          refine setLIntegral_mono' measurableSet_Ico fun z hz => ?_
          exact ENNReal.ofReal_le_ofReal
            ((hB ⟨z, hsub' hz, rfl⟩).trans (le_max_left _ _))
      _ = ENNReal.ofReal (max B 0 * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (le_max_right _ _)]
  have hc : 0 ≤ max B 0 * (y - x) := mul_nonneg (le_max_right _ _) (by linarith)
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ max B 0 * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIco
    rwa [ENNReal.toReal_ofReal hc] at this
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) N)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith

/-- `n` is continuous on `(0, ∞)`. -/
private lemma rigT_nClass_continuousOn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    ContinuousOn (nClass N σ) (Set.Ioi 0) := by
  intro E0 hE0
  have hE0' : (0 : ℝ) < E0 := hE0
  have hmem : Set.Icc (E0 / 2) (2 * E0) ∈ 𝓝 E0 :=
    Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨K, hK0, hK⟩ := rigT_nClass_lip (σ := σ) hσ hN (a := E0 / 2) (b := 2 * E0)
    (by linarith)
  have hanti := rigT_nClass_anti (σ := σ) hσ hN
  have hlip : LipschitzOnWith K.toNNReal (nClass N σ) (Set.Icc (E0 / 2) (2 * E0)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total x y with hxy | hxy
    · have h1 := hK x hx y hy hxy
      have h2 := hanti hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1 := hK y hy x hx hxy
      have h2 := hanti hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact (hlip.continuousOn.continuousAt hmem).continuousWithinAt

/-- `d_k` is nondecreasing in `k`. -/
private lemma rigT_cumCount_mono (σ : Fin M → ℝ) {a b : ℕ} (hab : a ≤ b) :
    cumCount N σ a ≤ cumCount N σ b := by
  unfold cumCount
  refine Nat.floor_le_floor ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hab)
    (fun l _ _ => by unfold bandCount; positivity)

/-- A positive classical location `γ_j` has `j ≤ N`. -/
private lemma rigT_index_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {j : ℕ}
    (hj : 0 < gammaLoc N σ j) : j ≤ N := by
  have h1 := nClass_gammaLoc_of_pos hσ hN hj
  have h2 := rigT_nClass_le hσ hN (gammaLoc N σ j)
  have : (j : ℝ) < N + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- `γ_{k,i} ∈ [a_{2k}, a_{2k−1}]` for `1 ≤ i ≤ N_k` when `γ_{k,i} > 0` (`σ ≥ 0`). -/
private lemma rigT_band_mem {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k i : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hi : 1 ≤ i) (hiN : i ≤ bandNat N σ k)
    (hγ : 0 < gammaBand N σ k i) :
    edgeVal N σ (2 * k) ≤ gammaBand N σ k i ∧ gammaBand N σ k i ≤ edgeVal N σ (2 * k - 1) := by
  obtain ⟨hN, -⟩ := rigT_facts h
  have hσ := h.nonneg
  have hanti := rigT_nClass_anti hσ hN
  have hn := nClass_gammaLoc_of_pos hσ hN hγ
  obtain ⟨he1, he2⟩ := nClass_edgeVal h hk hkp
  obtain ⟨-, -, hc3⟩ := cumCount_spec h hk hkp
  have hg : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  rw [hg] at hγ ⊢
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hjk : ((cumCount N σ (k - 1) + i : ℕ) : ℝ) ≤ cumCount N σ k := by
    exact_mod_cast (by omega : cumCount N σ (k - 1) + i ≤ cumCount N σ k)
  push_cast at hn hjk
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    have := hanti hlt.le
    rw [hn, he2 (hγ.trans hlt)] at this
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have := hanti hlt.le
    rw [hn, he1] at this
    linarith

/-- The bound of (rigidity) decreases when `min(i, N_k + 1 − i)` increases. -/
private lemma rigT_rigBound_mono {N Nk Nk' i i' : ℕ} {ε : ℝ}
    (h1 : 1 ≤ min i (Nk + 1 - i)) (h : min i (Nk + 1 - i) ≤ min i' (Nk' + 1 - i')) :
    rigBound N Nk' i' ε ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hp : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have hle : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ ((min i' (Nk' + 1 - i') : ℕ) : ℝ) := by
    exact_mod_cast h
  have hr := Real.rpow_le_rpow_of_nonpos hp hle (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0' : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr h0) h0'

/-- `N^ε N⁻¹ ≤ N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}` when `1 ≤ i ∧ (N_k + 1 − i) ≤ N`. -/
private lemma rigT_bulk_le_rigBound {N Nk i : ℕ} {ε : ℝ} (h1 : 1 ≤ min i (Nk + 1 - i))
    (hN : min i (Nk + 1 - i) ≤ N) : (N : ℝ) ^ ε * (N : ℝ)⁻¹ ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hp : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have hNr : (0 : ℝ) < N := hp.trans_le (by exact_mod_cast hN)
  have hle : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have hr := Real.rpow_le_rpow_of_nonpos hp hle (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
  have hinv : (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hNr, ← Real.rpow_neg_one]
    norm_num
  rw [hinv, ← mul_assoc]
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0' : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr h0) h0'

end RigidityTAux

/-- Theorem 3.14 (iii) (`thm:edge`) for a general `T`, window `τ'(τ) = tauGen τ`. -/
theorem rigidity_edge_gen (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      HighProbAt N D {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2) →
        gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i ∈
          Set.Icc (edgeVal N (specOf (T * Tᵀ)) k - tauGen τ)
            (edgeVal N (specOf (T * Tᵀ)) k + tauGen τ) →
        |lamBandT T (X ω) ((k + 1) / 2) i - gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i| ≤
          rigBound N (bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2)) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X k hm _ => absurd (rigT_tau_le_one hm) hτ1⟩
  have hτe : 0 < tauE τ := tauE_pos hτ
  have hτe3 : tauE τ ≤ τ ^ 3 := min_le_left _ _
  obtain ⟨hgen0, hgenτ⟩ := rigT_tauGen hτ hτ1
  obtain ⟨N₀, h₀⟩ := rigidity_edge (tauE τ) C ε D hτe hε
  refine ⟨max N₀ 1, fun N hN Ω _ _ M K T X k hm hreg => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hNpos : 0 < N := hN1
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  set e := edgeTau' (tauE τ) with he
  have he0 : 0 < e := edgeTau'_pos hτe
  have hgen : tauGen τ = e / 4 := rfl
  have hδa : deltaA τ ≤ e / 16 := min_le_left _ _
  -- the admissible edges `l'` of `Ŝ + κ P₀` and the event of `rigidity_edge` there
  set P : ℝ → ℕ → Prop := fun κ l' =>
    RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N σ k| ≤ deltaA τ ∧
      cumCount N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2 - 1) ≤ cumCount N σ ((k + 1) / 2 - 1) ∧
      cumCount N σ ((k + 1) / 2) ≤ cumCount N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2)
    with hP
  set Ev : ℝ → ℕ → Set Ω := fun κ l' =>
    {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2) →
      gammaBand N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2) i ∈
        Set.Icc (edgeVal N (specOf (regS κ (Tᵀ * T))) l' - e / 2)
          (edgeVal N (specOf (regS κ (Tᵀ * T))) l' + e / 2) →
      |lamBand (regS κ (Tᵀ * T)) (X ω) ((l' + 1) / 2) i -
          gammaBand N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2) i| ≤
        rigBound N (bandNat N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2)) i ε} with hEv
  have hregκ := regularEdge_regS hτ (show τ / 2 ≤ τ by linarith) hN1 hda hm.ratioK_le hreg
  have hκev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT (by positivity)) fun κ hκ => hκ
  unfold HighProbAt
  refine measure_le_of_eventually (l := 𝓝[>] (0 : ℝ))
    (Bi := fun κ => {ω | ∀ l', P κ l' → ω ∉ Ev κ l'}) ?_ ?_
  · intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨i, hi1, hiN, hwin, hbad⟩ := hω
    rw [not_le] at hbad
    obtain ⟨hk1, hk2, hak, -, -⟩ := hreg
    set kh := (k + 1) / 2 with hkh
    have hkh1 : 1 ≤ kh := by omega
    have hkhp : kh ≤ numBands N σ := by omega
    obtain ⟨-, -, hc3⟩ := cumCount_spec hda hkh1 hkhp
    set j := cumCount N σ (kh - 1) + i with hj
    have hγdef : gammaBand N σ kh i = gammaLoc N σ j := rfl
    have hlamdef : lamBandT T (X ω) kh i = sortedEig (QN (Tᵀ * T) (X ω)) j := rfl
    rw [hγdef] at hwin hbad
    rw [hlamdef] at hbad
    set γ := gammaLoc N σ j with hγ
    set lam := sortedEig (QN (Tᵀ * T) (X ω)) j with hlam
    set β := rigBound N (bandNat N σ kh) i ε with hβ
    have hγpos : 0 < γ := by
      have := hwin.1
      linarith
    set g := |lam - γ| - β with hg
    have hg0 : 0 < g := by rw [hg]; linarith
    have hγlim := tendsto_gammaLoc_regS hN1 T hγpos
    have hγev : ∀ᶠ κ in 𝓝[>] (0 : ℝ),
        dist (gammaLoc N (specOf (regS κ (Tᵀ * T))) j) γ < min (e / 8) (g / 2) :=
      (Metric.tendsto_nhds.1 hγlim) _ (by positivity)
    have hlamev := rigT_norm_QN_regS T (X ω) (show 0 < g / 2 by positivity)
    filter_upwards [hκev, hγev, hlamev] with κ hκ hγκ hlamκ
    intro l' hPl' hω'
    obtain ⟨hregl', hal', hcl1, hcl2⟩ := hPl'
    rw [← hkh] at hcl1 hcl2
    have hmκ : IsModel (tauE τ) C K N (regS κ (Tᵀ * T)) X :=
      (isModel_regS hτ hm hκ.1 hκ.2).mono hτe hτe3
    have hdaκ : DensityAssumptions (tauE τ) N (specOf (regS κ (Tᵀ * T))) :=
      hmκ.diagModel_specOf.densityAssumptions hτe
    obtain ⟨hl1, hl2, -, -, -⟩ := hregl'
    set σκ := specOf (regS κ (Tᵀ * T)) with hσκ
    set kh' := (l' + 1) / 2 with hkh'
    have hkh'1 : 1 ≤ kh' := by omega
    have hkh'p : kh' ≤ numBands N σκ := by omega
    obtain ⟨-, -, hc3'⟩ := cumCount_spec hdaκ hkh'1 hkh'p
    set i' := j - cumCount N σκ (kh' - 1) with hi'
    have hji : cumCount N σκ (kh' - 1) + i' = j := by omega
    have hi'1 : 1 ≤ i' := by omega
    have hi'N : i' ≤ bandNat N σκ kh' := by omega
    have hγκdef : gammaBand N σκ kh' i' = gammaLoc N σκ j := by
      unfold gammaBand; rw [hji]
    have hlamκdef : lamBand (regS κ (Tᵀ * T)) (X ω) kh' i' =
        sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j := by
      unfold lamBand; rw [← hσκ, hji]
    have hγκ' : |gammaLoc N σκ j - γ| < min (e / 8) (g / 2) := by
      rw [← Real.dist_eq]; exact hγκ
    have hγκ1 : |gammaLoc N σκ j - γ| < e / 8 := hγκ'.trans_le (min_le_left _ _)
    have hγκ2 : |gammaLoc N σκ j - γ| < g / 2 := hγκ'.trans_le (min_le_right _ _)
    have hwin' : gammaBand N σκ kh' i' ∈ Set.Icc (edgeVal N σκ l' - e / 2)
        (edgeVal N σκ l' + e / 2) := by
      rw [hγκdef]
      have h1 := abs_le.1 hγκ1.le
      have h2 := abs_le.1 hal'
      have h3 := hwin
      rw [hgen] at h3
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    have hres := hω' i' hi'1 hi'N hwin'
    rw [hγκdef, hlamκdef] at hres
    have hβ' : rigBound N (bandNat N σκ kh') i' ε ≤ β :=
      rigT_rigBound_mono (by omega) (min_le_min (by omega) (by omega))
    have hlam := rigT_abs_sortedEig_sub (rigT_QN_herm (regS_posDef hκ.1 T).isHermitian (X ω))
      (rigT_QN_herm (rigT_TtT_herm T) (X ω)) j
    have hlam' : |sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j - lam| < g / 2 := hlam.trans_lt hlamκ
    have htri : |lam - γ| ≤ |sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j - gammaLoc N σκ j| +
        |sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j - lam| + |gammaLoc N σκ j - γ| := by
      have h1 := abs_sub_le lam (sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j) γ
      have h2 := abs_sub_le (sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j) (gammaLoc N σκ j) γ
      have h3 := abs_sub_comm lam (sortedEig (QN (regS κ (Tᵀ * T)) (X ω)) j)
      linarith
    linarith
  · filter_upwards [hregκ, hκev] with κ hl hκ
    obtain ⟨l', hl'⟩ := hl
    have hmκ : IsModel (tauE τ) C K N (regS κ (Tᵀ * T)) X :=
      (isModel_regS hτ hm hκ.1 hκ.2).mono hτe hτe3
    have hpr := h₀ N hN0 K (regS κ (Tᵀ * T)) X l' hmκ hl'.1
    refine le_trans (measure_mono ?_) hpr
    intro ω hω
    exact hω l' hl'

/-- Theorem 3.15 (iii) (`thm:bulk`) for a general `T`. -/
theorem rigidity_bulk_gen (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularBulk c N (specOf (T * Tᵀ)) k →
      (RegularEdge τ N (specOf (T * Tᵀ)) (2 * k) ∨
        RegularEdge τ N (specOf (T * Tᵀ)) (2 * k - 1)) →
      HighProbAt N D {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k →
        gammaBand N (specOf (T * Tᵀ)) k i ∈
          Set.Icc (edgeVal N (specOf (T * Tᵀ)) (2 * k) + τ')
            (edgeVal N (specOf (T * Tᵀ)) (2 * k - 1) - τ') →
        |lamBandT T (X ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
          (N : ℝ) ^ ε * (N : ℝ)⁻¹} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X k hm _ _ => absurd (rigT_tau_le_one hm) hτ1⟩
  by_cases hc : 0 < c (τ' / 2) ∧ 0 < c (τ' / 8)
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X k _ hb _ =>
      absurd ⟨(hb.2.2 (τ' / 2) (by positivity)).1, (hb.2.2 (τ' / 8) (by positivity)).1⟩ hc⟩
  obtain ⟨hc2, hc8⟩ := hc
  -- the constants, fixed before `N₀`
  set τ₄ := min (τ ^ 3) (min (τ' / 4) (τ ^ 2 / 4)) with hτ₄
  have hτ₄0 : 0 < τ₄ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hτ₄3 : τ₄ ≤ τ ^ 3 := min_le_left _ _
  have hτ₄' : τ₄ ≤ τ' / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₄2 : τ₄ ≤ τ ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set c₁ := 2 * c (τ' / 8) * Real.arctan (τ' / 8) with hc₁
  have hc₁0 : 0 < c₁ := by
    have := Real.arctan_pos.2 (show 0 < τ' / 8 by positivity)
    positivity
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  obtain ⟨N₁, h₁⟩ := count_loc τ₄ (c₁ / 2) C (ε₁ / 2) D hτ₄0 (by positivity) (by positivity)
  set c₀ := c (τ' / 2) with hc₀
  have hev : ∀ᶠ n : ℕ in atTop, N₁ ≤ n ∧ 1 ≤ n ∧ 2 / c₀ ≤ (n : ℝ) ^ (ε₁ / 2) ∧
      4 / (c₀ * τ') ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    refine (eventually_ge_atTop N₁).and ((eventually_ge_atTop 1).and
      (Filter.Eventually.and ?_ ?_))
    · exact ((tendsto_rpow_atTop (by positivity)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    · exact ((tendsto_rpow_atTop (by norm_num)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN Ω _ _ M K T X k hm hb _ => ?_⟩
  obtain ⟨hNN₁, hN1, hs1, hs2⟩ := hN₀ N hN
  have hNpos : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  have hσ : ∀ i, 0 ≤ σ i := hda.nonneg
  obtain ⟨-, hS⟩ := rigT_facts hda
  obtain ⟨hk1, hkp, hbr⟩ := hb
  have ha2 := edgeVal_mem_Icc N σ hσ hNpos hS hτ hda.phi_lower hda.phi_upper hda.bound_Sigma
    (k := 2 * k) (by omega) (by omega)
  have ha1 := edgeVal_mem_Icc N σ hσ hNpos hS hτ hda.phi_lower hda.phi_upper hda.bound_Sigma
    (k := 2 * k - 1) (by omega) (by omega)
  set a₂ := edgeVal N σ (2 * k) with ha₂
  set a₁ := edgeVal N σ (2 * k - 1) with ha₁
  -- the final numerics
  set s : ℝ := (N : ℝ) ^ (ε₁ / 2) with hs
  have hs0 : 1 ≤ s := Real.one_le_rpow hN1r (by positivity)
  have hfin1 : (s + 1) / (c₀ * N) ≤ τ' / 2 := by
    rw [div_le_iff₀ (by positivity)]
    set r : ℝ := (N : ℝ) ^ (1 / 2 : ℝ) with hr
    have hrr : r * r = N := by
      rw [hr, ← Real.rpow_add hNr]
      norm_num
    have hsr : s ≤ r := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have h4 : 4 ≤ c₀ * τ' * r := by
      have := (div_le_iff₀ (by positivity)).1 hs2
      linarith
    have hr0 : 0 ≤ r := by positivity
    nlinarith
  have hfin2 : (s + 1) / (c₀ * N) ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
    have hss : s * s ≤ (N : ℝ) ^ ε := by
      rw [hs, ← Real.rpow_add hNr]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have h2 : 2 ≤ c₀ * s := by
      have := (div_le_iff₀ hc2).1 hs1
      linarith
    have key : s + 1 ≤ c₀ * (N : ℝ) ^ ε := by nlinarith
    calc (s + 1) / (c₀ * N) ≤ c₀ * (N : ℝ) ^ ε / (c₀ * N) :=
          div_le_div_of_nonneg_right key (by positivity)
      _ = (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by field_simp
  have hρ2 : ∀ E ∈ Set.Icc (a₂ + τ' / 2) (a₁ - τ' / 2), c₀ ≤ rhoDens N σ E :=
    (hbr (τ' / 2) (by positivity)).2
  have hρ8 : ∀ E ∈ Set.Icc (a₂ + τ' / 8) (a₁ - τ' / 8), c (τ' / 8) ≤ rhoDens N σ E :=
    (hbr (τ' / 8) (by positivity)).2
  -- the count for `T` on `[a_{2k} + τ'/2, a_{2k−1} − τ'/2]` gives the event (bulk inversion)
  set GT : Set Ω := {ω | ∀ E ∈ Set.Icc (a₂ + τ' / 2) (a₁ - τ' / 2),
    |(eigCount (QN (Tᵀ * T) (X ω)) E : ℝ) - nClass N σ E| ≤ s} with hGT
  have hsub : GT ⊆ {ω | ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
      gammaBand N σ k i ∈ Set.Icc (a₂ + τ') (a₁ - τ') →
      |lamBandT T (X ω) k i - gammaBand N σ k i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹} := by
    intro ω hω i _ _ hγ
    have h := bulk_inversion hσ hNpos (rigT_QN_herm (rigT_TtT_herm T) (X ω)) (k := k) (t := τ')
      (c₀ := c₀) (s := s) hτ' hc2 (by linarith) hρ2 hω hfin1 hγ ha2.1
    exact h.trans hfin2
  unfold HighProbAt
  refine le_trans (measure_mono (Set.compl_subset_compl.2 hsub)) ?_
  -- the window `[a_{2k} + τ'/4, a_{2k−1} − τ'/4]` for `Ŝ + κ P₀`
  set E₁ := a₂ + τ' / 4 with hE₁def
  set E₂ := a₁ - τ' / 4 with hE₂def
  have hE₁ : τ₄ ≤ E₁ := by linarith [ha2.1]
  have hE₂ : E₂ ≤ τ₄⁻¹ := by
    have hinv : (τ ^ 2 / 4)⁻¹ ≤ τ₄⁻¹ := inv_anti₀ hτ₄0 hτ₄2
    have ht1 : 1 ≤ τ⁻¹ := one_le_inv₀ hτ |>.2 hτ1
    have heq : (τ ^ 2 / 4)⁻¹ = 4 * (τ⁻¹ * τ⁻¹) := by field_simp
    have hb : 2 * τ⁻¹ * (1 + τ⁻¹) ≤ (τ ^ 2 / 4)⁻¹ := by rw [heq]; nlinarith
    linarith [ha1.2]
  -- `Im m ≥ c₁` on the vertical segments over the window, and `Im m_κ ≥ c₁/2` for small `κ`
  set L : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc E₁ E₂ ×ˢ Set.Icc (N : ℝ)⁻¹ 1) with hL
  have hLc : IsCompact L := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hL0 : ∀ z ∈ L, 0 < z.im := by
    rintro _ ⟨p, hp, rfl⟩
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    exact lt_of_lt_of_le (by positivity) hp.2.1
  have hImL : ∀ E ∈ Set.Icc E₁ E₂, ∀ η : ℝ, (N : ℝ)⁻¹ ≤ η → η ≤ 1 →
      c₁ ≤ (mFun N σ ⟨E, η⟩).im := by
    intro E hE η hη1 hη2
    have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
    have h := im_mFun_ge_of_density hσ hNpos (E := E) (t := τ' / 8) (c₀ := c (τ' / 8)) (η := η)
      (by positivity) (by linarith [hE.1, ha2.1]) hη0 hc8.le
      (fun x hx => hρ8 x ⟨by linarith [hx.1, hE.1], by linarith [hx.2, hE.2]⟩)
    have harc : Real.arctan (τ' / 8) ≤ Real.arctan (τ' / 8 / η) :=
      Real.arctan_strictMono.monotone (le_div_self (by positivity) hη0 hη2)
    calc c₁ = 2 * c (τ' / 8) * Real.arctan (τ' / 8) := rfl
      _ ≤ 2 * c (τ' / 8) * Real.arctan (τ' / 8 / η) :=
          mul_le_mul_of_nonneg_left harc (by positivity)
      _ ≤ _ := h
  have hunif := tendstoUniformlyOn_mFun_regS hN1 T hLc hL0
  have hImev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ E ∈ Set.Icc E₁ E₂, ∀ η : ℝ, (N : ℝ)⁻¹ ≤ η → η ≤ 1 →
      c₁ / 2 ≤ (mFun N (specOf (regS κ (Tᵀ * T))) ⟨E, η⟩).im := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (c₁ / 2) (by positivity)]
      with κ hκ E hE η hη1 hη2
    have hz : (⟨E, η⟩ : ℂ) ∈ L :=
      ⟨(E, η), ⟨hE, hη1, hη2⟩, by apply Complex.ext <;> simp⟩
    have h1 := hκ _ hz
    have h2 := hImL E hE η hη1 hη2
    have h3 := Complex.abs_im_le_norm
      (mFun N σ ⟨E, η⟩ - mFun N (specOf (regS κ (Tᵀ * T))) ⟨E, η⟩)
    rw [Complex.sub_im] at h3
    rw [dist_eq_norm] at h1
    have h4 := (abs_le.1 h3).2
    linarith
  have hκev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT (by positivity)) fun κ hκ => hκ
  refine measure_le_of_eventually (l := 𝓝[>] (0 : ℝ))
    (Bi := fun κ => {ω | ∀ E ∈ Set.Icc E₁ E₂,
      |(eigCount (QN (regS κ (Tᵀ * T)) (X ω)) E : ℝ) -
        nClass N (specOf (regS κ (Tᵀ * T))) E| ≤ s}ᶜ) ?_ ?_
  · -- transfer of a count violation from `T` to `Ŝ + κ P₀` (Weyl, `n_κ → n`)
    intro ω hω
    simp only [hGT, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨Es, hEs, hbad⟩ := hω
    have hEs0 : 0 < Es := by linarith [hEs.1, ha2.1]
    set A := QN (Tᵀ * T) (X ω) with hAdef
    have hA := rigT_QN_herm (rigT_TtT_herm T) (X ω)
    have hcont := (rigT_nClass_continuousOn hσ hNpos).continuousAt (Ioi_mem_nhds hEs0)
    rcases lt_abs.1 hbad with hpos | hneg
    · set g := (eigCount A Es : ℝ) - nClass N σ Es - s with hg
      have hg0 : 0 < g := by linarith
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (g / 2) (by positivity)
      set η₀ := min (δ / 2) (τ' / 4) with hη₀
      have hη₀0 : 0 < η₀ := lt_min (by positivity) (by positivity)
      have hη₀δ : η₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hη₀τ : η₀ ≤ τ' / 4 := min_le_right _ _
      have hn1 : nClass N σ (Es - η₀) < nClass N σ Es + g / 2 := by
        have := hδ' (x := Es - η₀) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.2]
      have hlim := tendsto_nClass_regS hN1 T (E := Es - η₀) (by linarith [hEs.1, ha2.1])
      filter_upwards [hκev, (Metric.tendsto_nhds.1 hlim) (g / 2) (by positivity),
        rigT_norm_QN_regS T (X ω) hη₀0] with κ hκ hnκ hnorm
      have hAκ := rigT_QN_herm (regS_posDef hκ.1 T).isHermitian (X ω)
      set Aκ := QN (regS κ (Tᵀ * T)) (X ω) with hAκdef
      set δκ := ‖Aκ - A‖ with hδκ
      have hδκ0 : 0 ≤ δκ := norm_nonneg _
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le]
      refine ⟨Es - δκ, ⟨by linarith [hEs.1], by linarith [hEs.2]⟩, ?_⟩
      have hw := eigCount_weyl hA hAκ (show ‖A - Aκ‖ ≤ δκ by rw [norm_sub_rev]) (Es - δκ)
      rw [sub_add_cancel] at hw
      have hw' : (eigCount A Es : ℝ) ≤ (eigCount Aκ (Es - δκ) : ℝ) := by exact_mod_cast hw
      have hanti := rigT_nClass_anti (rigT_specOf_regS_nonneg hκ.1 T) hNpos
        (show Es - η₀ ≤ Es - δκ by linarith)
      rw [Real.dist_eq, abs_lt] at hnκ
      rw [lt_abs]
      left
      linarith [hnκ.2]
    · set g := nClass N σ Es - s - (eigCount A Es : ℝ) with hg
      have hg0 : 0 < g := by linarith
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (g / 2) (by positivity)
      set η₀ := min (δ / 2) (τ' / 4) with hη₀
      have hη₀0 : 0 < η₀ := lt_min (by positivity) (by positivity)
      have hη₀δ : η₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hη₀τ : η₀ ≤ τ' / 4 := min_le_right _ _
      have hn1 : nClass N σ Es - g / 2 < nClass N σ (Es + η₀) := by
        have := hδ' (x := Es + η₀) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      have hlim := tendsto_nClass_regS hN1 T (E := Es + η₀) (by linarith)
      filter_upwards [hκev, (Metric.tendsto_nhds.1 hlim) (g / 2) (by positivity),
        rigT_norm_QN_regS T (X ω) hη₀0] with κ hκ hnκ hnorm
      have hAκ := rigT_QN_herm (regS_posDef hκ.1 T).isHermitian (X ω)
      set Aκ := QN (regS κ (Tᵀ * T)) (X ω) with hAκdef
      set δκ := ‖Aκ - A‖ with hδκ
      have hδκ0 : 0 ≤ δκ := norm_nonneg _
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le]
      refine ⟨Es + δκ, ⟨by linarith [hEs.1], by linarith [hEs.2]⟩, ?_⟩
      have hw := eigCount_weyl hAκ hA (le_refl δκ) Es
      have hw' : (eigCount Aκ (Es + δκ) : ℝ) ≤ (eigCount A Es : ℝ) := by exact_mod_cast hw
      have hanti := rigT_nClass_anti (rigT_specOf_regS_nonneg hκ.1 T) hNpos
        (show Es + δκ ≤ Es + η₀ by linarith)
      rw [Real.dist_eq, abs_lt] at hnκ
      rw [lt_abs]
      right
      linarith [hnκ.1]
  · filter_upwards [hκev, hImev] with κ hκ hIm
    have hmκ : IsModel τ₄ C K N (regS κ (Tᵀ * T)) X :=
      (isModel_regS hτ hm hκ.1 hκ.2).mono hτ₄0 hτ₄3
    exact h₁ N hNN₁ K (regS κ (Tᵀ * T)) X E₁ E₂ hmκ hE₁ hE₂ hIm

/-- Theorem 3.12 (`thm:rigidity`) for a general `T`, with every edge with `a_k ≥ τ/2` regular at
`τ/2`: (rigidity) for all `k ≤ p`, `i ≤ N_k` with `γ_{k,i} ≥ τ`, simultaneously. -/
theorem rigidity_gen (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k → τ ≤ gammaBand N (specOf (T * Tᵀ)) k i →
          |lamBandT T (X ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
            rigBound N (bandNat N (specOf (T * Tᵀ)) k) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X hm _ _ => absurd (rigT_tau_le_one hm) hτ1⟩
  have hτh : 0 < τ / 2 := by positivity
  obtain ⟨hr0, hrτ⟩ := rigT_tauGen hτh (by linarith)
  set τr := tauGen (τ / 2) with hτr
  obtain ⟨N₁, h₁⟩ := rigidity_edge_gen (τ / 2) C ε (D + 2) hτh hε
  obtain ⟨N₂, h₂⟩ := rigidity_bulk_gen (τ / 2) τr c C ε (D + 2) hτh hr0 hε
  refine ⟨max (max N₁ N₂) 3, fun N hN Ω _ _ M K T X hm hedge hbulk => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have hNpos : 0 < N := by omega
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  have hσ := hda.nonneg
  have hmh : IsModelT (τ / 2) C M K N T X := hm.mono hτh (by linarith)
  set p := numBands N σ with hp
  -- the bands containing some `γ_{k,i} ≥ τ`, and their edges with `a_l ≥ τ/2`
  set Sb : Finset ℕ := (Finset.Icc 1 p).filter
    (fun k => ∃ i, 1 ≤ i ∧ i ≤ bandNat N σ k ∧ τ ≤ gammaBand N σ k i) with hSb
  set Se : Finset ℕ := (Finset.Icc 1 (2 * p)).filter
    (fun l => τ / 2 ≤ edgeVal N σ l ∧ (l + 1) / 2 ∈ Sb) with hSe
  have hSbf : ∀ k ∈ Sb, 1 ≤ k ∧ k ≤ p ∧ 1 ≤ bandNat N σ k ∧ τ ≤ edgeVal N σ (2 * k - 1) ∧
      cumCount N σ (k - 1) + 1 ≤ N := by
    intro k hk
    simp only [hSb, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkp⟩, i, hi1, hiN, hγ⟩ := hk
    have hγ0 : 0 < gammaBand N σ k i := by linarith
    have hmem := rigT_band_mem hda hk1 hkp hi1 hiN hγ0
    have hjN := rigT_index_le hσ hNpos (j := cumCount N σ (k - 1) + i) hγ0
    exact ⟨hk1, hkp, by omega, by linarith [hmem.2], by omega⟩
  have hcardb : Sb.card ≤ N := by
    have h := Finset.card_le_card_of_injOn (s := Sb) (t := Finset.Icc 1 N)
      (fun k => cumCount N σ (k - 1) + 1) ?_ ?_
    · simpa using h
    · intro k hk
      obtain ⟨-, -, -, -, h⟩ := hSbf k (Finset.mem_coe.1 hk)
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro k hk k' hk' heq
      simp only at heq
      obtain ⟨hk1, hkp, hNk, -, -⟩ := hSbf k (Finset.mem_coe.1 hk)
      obtain ⟨hk1', hkp', hNk', -, -⟩ := hSbf k' (Finset.mem_coe.1 hk')
      obtain ⟨-, -, hc⟩ := cumCount_spec hda hk1 hkp
      obtain ⟨-, -, hc'⟩ := cumCount_spec hda hk1' hkp'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := rigT_cumCount_mono (N := N) σ (show k ≤ k' - 1 by omega)
        omega
      · have := rigT_cumCount_mono (N := N) σ (show k' ≤ k - 1 by omega)
        omega
  have hcarde : Se.card ≤ 2 * Sb.card := by
    have hsub : Se ⊆ Sb.biUnion (fun k => {2 * k - 1, 2 * k}) := by
      intro l hl
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc] at hl
      rw [Finset.mem_biUnion]
      refine ⟨(l + 1) / 2, hl.2.2, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc Se.card ≤ (Sb.biUnion (fun k => {2 * k - 1, 2 * k})).card := Finset.card_le_card hsub
      _ ≤ ∑ k ∈ Sb, ({2 * k - 1, 2 * k} : Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Sb, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
      _ = 2 * Sb.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : ((Sb.disjSum Se).card : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Finset.card_disjSum, Real.rpow_two]
    have h : Sb.card + Se.card ≤ N ^ 2 := by nlinarith
    exact_mod_cast h
  -- the events of Theorems 3.14 (iii) and 3.15 (iii) at `τ/2`
  set Eb : ℕ → Set Ω := fun k => {ω | ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
    gammaBand N σ k i ∈ Set.Icc (edgeVal N σ (2 * k) + τr) (edgeVal N σ (2 * k - 1) - τr) →
    |lamBandT T (X ω) k i - gammaBand N σ k i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹} with hEb
  set Ee : ℕ → Set Ω := fun l => {ω | ∀ i, 1 ≤ i → i ≤ bandNat N σ ((l + 1) / 2) →
    gammaBand N σ ((l + 1) / 2) i ∈ Set.Icc (edgeVal N σ l - τr) (edgeVal N σ l + τr) →
    |lamBandT T (X ω) ((l + 1) / 2) i - gammaBand N σ ((l + 1) / 2) i| ≤
      rigBound N (bandNat N σ ((l + 1) / 2)) i ε} with hEe
  have hev : ∀ x ∈ Sb.disjSum Se, HighProbAt N (D + 2) (Sum.elim Eb Ee x) := by
    rintro (k | l) hx
    · have hk := Finset.inl_mem_disjSum.1 hx
      obtain ⟨hk1, hkp, -, ha, -⟩ := hSbf k hk
      exact h₂ N hN₂ M K T X k hmh (hbulk k hk1 hkp)
        (Or.inr (hedge (2 * k - 1) (by omega) (by omega) (by linarith)))
    · have hl := Finset.inr_mem_disjSum.1 hx
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc] at hl
      exact h₁ N hN₁ M K T X l hmh (hedge l hl.1.1 hl.1.2 hl.2.1)
  have hI := HighProbAt.biInter (Sb.disjSum Se) (by omega) hcard hev
  unfold HighProbAt at hI ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hI
  intro ω hω
  simp only [Set.mem_ofPred_eq]
  intro k hk1 hkp i hi1 hiN hγ
  have hkSb : k ∈ Sb := by
    simp only [hSb, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk1, hkp⟩, i, hi1, hiN, hγ⟩
  have hγ0 : 0 < gammaBand N σ k i := by linarith
  have hmem := rigT_band_mem hda hk1 hkp hi1 hiN hγ0
  have hjN := rigT_index_le hσ hNpos (j := cumCount N σ (k - 1) + i) hγ0
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  have hmin1 : 1 ≤ min i (bandNat N σ k + 1 - i) := le_min hi1 (by omega)
  have hminN : min i (bandNat N σ k + 1 - i) ≤ N := (min_le_left _ _).trans (by omega)
  by_cases hA : |gammaBand N σ k i - edgeVal N σ (2 * k - 1)| ≤ τr
  · have hkk : (2 * k - 1 + 1) / 2 = k := by omega
    have hlSe : 2 * k - 1 ∈ Se := by
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc, hkk]
      exact ⟨⟨by omega, by omega⟩, by linarith [hmem.2], hkSb⟩
    have hE : ω ∈ Ee (2 * k - 1) :=
      Set.mem_iInter₂.1 hω (Sum.inr (2 * k - 1)) (Finset.inr_mem_disjSum.2 hlSe)
    simp only [hEe, Set.mem_ofPred_eq, hkk] at hE
    have h := abs_le.1 hA
    exact hE i hi1 hiN ⟨by linarith [h.1], by linarith [h.2]⟩
  by_cases hB : τ / 2 ≤ edgeVal N σ (2 * k) ∧ |gammaBand N σ k i - edgeVal N σ (2 * k)| ≤ τr
  · have hkk : (2 * k + 1) / 2 = k := by omega
    have hlSe : 2 * k ∈ Se := by
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc, hkk]
      exact ⟨⟨by omega, by omega⟩, hB.1, hkSb⟩
    have hE : ω ∈ Ee (2 * k) :=
      Set.mem_iInter₂.1 hω (Sum.inr (2 * k)) (Finset.inr_mem_disjSum.2 hlSe)
    simp only [hEe, Set.mem_ofPred_eq, hkk] at hE
    have h := abs_le.1 hB.2
    exact hE i hi1 hiN ⟨by linarith [h.1], by linarith [h.2]⟩
  · have hE : ω ∈ Eb k :=
      Set.mem_iInter₂.1 hω (Sum.inl k) (Finset.inl_mem_disjSum.2 hkSb)
    simp only [hEb, Set.mem_ofPred_eq] at hE
    have hup : gammaBand N σ k i ≤ edgeVal N σ (2 * k - 1) - τr := by
      rw [not_le, abs_sub_comm, abs_of_nonneg (by linarith [hmem.2])] at hA
      linarith
    have hlow : edgeVal N σ (2 * k) + τr ≤ gammaBand N σ k i := by
      by_cases h2 : τ / 2 ≤ edgeVal N σ (2 * k)
      · have hB' : ¬ |gammaBand N σ k i - edgeVal N σ (2 * k)| ≤ τr := fun h => hB ⟨h2, h⟩
        rw [not_le, abs_of_nonneg (by linarith [hmem.1])] at hB'
        linarith
      · linarith
    exact (hE i hi1 hiN ⟨hlow, hup⟩).trans (rigT_bulk_le_rigBound hmin1 hminN)

/-! ## Compiled instances

Each theorem above has an `∃ N₀` conclusion, so no instance fixes a concrete `N ≥ N₀`. The
following instances are conditional: they specialise the fixed parameters (`τ = 1/5`,
`C = gaussMoment`, `c t = min t 1 / 50`, `ε = D = 1`) and the Gaussian ensemble, and keep the
model, edge and bulk hypotheses as binders. These hold together, for instance, at `N = 200`,
`M = 100`, `K = 200`, `T = (I₁₀₀ | 0)`: then `Σ = T Tᵀ = I₁₀₀`, `Tᵀ T` is singular, `p = 1`,
`a₁ = 3/2 + √2` is regular at `1/5`, and the density on `[a₂ + τ', a₁ − τ']` is at least
`min(τ', 1)/50`. -/

/-- Theorem 3.14 (iii) for a general `T` at `τ = 1/5`, `C = gaussMoment`, `ε = D = 1`, Gaussian
`X`; the model and edge hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (k : ℕ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    RegularEdge (1 / 5) N (specOf (T * Tᵀ)) k →
    HighProbAt N 1 {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2) →
      gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i ∈
        Set.Icc (edgeVal N (specOf (T * Tᵀ)) k - tauGen (1 / 5))
          (edgeVal N (specOf (T * Tᵀ)) k + tauGen (1 / 5)) →
      |lamBandT T (gaussX K N ω) ((k + 1) / 2) i -
          gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i| ≤
        rigBound N (bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2)) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_edge_gen (1 / 5) gaussMoment 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M K T k hm hk => h N hN M K T (gaussX K N) k hm hk⟩

/-- Theorem 3.15 (iii) for a general `T` at `τ = 1/5`, `τ' = 1/10`, `c t = min t 1 / 50`,
`C = gaussMoment`, `ε = D = 1`, Gaussian `X`; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (k : ℕ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    RegularBulk (fun t => min t 1 / 50) N (specOf (T * Tᵀ)) k →
    RegularEdge (1 / 5) N (specOf (T * Tᵀ)) (2 * k - 1) →
    HighProbAt N 1 {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k →
      gammaBand N (specOf (T * Tᵀ)) k i ∈
        Set.Icc (edgeVal N (specOf (T * Tᵀ)) (2 * k) + 1 / 10)
          (edgeVal N (specOf (T * Tᵀ)) (2 * k - 1) - 1 / 10) →
      |lamBandT T (gaussX K N ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ)⁻¹} := by
  obtain ⟨N₀, h⟩ := rigidity_bulk_gen (1 / 5) (1 / 10) (fun t => min t 1 / 50) gaussMoment 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M K T k hm hb he => h N hN M K T (gaussX K N) k hm hb (Or.inr he)⟩

/-- Theorem 3.12 for a general `T` at `τ = 1/5`, `C = gaussMoment`, `c t = min t 1 / 50`,
`ε = D = 1`, Gaussian `X`; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) →
      1 / 5 / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k → RegularEdge (1 / 5 / 2) N (specOf (T * Tᵀ)) k) →
    (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
      RegularBulk (fun t => min t 1 / 50) N (specOf (T * Tᵀ)) k) →
    HighProbAt N 1 {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k → 1 / 5 ≤ gammaBand N (specOf (T * Tᵀ)) k i →
        |lamBandT T (gaussX K N ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
          rigBound N (bandNat N (specOf (T * Tᵀ)) k) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_gen (1 / 5) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M K T hm he hb => h N hN M K T (gaussX K N) hm he hb⟩

end Anisotropic

#print axioms Anisotropic.lamBandT
#print axioms Anisotropic.rigidity_edge_gen
#print axioms Anisotropic.rigidity_bulk_gen
#print axioms Anisotropic.rigidity_gen
