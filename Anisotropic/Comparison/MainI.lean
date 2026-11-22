module

public import Anisotropic.Comparison.SelfConsistent
public import Anisotropic.Comparison.Gronwall
public import Anisotropic.Gaussian.Main

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-!
# From the diagonal bounds to the anisotropic law

Section 7, proof of Proposition 7.1: by polarization, the bounds `|⟨u, B u⟩| ≺ K Ψ` on unit vectors
`u` for `B = Σ̲⁻¹(G − Π)Σ̲⁻¹` give the anisotropic law (Definition 3.20 (ii)) for all deterministic
unit vectors `v`, `w`.
-/

/-- `⟨c v, B w⟩ = c ⟨v, B w⟩`. -/
private theorem mainI_testBilin_smul_left {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin (a • v) B w = a * testBilin v B w := by
  have e : (fun s => (((a • v) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (v s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, smul_dotProduct, smul_eq_mul]

/-- `⟨v, B (c w)⟩ = c ⟨v, B w⟩`. -/
private theorem mainI_testBilin_smul_right {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin v B (a • w) = a * testBilin v B w := by
  have e : (fun s => (((a • w) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (w s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- `|v|² = ∑_s v_s²`. -/
private theorem mainI_testNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    testNorm v ^ 2 = ∑ s, v s ^ 2 := by
  unfold testNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|c v| = |c| |v|`. -/
private theorem mainI_testNorm_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    testNorm (a • v) = |a| * testNorm v := by
  unfold testNorm
  have e : ∑ s, (a • v) s ^ 2 = a ^ 2 * ∑ s, v s ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- `|v| = 0` only for `v = 0`. -/
private theorem mainI_eq_zero_of_testNorm {ι : Type*} [Fintype ι] {v : ι → ℝ}
    (h : testNorm v = 0) : v = 0 := by
  have h2 : ∑ s, v s ^ 2 = 0 := by
    rw [← mainI_testNorm_sq, h]
    ring
  funext s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (v t)).1 h2 s
    (Finset.mem_univ s)
  simpa using this

/-- From the diagonal bound for unit vectors, `|⟨a, B a⟩| ≤ |a|² N^{ε₀} K Ψ` off an event of
probability at most `N^{−(D+1)}`, for every `a`. -/
private theorem mainI_diag_event {Ω : Type*} [MeasureSpace Ω] {ι : Type*} [Fintype ι]
    {B : Ω → Matrix ι ι ℂ} {ε₀ D b : ℝ}
    (h : ∀ u : ι → ℝ, testNorm u = 1 →
      DomAt N ε₀ (D + 1) (fun ω => ‖testBilin u (B ω) u‖) (fun _ => b)) (a : ι → ℝ) :
    ∃ E : Set Ω, ℙ E ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) ∧
      ∀ ω ∉ E, ‖testBilin a (B ω) a‖ ≤ testNorm a ^ 2 * ((N : ℝ) ^ ε₀ * b) := by
  by_cases ha : testNorm a = 0
  · refine ⟨∅, by simp, fun ω _ => ?_⟩
    have h0 := mainI_eq_zero_of_testNorm ha
    subst h0
    rw [ha]
    simp [testBilin]
  · set u : ι → ℝ := (testNorm a)⁻¹ • a with hu
    have hpos : 0 < testNorm a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
    have hu1 : testNorm u = 1 := by
      rw [hu, mainI_testNorm_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ ha]
    have hau : a = testNorm a • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ ha, one_smul]
    refine ⟨{ω | (N : ℝ) ^ ε₀ * b < ‖testBilin u (B ω) u‖}, h u hu1, fun ω hω => ?_⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have e : testBilin a (B ω) a = ((testNorm a ^ 2 : ℝ) : ℂ) * testBilin u (B ω) u := by
      conv_lhs => rw [hau]
      rw [mainI_testBilin_smul_left, mainI_testBilin_smul_right]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hω (sq_nonneg _)

/-- The diagonal bounds `|⟨u, B u⟩| ≺ K Ψ` on the unit sphere give the anisotropic law. -/
theorem aniso_of_diag_bound {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.im) {ε₀ ε D K : ℝ} (hN : 2 ≤ N) (hK : 0 ≤ K)
    (hε : (N : ℝ) ^ ε₀ * K ≤ (N : ℝ) ^ ε)
    (h : ∀ z ∈ S, ∀ u : Fin M ⊕ Fin N → ℝ, testNorm u = 1 →
      DomAt N ε₀ (D + 1) (fun ω => ‖testBilin u (lawMat Sig (X ω) z) u‖)
        (fun _ => K * Psi N (specOf Sig) z)) :
    AnisotropicLawAt N ε D Sig X S := by
  intro z hz v w
  have hzim := hS z hz
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hΨ : 0 ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
    linarith [Real.sqrt_nonneg ((mFun N (specOf Sig) z).im / (N * z.im))]
  unfold DomAt
  by_cases hv0 : testNorm v = 0
  · have h0 := mainI_eq_zero_of_testNorm hv0
    subst h0
    have he : {ω | (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm (0 : Fin M ⊕ Fin N → ℝ) *
        testNorm w) < ‖testBilin 0 (lawMat Sig (X ω) z) w‖} = ∅ := by
      ext ω
      simp [testBilin, hv0]
    rw [he, measure_empty]
    simp
  by_cases hw0 : testNorm w = 0
  · have h0 := mainI_eq_zero_of_testNorm hw0
    subst h0
    have he : {ω | (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v *
        testNorm (0 : Fin M ⊕ Fin N → ℝ)) < ‖testBilin v (lawMat Sig (X ω) z) 0‖} = ∅ := by
      ext ω
      simp [testBilin, hw0, show (fun _ : Fin M ⊕ Fin N => (0 : ℂ)) = 0 from rfl]
    rw [he, measure_empty]
    simp
  have hvp : 0 < testNorm v := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv0)
  have hwp : 0 < testNorm w := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hw0)
  set v' : Fin M ⊕ Fin N → ℝ := (testNorm v)⁻¹ • v with hv'
  set w' : Fin M ⊕ Fin N → ℝ := (testNorm w)⁻¹ • w with hw'
  have hv1 : testNorm v' = 1 := by
    rw [hv', mainI_testNorm_smul, abs_inv, abs_of_pos hvp, inv_mul_cancel₀ hv0]
  have hw1 : testNorm w' = 1 := by
    rw [hw', mainI_testNorm_smul, abs_inv, abs_of_pos hwp, inv_mul_cancel₀ hw0]
  have hvv : v = testNorm v • v' := by rw [hv', smul_smul, mul_inv_cancel₀ hv0, one_smul]
  have hww : w = testNorm w • w' := by rw [hw', smul_smul, mul_inv_cancel₀ hw0, one_smul]
  -- `|v' + w'|² + |v' − w'|² = 4`.
  have hsum : testNorm (v' + w') ^ 2 + testNorm (v' - w') ^ 2 = 4 := by
    have h1 := mainI_testNorm_sq v'
    have h2 := mainI_testNorm_sq w'
    rw [hv1] at h1
    rw [hw1] at h2
    rw [mainI_testNorm_sq, mainI_testNorm_sq, ← Finset.sum_add_distrib]
    have e : ∀ s, (v' + w') s ^ 2 + (v' - w') s ^ 2 = 2 * v' s ^ 2 + 2 * w' s ^ 2 := fun s => by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← h1, ← h2]
    norm_num
  obtain ⟨Ea, hEa, ha⟩ := mainI_diag_event (B := fun ω => lawMat Sig (X ω) z) (h z hz) (v' + w')
  obtain ⟨Eb, hEb, hb⟩ := mainI_diag_event (B := fun ω => lawMat Sig (X ω) z) (h z hz) (v' - w')
  have hsub : {ω | (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v * testNorm w) <
      ‖testBilin v (lawMat Sig (X ω) z) w‖} ⊆ Ea ∪ Eb := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hA := ha ω hnot.1
    have hB := hb ω hnot.2
    have hpol := testBilin_polar (lawMat Sig (X ω) z) (lawMat_transpose hSig (X ω) hzim) v' w'
    have e : testBilin v (lawMat Sig (X ω) z) w =
        ((testNorm v * testNorm w : ℝ) : ℂ) * testBilin v' (lawMat Sig (X ω) z) w' := by
      conv_lhs => rw [hvv, hww]
      rw [mainI_testBilin_smul_left, mainI_testBilin_smul_right]
      push_cast
      ring
    have hnorm : ‖testBilin v' (lawMat Sig (X ω) z) w'‖ ≤
        (N : ℝ) ^ ε₀ * (K * Psi N (specOf Sig) z) := by
      rw [hpol, norm_div]
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [h4, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      calc ‖testBilin (v' + w') (lawMat Sig (X ω) z) (v' + w') -
            testBilin (v' - w') (lawMat Sig (X ω) z) (v' - w')‖
          ≤ ‖testBilin (v' + w') (lawMat Sig (X ω) z) (v' + w')‖ +
            ‖testBilin (v' - w') (lawMat Sig (X ω) z) (v' - w')‖ := norm_sub_le _ _
        _ ≤ testNorm (v' + w') ^ 2 * ((N : ℝ) ^ ε₀ * (K * Psi N (specOf Sig) z)) +
            testNorm (v' - w') ^ 2 * ((N : ℝ) ^ ε₀ * (K * Psi N (specOf Sig) z)) :=
          add_le_add hA hB
        _ = (N : ℝ) ^ ε₀ * (K * Psi N (specOf Sig) z) * 4 := by
          rw [← add_mul, hsum]
          ring
    have hfin : ‖testBilin v (lawMat Sig (X ω) z) w‖ ≤
        (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v * testNorm w) := by
      rw [e, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg hvp.le hwp.le)]
      have hvw : 0 ≤ testNorm v * testNorm w := mul_nonneg hvp.le hwp.le
      calc testNorm v * testNorm w * ‖testBilin v' (lawMat Sig (X ω) z) w'‖
          ≤ testNorm v * testNorm w * ((N : ℝ) ^ ε₀ * (K * Psi N (specOf Sig) z)) :=
            mul_le_mul_of_nonneg_left hnorm hvw
        _ = testNorm v * testNorm w * Psi N (specOf Sig) z * ((N : ℝ) ^ ε₀ * K) := by ring
        _ ≤ testNorm v * testNorm w * Psi N (specOf Sig) z * (N : ℝ) ^ ε :=
            mul_le_mul_of_nonneg_left hε (mul_nonneg hvw hΨ)
        _ = _ := by ring
    exact absurd hω (not_lt.2 hfin)
  have hNe : 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
    have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
      rw [← Real.rpow_add_one hNpos.ne']
      ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left hNr (Real.rpow_nonneg hNpos.le _) |>.trans_eq' (by ring)
  calc ℙ {ω | (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v * testNorm w) <
        ‖testBilin v (lawMat Sig (X ω) z) w‖}
      ≤ ℙ (Ea ∪ Eb) := measure_mono hsub
    _ ≤ ℙ Ea + ℙ Eb := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hEa hEb
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hNe

end Anisotropic

#print axioms Anisotropic.aniso_of_diag_bound
