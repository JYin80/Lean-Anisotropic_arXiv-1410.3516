import Anisotropic.Comparison.Ladder
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.LinAlg.Basic
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistent
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Model classes, the settings and the propositions (A_m), (C_m) for Wigner matrices -/

/-- A class of random symmetric matrices (a predicate on all probability spaces). -/
abbrev ModelClassW (N : ℕ) : Type 1 :=
  ∀ (Ω : Type) [MeasureSpace Ω], (Ω → Matrix (Fin N) (Fin N) ℝ) → Prop

/-- (a) of Theorem 12.2: `E W_{ij}³ = 0`. -/
def zeroThirdW {N : ℕ} : ModelClassW N := fun _ _ W => ∀ i j, ∫ ω, W ω i j ^ 3 = 0

/-- The class with no condition beyond the entry conditions. -/
def allModelsW {N : ℕ} : ModelClassW N := fun _ _ _ => True

/-- The standing hypotheses of §12.2 on `(τ, N, A, S)`. -/
structure WigSetting (τ : ℝ) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop where
  pos : 0 < τ
  le_one : τ ≤ 1
  symmA : A.IsHermitian
  normA : ‖A‖ ≤ τ⁻¹
  domain : SpectralDomainW τ N S
  standing : StandingBoundW τ (specOf A) S

/-- `F_v(W, z) = |G_{vv}(z) − Π_{vv}(z)|`. -/
def FvW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ) : ℝ :=
  ‖ent (GW A Wm z - piW A z) v v‖

/-- (A_m) of §12.2, (bound_assumption_W), at fixed `N`, for the class `P` with moments `C`. -/
def PropAW (N : ℕ) (C : ℕ → ℝ) (P : ModelClassW N) (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
    (C₀ δ : ℝ) (m : ℕ) (ε D : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
    ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
      DomAt N ε D (fun ω => (ent (GW A (W ω) z) v v).im)
        (fun _ => (mW (specOf A) z).im + (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z)

/-- (C_m) of §12.2, (bound_goal_W), at fixed `N`, for the class `P` with moments `C`. -/
def PropCW (N : ℕ) (C : ℕ → ℝ) (P : ModelClassW N) (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
    (C₀ δ : ℝ) (m : ℕ) (ε D : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
    ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
      ODomAt N ε D (fun ω => ent (GW A (W ω) z - piW A z) v v)
        (fun _ => (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z)

/-- The real orthogonal matrix of eigenvectors of a symmetric `M`: `U Uᵀ = 1`, `Uᵀ U = 1`
and `M = U diag(λ) Uᵀ`. -/
private lemma props_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
    ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ), U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      M = U * diagonal l * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), hM.eigenvalues, ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- For `M = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w ≠ 0`, `(M − w)⁻¹` is the rotated
diagonal `(λₖ − w)⁻¹`. -/
private lemma props_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx M = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hMU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - w) =
        diagonal (fun k => (l k : ℂ)) - w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  refine Matrix.inv_eq_right_inv ?_
  rw [hM]
  calc cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ *
        (cplx U * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ)
      = cplx U * diagonal (fun k => (l k : ℂ) - w) * ((cplx U)ᵀ * cplx U) *
        diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
        have : (fun k => ((l k : ℂ) - w) * ((l k : ℂ) - w)⁻¹) = fun _ => 1 := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]

/-- A real matrix `Q` with `Qᵀ Q = 1` preserves the Euclidean norm of a test vector. -/
private lemma props_testNorm_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) (v : ι → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- The diagonal sandwich `⟨v, U D Uᵀ v⟩ = ∑ₖ dₖ ((Uᵀ v)ₖ)²`. -/
private lemma props_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
    (v : Fin N → ℝ) :
    ent (cplx U * diagonal d * (cplx U)ᵀ) v v = ∑ k, d k * ((((Uᵀ *ᵥ v) k : ℝ) : ℂ)) ^ 2 := by
  have h1 : cvec v ᵥ* cplx U = cvec (Uᵀ *ᵥ v) := by
    funext k
    simp [cvec, cplx, vecMul, dotProduct, mulVec, mul_comm]
  have h2 : (cplx U)ᵀ *ᵥ cvec v = cvec (Uᵀ *ᵥ v) := by
    funext k
    simp [cvec, cplx, dotProduct, mulVec]
  unfold ent
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
    ← Matrix.mulVec_mulVec, h2]
  simp [dotProduct, cvec, sq, mulVec_diagonal, mul_left_comm]

/-- `Im G^W_{vv}(z) ≤ |v|² / Im z` for a real symmetric `W + A` and `Im z > 0`. -/
private lemma props_im_GW_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) :
    (ent (GW A Wm z) v v).im ≤ z.im⁻¹ * testNorm v ^ 2 := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := props_eig_decomp (hW'.add hA)
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    props_resolvent_eq hUU hUU' hMU hne
  rw [hG, props_ent_sandwich, Complex.im_sum]
  have hsq : testNorm v ^ 2 = ∑ k, ((Uᵀ *ᵥ v) k) ^ 2 := by
    rw [← props_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v]
    unfold testNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [hsq, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hc : ((((Uᵀ *ᵥ v) k : ℝ) : ℂ)) ^ 2 = (((Uᵀ *ᵥ v) k) ^ 2 : ℝ) := by push_cast; ring
  rw [hc, Complex.im_mul_ofReal]
  have h1 : (((l k : ℂ) - z)⁻¹).im = z.im / Complex.normSq ((l k : ℂ) - z) := by
    rw [Complex.inv_im]
    simp
  have h2 : z.im ^ 2 ≤ Complex.normSq ((l k : ℂ) - z) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith [sq_nonneg (l k - z.re)]
  have h3 : z.im / Complex.normSq ((l k : ℂ) - z) ≤ z.im⁻¹ := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h2)]
    rw [inv_mul_eq_div, le_div_iff₀ hz]
    nlinarith
  rw [h1, mul_comm]
  exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _) |>.trans_eq (by ring)

/-- (A_0) (Lemma 7.3 analogue). -/
theorem wig_propA_zero (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (P : ModelClassW N)
      (C₀ δ : ℝ), WigSetting τ N A S → 0 ≤ C₀ → 0 ≤ δ → PropAW N C P A S C₀ δ 0 ε D := by
  set K : ℝ := (3 * τ⁻¹ + 1) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨max 1 ⌈K ^ ε⁻¹⌉₊, fun N hN A S P C₀ δ hset _ _ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hNε : K ≤ (N : ℝ) ^ ε := by
    have h0 : ⌈K ^ ε⁻¹⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    have h1 : K ^ ε⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc K = (K ^ ε⁻¹) ^ ε := (Real.rpow_inv_rpow hK0.le hε.ne').symm
      _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le _) h1 hε.le
  intro Ω _ _ W hW _ z hz v hv
  have hzD := hset.domain.1 hz.1
  obtain ⟨hzim, hzE, -, hzη⟩ := hzD
  have hη : 1 ≤ z.im := by
    have := hz.2
    simpa using this
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i =>
    (abs_specOf_le_norm hset.symmA i).trans hset.normA
  have hm : K⁻¹ * z.im ≤ (mW (specOf A) z).im := im_mW_ge hN1 hset.pos ha hzim hzE hzη
  have hm1 : K⁻¹ ≤ (mW (specOf A) z).im :=
    le_trans (le_mul_of_one_le_right (inv_nonneg.2 hK0.le) hη) hm
  have hPsi : 0 ≤ PsiW (specOf A) z := by
    unfold PsiW
    positivity
  have hb : 0 ≤ (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) hPsi
  have hbound : 1 ≤ (N : ℝ) ^ ε * ((mW (specOf A) z).im +
      (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) := by
    have h1 : 1 ≤ (N : ℝ) ^ ε * (mW (specOf A) z).im := by
      calc (1 : ℝ) = K * K⁻¹ := (mul_inv_cancel₀ hK0.ne').symm
        _ ≤ (N : ℝ) ^ ε * (mW (specOf A) z).im :=
          mul_le_mul hNε hm1 (inv_nonneg.2 hK0.le) (Real.rpow_nonneg hNpos.le _)
    have h2 : 0 ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) :=
      mul_nonneg (Real.rpow_nonneg hNpos.le _) hb
    rw [mul_add]
    linarith
  have hempty : {ω | (N : ℝ) ^ ε * ((mW (specOf A) z).im +
      (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) < (ent (GW A (W ω) z) v v).im} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have hG := props_im_GW_le hset.symmA (hW.symm ω) hzim v
    rw [hv] at hG
    have : z.im⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hη
    nlinarith
  unfold DomAt
  simp only [hempty, measure_empty]
  exact zero_le

/-! ## Instances -/

/-- The standing hypotheses `WigSetting` hold at `τ = 1/2`, `A = aEx N`, `S = 𝐃^W(1/2, N)`. -/
example {N : ℕ} (hN : 1 ≤ N) : WigSetting (1 / 2) N (aEx N) (domW (1 / 2) N) where
  pos := by norm_num
  le_one := by norm_num
  symmA := aEx_isHermitian N
  normA := (norm_aEx_le hN).trans (by norm_num)
  domain := spectralDomainW_domW _ _
  standing := standingBoundW_aEx hN

#print axioms Anisotropic.wig_propA_zero
#print axioms Anisotropic.ModelClassW
#print axioms Anisotropic.zeroThirdW
#print axioms Anisotropic.allModelsW
#print axioms Anisotropic.WigSetting
#print axioms Anisotropic.FvW
#print axioms Anisotropic.PropAW
#print axioms Anisotropic.PropCW

end Anisotropic
