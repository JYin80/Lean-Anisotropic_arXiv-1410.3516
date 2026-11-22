module

public import Anisotropic.Entrywise.Defs
public import Anisotropic.LinAlg.ResolventIdDiag
public import Anisotropic.LinAlg.ResolventId
public import Anisotropic.Density.Stability.Domains

@[expose] public section

/-! # Control parameters and the identities of Section 5 for `Σ = diag(σ)`

The functions `m_i` of (def_m_i), the control parameters `Λ`, `Λ_o`, `Θ`, `Ψ_Θ` and the event
`Ξ` of Section 5.1, the fluctuation terms `Z_s` of (Gii_exp) and (Gmumu_exp) in explicit form,
the bounds (m_i_bound), (m_asymp_1), (Theta_leq_Lambda), and (Gtt_bound) on `Ξ` for minors with
at most one removed index. -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-- (def_m_i). -/
def mI (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) (i : Fin M) : ℂ := -(σ i : ℂ) / (1 + σ i * mFun N σ z)

/-- `m_s`: `m_i` for `s = i ∈ 𝓘_M`, `m` for `s = μ ∈ 𝓘_N`. -/
def mS (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : Fin M ⊕ Fin N → ℂ :=
  Sum.elim (mI N σ z) fun _ => mFun N σ z

/-- `Λ = max_{s,t} |G_{st} − δ_{st} m_s| / (σ_s σ_t)`. -/
def Lambda {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ⨆ s : Fin M ⊕ Fin N, ⨆ t : Fin M ⊕ Fin N,
    ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖ / (sigS σ s * sigS σ t)

/-- `Λ_o = max_{s ≠ t} |G_{st}| / (σ_s σ_t)`. -/
def LambdaO {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ⨆ p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2},
    ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2)

/-- `Θ_M = |M⁻¹ Σ_i (G_ii − m_i)|`. -/
def ThetaM {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ‖(M : ℂ)⁻¹ * ∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)‖

/-- `Θ_N = |m_N − m|`. -/
def ThetaN {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ‖mN (diagonal σ) Xm z - mFun N σ z‖

def Theta {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ThetaM σ Xm z + ThetaN σ Xm z

/-- `Φ = (Nη)⁻¹`. -/
def PhiN (N : ℕ) (z : ℂ) : ℝ := ((N : ℝ) * z.im)⁻¹

/-- `Ψ_Θ = ((Im m + Θ)/(Nη))^{1/2}`. -/
def PsiTheta {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  √(((mFun N σ z).im + Theta σ Xm z) * PhiN N z)

/-- The indicator of `Ξ = {Λ ≤ (log N)⁻¹}`. -/
def xiInd {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  if Lambda σ Xm z ≤ (Real.log N)⁻¹ then 1 else 0

/-- `Z_i = (X G^{(i)} Xᵀ)_{ii} − N⁻¹ Σ_μ G^{(i)}_{μμ}` ((Gii_exp)). -/
def Zi {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) : ℂ :=
  (Xhat Xm * G1 (diagonal σ) Xm z (Sum.inl i) * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl i)
    - (N : ℂ)⁻¹ * ∑ μ, G1 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr μ)

/-- `Z_μ = (Xᵀ G^{(μ)} X)_{μμ} − N⁻¹ Σ_i G^{(μ)}_{ii}` ((Gmumu_exp)). -/
def Zmu {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) : ℂ :=
  ((Xhat Xm)ᵀ * G1 (diagonal σ) Xm z (Sum.inr μ) * Xhat Xm) (Sum.inr μ) (Sum.inr μ)
    - (N : ℂ)⁻¹ * ∑ i, G1 (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) (Sum.inl i)

def ZS {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : Fin M ⊕ Fin N → ℂ :=
  Sum.elim (Zi σ Xm z) (Zmu σ Xm z)

/-- The constant of (Theta_leq_Lambda). -/
def ThetaConst (τ : ℝ) : ℝ := τ⁻¹ ^ 2 + 1

/-- The lower constant of (m_asymp_1). -/
def mAsympLower (τ : ℝ) : ℝ := (1 + mBoundConst τ * τ⁻¹)⁻¹

/-- The upper constant of (m_i_bound) and (m_asymp_1). -/
def mAsympUpper (c τ : ℝ) : ℝ := max c⁻¹ (mBoundConst τ)

/-- The threshold for `(log N)⁻¹` under which the event `Ξ` gives (Gtt_bound) and
`|1 + m_N σ_i| ≥ c/2`, `|m_N| ≥ (2 C_m)⁻¹`. -/
def xiThr (c τ : ℝ) : ℝ :=
  min (mAsympLower τ * τ / 4) (min (c * τ / (2 * ThetaConst τ)) (2 * mBoundConst τ)⁻¹)

/-- (Gii_exp). -/
theorem Gii_exp {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (i : Fin M) :
    1 / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) = -1 / (σ i : ℂ)
      - (N : ℂ)⁻¹ * ∑ μ, G1 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr μ)
      - Zi σ Xm z i := by
  rw [Gaa hσ Xm hz i, Zi]
  ring

/-- (Gmumu_exp). -/
theorem Gmumu_exp {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (μ : Fin N) :
    1 / G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) = -z
      - (N : ℂ)⁻¹ * ∑ i, G1 (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) (Sum.inl i)
      - Zmu σ Xm z μ := by
  rw [Gii (posDef_diagonal_iff.2 hσ) Xm hz μ, Zmu]
  ring

/-- `Im m_i = σ_i² Im m / |1 + m σ_i|²`. -/
theorem im_mI {N : ℕ} {σ : Fin M → ℝ} (z : ℂ) (i : Fin M) :
    (mI N σ z i).im = σ i ^ 2 * (mFun N σ z).im / ‖1 + (σ i : ℂ) * mFun N σ z‖ ^ 2 := by
  rw [mI, Complex.div_im, Complex.sq_norm]
  simp only [Complex.neg_im, Complex.ofReal_im, Complex.neg_re, Complex.ofReal_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, zero_mul, neg_zero, zero_div, zero_add, zero_sub]
  ring

/-! ## Consequences of the density assumptions -/

/-- `τ ≤ 1` under the density assumptions, since `τ ≤ M/N ≤ τ⁻¹`. -/
private theorem control_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  rw [not_le] at hc
  linarith [inv_lt_one_of_one_lt₀ hc]

/-- `N > 0` under the density assumptions. -/
private theorem control_N_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `M > 0` under the density assumptions. -/
private theorem control_M_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < M := by
  rcases Nat.eq_zero_or_pos M with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `C_m > 0`. -/
private theorem control_mBoundConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)

/-- `0 < c_as ≤ C_m⁻¹` for `0 < τ ≤ 1`. -/
private theorem control_mAsympLower_bounds {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < mAsympLower τ ∧ mAsympLower τ ≤ (mBoundConst τ)⁻¹ ∧ mAsympLower τ ≤ 1 := by
  have hC := control_mBoundConst_pos hτ
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hD : 0 < 1 + mBoundConst τ * τ⁻¹ := by positivity
  refine ⟨inv_pos.2 hD, ?_, ?_⟩
  · exact inv_anti₀ hC (by nlinarith)
  · exact inv_le_one_of_one_le₀ (by nlinarith)

/-- `σ̲_s > 0` for `σ > 0`. -/
private theorem control_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `σ̲_s ≤ τ⁻¹` under the density assumptions. -/
private theorem control_sigS_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (s : Fin M ⊕ Fin N) : sigS σ s ≤ τ⁻¹ := by
  cases s with
  | inl i => exact h.bound_Sigma i
  | inr μ => exact (one_le_inv₀ h.pos).2 (control_tau_le_one h)

/-! ## Entrywise consequences of the definition of `Λ` -/

/-- `|G_{st} − δ_{st} m_s| ≤ σ_s σ_t Λ`. -/
private theorem control_entry_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (s t : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      ≤ sigS σ s * sigS σ t * Lambda σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (control_sigS_pos hσ s) (control_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      / (sigS σ s * sigS σ t) ≤ Lambda σ Xm z := by
    unfold Lambda
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove s)
    exact le_ciSup (f := fun t => ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      / (sigS σ s * sigS σ t)) (Set.finite_range _).bddAbove t
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `Λ ≥ 0`. -/
private theorem control_lambda_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ Lambda σ Xm z :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun t =>
    div_nonneg (norm_nonneg _) (mul_pos (control_sigS_pos hσ s) (control_sigS_pos hσ t)).le

/-- `|G_{ss} − m_s| ≤ σ_s² Λ`. -/
private theorem control_diag_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (s : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z s s - mS N σ z s‖ ≤ sigS σ s * sigS σ s * Lambda σ Xm z := by
  simpa using control_entry_le hσ Xm z s s

/-- `|G_{st}| ≤ σ_s σ_t Λ` for `s ≠ t`. -/
private theorem control_offdiag_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * Lambda σ Xm z := by
  simpa [hst] using control_entry_le hσ Xm z s t

/-- `Θ_N ≤ Λ` for `N > 0`. -/
private theorem control_thetaN_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (hN : 0 < N) :
    ThetaN σ Xm z ≤ Lambda σ Xm z := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : mN (diagonal σ) Xm z - mFun N σ z = (N : ℂ)⁻¹
      * ∑ μ, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mFun N σ z) := by
    rw [mN, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hb : ∀ μ : Fin N,
      ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mFun N σ z‖ ≤ Lambda σ Xm z := by
    intro μ
    simpa [mS, sigS] using control_diag_le hσ Xm z (Sum.inr μ)
  unfold ThetaN
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ μ, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mFun N σ z)‖
      ≤ (N : ℝ)⁻¹ * ∑ μ, ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mFun N σ z‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _μ : Fin N, Lambda σ Xm z := by
        gcongr with μ
        exact hb μ
    _ = Lambda σ Xm z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- `Θ_M ≤ τ⁻² Λ` under the density assumptions. -/
private theorem control_thetaM_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) : ThetaM σ Xm z ≤ τ⁻¹ ^ 2 * Lambda σ Xm z := by
  have hM := control_M_pos h
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hL := control_lambda_nonneg hσ Xm z
  have hb : ∀ i : Fin M, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i‖
      ≤ τ⁻¹ ^ 2 * Lambda σ Xm z := by
    intro i
    have h1 := control_diag_le hσ Xm z (Sum.inl i)
    simp only [mS, sigS, Sum.elim_inl] at h1
    have h2 : σ i * σ i ≤ τ⁻¹ ^ 2 := by
      rw [sq]
      exact mul_le_mul (h.bound_Sigma i) (h.bound_Sigma i) (hσ i).le
        (inv_pos.2 h.pos).le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hL)
  unfold ThetaM
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (M : ℝ)⁻¹ * ‖∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)‖
      ≤ (M : ℝ)⁻¹ * ∑ i, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (M : ℝ)⁻¹ * ∑ _i : Fin M, τ⁻¹ ^ 2 * Lambda σ Xm z := by
        gcongr with i
        exact hb i
    _ = τ⁻¹ ^ 2 * Lambda σ Xm z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- (m_i_bound) and (m_asymp_1). -/
theorem norm_mS_bounds {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) {z : ℂ} (hz : z ∈ specDomain τ N)
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (s : Fin M ⊕ Fin N) :
    mAsympLower τ * sigS σ s ≤ ‖mS N σ z s‖ ∧ ‖mS N σ z s‖ ≤ mAsympUpper c τ * sigS σ s := by
  obtain ⟨hm1, hm2, -⟩ := gen_prop_m_specDomain h hz
  have hτ := h.pos
  have hτ1 := control_tau_le_one h
  obtain ⟨hca0, hcaC, -⟩ := control_mAsympLower_bounds hτ hτ1
  cases s with
  | inl i =>
    have hw : 0 < ‖1 + (σ i : ℂ) * mFun N σ z‖ := hc.trans_le (hx i)
    have hnorm : ‖mS N σ z (Sum.inl i)‖ = σ i / ‖1 + (σ i : ℂ) * mFun N σ z‖ := by
      simp [mS, mI, abs_of_pos (hσ i)]
    have hwle : ‖1 + (σ i : ℂ) * mFun N σ z‖ ≤ 1 + mBoundConst τ * τ⁻¹ := by
      calc ‖1 + (σ i : ℂ) * mFun N σ z‖ ≤ ‖(1 : ℂ)‖ + ‖(σ i : ℂ) * mFun N σ z‖ := norm_add_le _ _
        _ = 1 + σ i * ‖mFun N σ z‖ := by
            rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ i)]
        _ ≤ 1 + mBoundConst τ * τ⁻¹ := by
            have := mul_le_mul (h.bound_Sigma i) hm2 (norm_nonneg _) (inv_pos.2 hτ).le
            linarith
    simp only [sigS, Sum.elim_inl]
    rw [hnorm]
    refine ⟨?_, ?_⟩
    · rw [mAsympLower, inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (hσ i).le hw hwle
    · calc σ i / ‖1 + (σ i : ℂ) * mFun N σ z‖ ≤ σ i / c :=
            div_le_div_of_nonneg_left (hσ i).le hc (hx i)
        _ = c⁻¹ * σ i := by rw [div_eq_inv_mul]
        _ ≤ mAsympUpper c τ * σ i :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (hσ i).le
  | inr μ =>
    simp only [mS, sigS, Sum.elim_inr, mul_one]
    exact ⟨hcaC.trans hm1, hm2.trans (le_max_right _ _)⟩

/-- (Theta_leq_Lambda). -/
theorem Theta_le_Lambda {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (hN : 0 < N) :
    Theta σ Xm z ≤ ThetaConst τ * Lambda σ Xm z := by
  rw [Theta, ThetaConst, add_mul, one_mul]
  exact add_le_add (control_thetaM_le h hσ Xm z) (control_thetaN_le hσ Xm z hN)

/-- On `Λ ≤ c_as τ / 4`: `|G_{tt} − m_t| ≤ (c_as/4) σ_t`, and `|G_{tt}| ≥ (3/4) c_as σ_t`. -/
private theorem control_diag_dev {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hL : Lambda σ Xm z ≤ mAsympLower τ * τ / 4) (t : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z t t - mS N σ z t‖ ≤ mAsympLower τ / 4 * sigS σ t ∧
      3 / 4 * mAsympLower τ * sigS σ t ≤ ‖G (diagonal σ) Xm z t t‖ := by
  have hτ := h.pos
  have hst := control_sigS_pos (N := N) hσ t
  have hst' := control_sigS_le h t
  have hL0 := control_lambda_nonneg hσ Xm z
  have hτL : τ⁻¹ * Lambda σ Xm z ≤ mAsympLower τ / 4 := by
    calc τ⁻¹ * Lambda σ Xm z ≤ τ⁻¹ * (mAsympLower τ * τ / 4) :=
          mul_le_mul_of_nonneg_left hL (inv_pos.2 hτ).le
      _ = mAsympLower τ / 4 := by field_simp
  have hsL : sigS σ t * Lambda σ Xm z ≤ mAsympLower τ / 4 :=
    (mul_le_mul_of_nonneg_right hst' hL0).trans hτL
  have hdev : ‖G (diagonal σ) Xm z t t - mS N σ z t‖ ≤ mAsympLower τ / 4 * sigS σ t := by
    calc ‖G (diagonal σ) Xm z t t - mS N σ z t‖ ≤ sigS σ t * sigS σ t * Lambda σ Xm z :=
          control_diag_le hσ Xm z t
      _ = sigS σ t * (sigS σ t * Lambda σ Xm z) := by ring
      _ ≤ sigS σ t * (mAsympLower τ / 4) := mul_le_mul_of_nonneg_left hsL hst.le
      _ = mAsympLower τ / 4 * sigS σ t := by ring
  refine ⟨hdev, ?_⟩
  have hm := (norm_mS_bounds hc h hσ hz hx t).1
  have h1 := norm_sub_norm_le (mS N σ z t) (G (diagonal σ) Xm z t t)
  rw [norm_sub_rev] at h1
  linarith

/-- (Gtt_bound) on `Ξ`, for minors with `|T| ≤ 1`. -/
theorem Gtt_bound {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (T : Finset (Fin M ⊕ Fin N)) (hT : T.card ≤ 1) (t : Fin M ⊕ Fin N) (ht : t ∉ T) :
    mAsympLower τ / 2 * sigS σ t ≤ ‖Gm (diagonal σ) Xm z T t t‖ ∧
      ‖Gm (diagonal σ) Xm z T t t‖ ≤ (mAsympUpper c τ + 1) * sigS σ t := by
  have hτ := h.pos
  obtain ⟨hca0, -, hca1⟩ := control_mAsympLower_bounds hτ (control_tau_le_one h)
  have hL : Lambda σ Xm z ≤ mAsympLower τ * τ / 4 :=
    (hΞ.trans hlog).trans (min_le_left _ _)
  have hL0 := control_lambda_nonneg hσ Xm z
  have hst := control_sigS_pos (N := N) hσ t
  have hm := norm_mS_bounds hc h hσ hz hx t
  -- the deviation `|G^{(T)}_{tt} − m_t| ≤ (c_as/3) σ_t`
  have hdev : ‖Gm (diagonal σ) Xm z T t t - mS N σ z t‖ ≤ mAsympLower τ / 3 * sigS σ t := by
    obtain ⟨hd0, -⟩ := control_diag_dev hc h hσ Xm hz hx hL t
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hT with h0 | h1
    · rw [Finset.card_eq_zero.1 h0, Gm_empty]
      refine hd0.trans (mul_le_mul_of_nonneg_right ?_ hst.le)
      linarith
    · obtain ⟨r, rfl⟩ := Finset.card_eq_one.1 h1
      have htr : t ≠ r := fun e => ht (by simp [e])
      have hrt : r ≠ t := Ne.symm htr
      have e : Gm (diagonal σ) Xm z {r} t t = G (diagonal σ) Xm z t t
          - G (diagonal σ) Xm z t r * G (diagonal σ) Xm z r t / G (diagonal σ) Xm z r r :=
        Gstu (posDef_diagonal_iff.2 hσ) Xm hz.1 r t t htr htr
      have hsr := control_sigS_pos (N := N) hσ r
      have hsr' := control_sigS_le h r
      have hst' := control_sigS_le h t
      obtain ⟨-, hrr⟩ := control_diag_dev hc h hσ Xm hz hx hL r
      have hrr0 : 0 < 3 / 4 * mAsympLower τ * sigS σ r := by positivity
      have htrb := control_offdiag_le hσ Xm z htr
      have hrtb := control_offdiag_le hσ Xm z hrt
      have hτL : τ⁻¹ * Lambda σ Xm z ≤ mAsympLower τ / 4 := by
        calc τ⁻¹ * Lambda σ Xm z ≤ τ⁻¹ * (mAsympLower τ * τ / 4) :=
              mul_le_mul_of_nonneg_left hL (inv_pos.2 hτ).le
          _ = mAsympLower τ / 4 := by field_simp
      have htL : sigS σ t * Lambda σ Xm z ≤ mAsympLower τ / 4 :=
        (mul_le_mul_of_nonneg_right hst' hL0).trans hτL
      have hrL : sigS σ r * Lambda σ Xm z ≤ mAsympLower τ / 4 :=
        (mul_le_mul_of_nonneg_right hsr' hL0).trans hτL
      have hoff : ‖G (diagonal σ) Xm z t r * G (diagonal σ) Xm z r t / G (diagonal σ) Xm z r r‖
          ≤ mAsympLower τ / 12 * sigS σ t := by
        rw [norm_div, norm_mul, div_le_iff₀ (hrr0.trans_le hrr)]
        calc ‖G (diagonal σ) Xm z t r‖ * ‖G (diagonal σ) Xm z r t‖
            ≤ (sigS σ t * sigS σ r * Lambda σ Xm z) * (sigS σ r * sigS σ t * Lambda σ Xm z) :=
              mul_le_mul htrb hrtb (norm_nonneg _) (by positivity)
          _ = sigS σ t * sigS σ r * ((sigS σ t * Lambda σ Xm z) * (sigS σ r * Lambda σ Xm z)) := by
              ring
          _ ≤ sigS σ t * sigS σ r * ((mAsympLower τ / 4) * (mAsympLower τ / 4)) := by
              gcongr
          _ = mAsympLower τ / 12 * sigS σ t * (3 / 4 * mAsympLower τ * sigS σ r) := by ring
          _ ≤ mAsympLower τ / 12 * sigS σ t * ‖G (diagonal σ) Xm z r r‖ := by
              gcongr
      rw [e]
      calc ‖G (diagonal σ) Xm z t t
            - G (diagonal σ) Xm z t r * G (diagonal σ) Xm z r t / G (diagonal σ) Xm z r r
            - mS N σ z t‖
          = ‖(G (diagonal σ) Xm z t t - mS N σ z t)
            - G (diagonal σ) Xm z t r * G (diagonal σ) Xm z r t / G (diagonal σ) Xm z r r‖ := by
            ring_nf
        _ ≤ ‖G (diagonal σ) Xm z t t - mS N σ z t‖
            + ‖G (diagonal σ) Xm z t r * G (diagonal σ) Xm z r t / G (diagonal σ) Xm z r r‖ :=
            norm_sub_le _ _
        _ ≤ mAsympLower τ / 4 * sigS σ t + mAsympLower τ / 12 * sigS σ t := add_le_add hd0 hoff
        _ = mAsympLower τ / 3 * sigS σ t := by ring
  have h1 := norm_sub_norm_le (mS N σ z t) (Gm (diagonal σ) Xm z T t t)
  have h2 := norm_sub_norm_le (Gm (diagonal σ) Xm z T t t) (mS N σ z t)
  rw [norm_sub_rev] at h1
  have hcs : 0 ≤ mAsympLower τ * sigS σ t := by positivity
  have hcs1 : mAsympLower τ * sigS σ t ≤ sigS σ t := by nlinarith
  constructor
  · nlinarith [hm.1]
  · nlinarith [hm.2]

/-- On `Ξ`: `|1 + m_N σ_i| ≥ c/2` and `|m_N| ≥ (2 C_m)⁻¹`. -/
theorem oneAddMN_ge {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹) :
    (∀ i, c / 2 ≤ ‖1 + mN (diagonal σ) Xm z * σ i‖) ∧
      (2 * mBoundConst τ)⁻¹ ≤ ‖mN (diagonal σ) Xm z‖ := by
  have hτ := h.pos
  have hC := control_mBoundConst_pos hτ
  have hθ := control_thetaN_le hσ Xm z (control_N_pos h)
  have hLx := hΞ.trans hlog
  have hL2 : Lambda σ Xm z ≤ c * τ / (2 * ThetaConst τ) :=
    hLx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hL3 : Lambda σ Xm z ≤ (2 * mBoundConst τ)⁻¹ :=
    hLx.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCT : 1 ≤ ThetaConst τ := by
    rw [ThetaConst]
    linarith [sq_nonneg τ⁻¹]
  unfold ThetaN at hθ
  refine ⟨fun i => ?_, ?_⟩
  · have e : (1 + (σ i : ℂ) * mFun N σ z) - (1 + mN (diagonal σ) Xm z * σ i)
        = (σ i : ℂ) * (mFun N σ z - mN (diagonal σ) Xm z) := by ring
    have h1 := norm_sub_norm_le (1 + (σ i : ℂ) * mFun N σ z) (1 + mN (diagonal σ) Xm z * σ i)
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ i), norm_sub_rev] at h1
    have h2 : σ i * ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ c / 2 := by
      calc σ i * ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ τ⁻¹ * Lambda σ Xm z :=
            mul_le_mul (h.bound_Sigma i) hθ (norm_nonneg _) (inv_pos.2 hτ).le
        _ ≤ τ⁻¹ * (c * τ / (2 * ThetaConst τ)) :=
            mul_le_mul_of_nonneg_left hL2 (inv_pos.2 hτ).le
        _ = c / (2 * ThetaConst τ) := by field_simp
        _ ≤ c / 2 := div_le_div_of_nonneg_left hc.le two_pos (by linarith)
    linarith [hx i]
  · obtain ⟨hm1, -, -⟩ := gen_prop_m_specDomain h hz
    have h1 := norm_sub_norm_le (mFun N σ z) (mN (diagonal σ) Xm z)
    rw [norm_sub_rev] at h1
    have e : (mBoundConst τ)⁻¹ = 2 * (2 * mBoundConst τ)⁻¹ := by
      field_simp
    linarith

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` -/

section Checks

example : PhiN 2 (2 * Complex.I) = 1 / 4 := by
  simp [PhiN]
  norm_num

example : (mI 2 (fun _ : Fin 2 => (1 : ℝ)) (2 * Complex.I) 0).im
    = (1 : ℝ) ^ 2 * (mFun 2 (fun _ : Fin 2 => (1 : ℝ)) (2 * Complex.I)).im
      / ‖1 + ((1 : ℝ) : ℂ) * mFun 2 (fun _ : Fin 2 => (1 : ℝ)) (2 * Complex.I)‖ ^ 2 :=
  im_mI (2 * Complex.I) 0

end Checks

end Anisotropic

#print axioms Anisotropic.mI
#print axioms Anisotropic.mS
#print axioms Anisotropic.Lambda
#print axioms Anisotropic.LambdaO
#print axioms Anisotropic.ThetaM
#print axioms Anisotropic.ThetaN
#print axioms Anisotropic.Theta
#print axioms Anisotropic.PhiN
#print axioms Anisotropic.PsiTheta
#print axioms Anisotropic.xiInd
#print axioms Anisotropic.Zi
#print axioms Anisotropic.Zmu
#print axioms Anisotropic.ZS
#print axioms Anisotropic.ThetaConst
#print axioms Anisotropic.mAsympLower
#print axioms Anisotropic.mAsympUpper
#print axioms Anisotropic.xiThr
#print axioms Anisotropic.Gii_exp
#print axioms Anisotropic.Gmumu_exp
#print axioms Anisotropic.im_mI
#print axioms Anisotropic.norm_mS_bounds
#print axioms Anisotropic.Theta_le_Lambda
#print axioms Anisotropic.Gtt_bound
#print axioms Anisotropic.oneAddMN_ge
