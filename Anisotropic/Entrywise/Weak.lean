module

public import Anisotropic.Entrywise.Initial
public import Anisotropic.Entrywise.Lattice

@[expose] public section

/-! # Proposition 5.1: the weak entrywise law `Λ ≺ (Nη)^{−1/4}`

`Σ = diag(σ)`, at fixed `N`, on a spectral domain `S` (Definition 3.20) on which (1+xm) and the
stability of Definition 5.4 hold.

Fix `z ∈ S`, `ε_r = min(ε, τ)/16`, `n = N^{ε_r}` and `δ = N^{2ε_r} Φ^{1/2}`, `Φ = (Nη)⁻¹`.
Along the lattice `z_k = z + i k N⁻⁵`, `k ≤ K = ⌈(1 − η) N⁵⌉`, the good event is the
intersection of the events of Lemma 5.2, Lemma 5.3, (Gii_2) and (Gmumu-m) at every `z_k`, of
`{‖XᵀX‖ ≤ C}` and of the event of Lemma 5.5 at `z_K`. On it:
* on `Ξ(z_k)`, `Ψ_Θ ≤ C_ψ Φ^{1/2}`, `|f(m_N) − z_k| ≤ |calDErr| + |[Z]_N| + |[Z]_M| ≤ δ(z_k)`,
  and `Λ ≤ K_g (n Ψ_Θ + Θ_N)` from
  `G_{ii} − m_i = −G_{ii} (σ_i (m_N − m) + σ_i Z_i + giiErr_i) / (1 + σ_i m)`;
* stability at `z_k`, whose hypothesis at `z_k + i N⁻⁵ = z_{k+1}` is the conclusion at `z_{k+1}`,
  gives `Θ_N ≤ max(C₀, C₁) δ / (Im m + √δ) ≤ B⁺ √δ`, hence `Λ(z_k) ≤ n² Φ^{1/4}`;
* the Lipschitz bound for `Λ` along the vertical segment gives
  `Λ(z_k) ≤ n² N^{−τ/4} + L N⁻³ ≤ (log N)⁻¹`, i.e. `Ξ(z_k)` from `Λ(z_{k+1}) ≤ n² Φ^{1/4}`;
* Lemma 5.5 gives `Ξ(z_K)`.
This is the continuity argument of Section 5.1 (proof of Proposition 5.1). The union bound runs
over at most `N⁹` indices per family.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Constants -/

/-- `C_ψ = (C_m + C_Θ)^{1/2}`: `Ψ_Θ ≤ C_ψ Φ^{1/2}` on `Ξ`. -/
private def weak_Cpsi (τ : ℝ) : ℝ := √(mBoundConst τ + ThetaConst τ)

/-- The constant of `|f(m_N) − z| ≤ A n Ψ_Θ` on `Ξ`. -/
private def weak_A (c τ : ℝ) : ℝ := 1 + τ⁻¹ * (4 * τ⁻¹ ^ 2 * c⁻¹ ^ 2) + weak_Cpsi τ

/-- The constant of `Λ ≤ K_g (n Ψ_Θ + Θ_N)` on `Ξ`. -/
private def weak_Kg (c τ : ℝ) : ℝ := ((mAsympUpper c τ + 1) / c + 1) * (1 + weak_Cpsi τ)

private theorem weak_Cpsi_nonneg (τ : ℝ) : 0 ≤ weak_Cpsi τ := Real.sqrt_nonneg _

private theorem weak_A_nonneg {c τ : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 0 ≤ weak_A c τ := by
  have := weak_Cpsi_nonneg τ
  unfold weak_A
  positivity

private theorem weak_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

private theorem weak_Kg_ge_one {c τ : ℝ} (hc : 0 < c) : 1 ≤ weak_Kg c τ := by
  have h1 : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have h2 : 0 ≤ (mAsympUpper c τ + 1) / c := by positivity
  have h3 := weak_Cpsi_nonneg τ
  unfold weak_Kg
  nlinarith

/-! ## Deterministic bounds at one point -/

section Det

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `σ̲_s > 0`. -/
private theorem weak_sigS_pos (hσ : ∀ i, 0 < σ i) (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Λ_o ≥ 0`. -/
private theorem weak_LambdaO_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) : 0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (weak_sigS_pos hσ _) (weak_sigS_pos hσ _)).le

/-- `|G_{st}| ≤ σ̲_s σ̲_t Λ_o` for `s ≠ t`. -/
private theorem weak_offdiag_le (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (weak_sigS_pos hσ s) (weak_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
    unfold LambdaO
    exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `‖N⁻¹ Σ_j f_j‖ ≤ (#ι / N) K` when every `‖f_j‖ ≤ K`. -/
private theorem weak_avg_le {ι : Type*} [Fintype ι] (hN : 0 < N) (f : ι → ℂ) {K : ℝ}
    (hK : ∀ j, ‖f j‖ ≤ K) :
    ‖(N : ℂ)⁻¹ * ∑ j, f j‖ ≤ (Fintype.card ι : ℝ) / N * K := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, f j‖ ≤ (N : ℝ)⁻¹ * ∑ _j : ι, K := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hK j)
    _ = (Fintype.card ι : ℝ) / N * K := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- `0 ≤ Φ ≤ N^{−τ}` on `𝐃(τ,N)`. -/
private theorem weak_Phi_le {τ : ℝ} (hN : 0 < N) {w : ℂ} (hw : w ∈ specDomain τ N) :
    0 ≤ PhiN N w ∧ PhiN N w ≤ (N : ℝ) ^ (-τ) := by
  obtain ⟨h0, -, -, hη, -⟩ := hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [Real.rpow_add hN0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
  have hx : (N : ℝ) ^ τ ≤ (N : ℝ) * w.im := by
    rw [← e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  refine ⟨by unfold PhiN; positivity, ?_⟩
  unfold PhiN
  rw [Real.rpow_neg hN0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hx

/-- `Φ ≤ 1` on `𝐃(τ,N)`, `τ ≥ 0`. -/
private theorem weak_Phi_le_one {τ : ℝ} (hτ : 0 ≤ τ) (hN : 0 < N) {w : ℂ}
    (hw : w ∈ specDomain τ N) : PhiN N w ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (weak_Phi_le hN hw).2.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))

/-- `(Φ^{1/4})² = Φ^{1/2} = √Φ`. -/
private theorem weak_quarter_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = √x := by
  rw [← Real.rpow_add' hx (by norm_num), Real.sqrt_eq_rpow]
  norm_num

/-- `Ψ_Θ ≤ C_ψ Φ^{1/2}` on `Ξ` with `(log N)⁻¹ ≤ 1`. -/
private theorem weak_psi_le {τ : ℝ} (hN : 0 < N) (da : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : w ∈ specDomain τ N)
    (hlog1 : (Real.log N)⁻¹ ≤ 1) (hΞ : Lambda σ Xm w ≤ (Real.log N)⁻¹) :
    PsiTheta σ Xm w ≤ weak_Cpsi τ * √(PhiN N w) := by
  have hτ := da.pos
  obtain ⟨-, hm, -⟩ := gen_prop_m_specDomain da hw
  have him1 : (mFun N σ w).im ≤ mBoundConst τ := (Complex.im_le_norm _).trans hm
  have hθ := Theta_le_Lambda da hσ Xm w hN
  have hC : 0 ≤ ThetaConst τ := by unfold ThetaConst; positivity
  have hθ1 : Theta σ Xm w ≤ ThetaConst τ :=
    hθ.trans ((mul_le_mul_of_nonneg_left (hΞ.trans hlog1) hC).trans (mul_one _).le)
  have hΦ0 := (weak_Phi_le hN hw).1
  have hCm := weak_Cm_pos hτ
  unfold PsiTheta weak_Cpsi
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right (by linarith) hΦ0

/-- `G_{ii} − m_i = −G_{ii} (σ_i (m_N − m) + σ_i Z_i + giiErr_i) / (1 + σ_i m)`. -/
private theorem weak_gii_id (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ}
    (hw : 0 < w.im) (i : Fin M) (h1 : 1 + (σ i : ℂ) * mFun N σ w ≠ 0) :
    G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) - mI N σ w i =
      -G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) *
        ((σ i : ℂ) * (mN (diagonal σ) Xm w - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i
          + giiErr σ Xm w i) / (1 + (σ i : ℂ) * mFun N σ w) := by
  have hG := G_diag_ne_zero (posDef_diagonal_iff.2 hσ) Xm hw (Sum.inl i)
  rw [mI, giiErr]
  field_simp
  ring

/-- The bounds at a point `w` of `Ξ` where the inputs of Lemma 5.2, Lemma 5.3, (Gii_2) and
(Gmumu-m) hold with the factor `n`: `|f(m_N) − w| ≤ A n Ψ_Θ` and `Λ ≤ K_g (n Ψ_Θ + Θ_N)`. -/
private theorem weak_point {τ c : ℝ} (hc : 0 < c) (hN : 0 < N) (da : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : w ∈ specDomain τ N)
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖) (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hlog1 : (Real.log N)⁻¹ ≤ 1) (hΞ : Lambda σ Xm w ≤ (Real.log N)⁻¹) {n : ℝ} (hn : 0 ≤ n)
    (hZ : ∀ s, ‖ZS σ Xm w s‖ + LambdaO σ Xm w ≤ n * PsiTheta σ Xm w)
    (hD : ‖calDErr σ Xm w‖ ≤ n * PsiTheta σ Xm w ^ 2)
    (hgii : ∀ i, ‖giiErr σ Xm w i‖ ≤ n * (σ i * PsiTheta σ Xm w ^ 2))
    (hmu : ∀ μ, ‖G (diagonal σ) Xm w (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm w‖ ≤
      n * PsiTheta σ Xm w) :
    ‖fC N σ (mN (diagonal σ) Xm w) - w‖ ≤ weak_A c τ * (n * PsiTheta σ Xm w) ∧
      Lambda σ Xm w ≤ weak_Kg c τ * (n * PsiTheta σ Xm w + ThetaN σ Xm w) := by
  have hτ := da.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set ψ := PsiTheta σ Xm w with hψ
  set r := n * ψ with hr
  have hψ0 : 0 ≤ ψ := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := mul_nonneg hn hψ0
  have hCψ0 := weak_Cpsi_nonneg τ
  -- `Ψ_Θ ≤ C_ψ`
  have hψC : ψ ≤ weak_Cpsi τ := by
    have h1 := weak_psi_le hN da hσ Xm hw hlog1 hΞ
    have hΦ1 : √(PhiN N w) ≤ 1 := Real.sqrt_le_one.mpr (weak_Phi_le_one hτ.le hN hw)
    calc ψ ≤ weak_Cpsi τ * √(PhiN N w) := h1
      _ ≤ weak_Cpsi τ * 1 := mul_le_mul_of_nonneg_left hΦ1 hCψ0
      _ = weak_Cpsi τ := mul_one _
  have hsq : n * ψ ^ 2 ≤ weak_Cpsi τ * r := by
    have := mul_le_mul_of_nonneg_left hψC (mul_nonneg hn hψ0)
    rw [hr]
    nlinarith
  have hLo0 := weak_LambdaO_nonneg hσ Xm w
  have hZi : ∀ i, ‖Zi σ Xm w i‖ ≤ r := fun i => by
    have := hZ (Sum.inl i)
    simp only [ZS, Sum.elim_inl] at this
    linarith
  have hZmu : ∀ μ, ‖Zmu σ Xm w μ‖ ≤ r := fun μ => by
    have := hZ (Sum.inr μ)
    simp only [ZS, Sum.elim_inr] at this
    linarith
  have hLo : LambdaO σ Xm w ≤ r := by
    have := hZ (Sum.inr ⟨0, hN⟩)
    linarith [norm_nonneg (ZS σ Xm w (Sum.inr ⟨0, hN⟩))]
  have hA := (oneAddMN_ge hc da hσ Xm hw hx hlog hΞ).1
  refine ⟨?_, ?_⟩
  · -- `f(m_N) − w = calDErr + [Z]_N + [Z]_M`
    have e : fC N σ (mN (diagonal σ) Xm w) - w = calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w := by
      unfold calDErr
      ring
    have hZN : ‖ZN σ Xm w‖ ≤ r := by
      unfold ZN
      have := weak_avg_le hN (Zmu σ Xm w) hZmu
      rwa [Fintype.card_fin, div_self hN0.ne', one_mul] at this
    have hZM : ‖ZM σ Xm w‖ ≤ τ⁻¹ * (4 * τ⁻¹ ^ 2 * c⁻¹ ^ 2 * r) := by
      unfold ZM
      have hterm : ∀ i, ‖(σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm w * σ i) ^ 2 * Zi σ Xm w i‖
          ≤ 4 * τ⁻¹ ^ 2 * c⁻¹ ^ 2 * r := by
        intro i
        have hσi := hσ i
        have hσle := da.bound_Sigma i
        have hAi := hA i
        have hA0 : 0 < ‖1 + mN (diagonal σ) Xm w * σ i‖ := lt_of_lt_of_le (half_pos hc) hAi
        rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hσi]
        calc σ i ^ 2 / ‖1 + mN (diagonal σ) Xm w * σ i‖ ^ 2 * ‖Zi σ Xm w i‖
            ≤ τ⁻¹ ^ 2 / (c / 2) ^ 2 * r := by
              gcongr
              exact hZi i
          _ = 4 * τ⁻¹ ^ 2 * c⁻¹ ^ 2 * r := by
              field_simp
              ring
      have hav := weak_avg_le hN _ hterm
      rw [Fintype.card_fin] at hav
      have hφ : (M : ℝ) / N ≤ τ⁻¹ := da.phi_upper
      refine hav.trans (mul_le_mul_of_nonneg_right hφ (by positivity))
    rw [e]
    calc ‖calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w‖
        ≤ ‖calDErr σ Xm w‖ + ‖ZN σ Xm w‖ + ‖ZM σ Xm w‖ := norm_add₃_le
      _ ≤ weak_Cpsi τ * r + r + τ⁻¹ * (4 * τ⁻¹ ^ 2 * c⁻¹ ^ 2 * r) := by
          gcongr
          exact hD.trans hsq
      _ = weak_A c τ * r := by unfold weak_A; ring
  · -- `Λ ≤ K_g (n Ψ_Θ + Θ_N)`
    have hθ0 : 0 ≤ ThetaN σ Xm w := norm_nonneg _
    have hKg := weak_Kg_ge_one (τ := τ) hc
    have hb0 : 0 ≤ weak_Kg c τ * (r + ThetaN σ Xm w) := by positivity
    have hle1 : r + ThetaN σ Xm w ≤ weak_Kg c τ * (r + ThetaN σ Xm w) :=
      le_mul_of_one_le_left (by positivity) hKg
    unfold Lambda
    refine Real.iSup_le (fun s => Real.iSup_le (fun t => ?_) hb0) hb0
    have hst0 : 0 < sigS (N := N) σ s * sigS σ t :=
      mul_pos (weak_sigS_pos hσ s) (weak_sigS_pos hσ t)
    rw [div_le_iff₀ hst0]
    by_cases hst : s = t
    · subst hst
      simp only [ite_true]
      cases s with
      | inl i =>
          have hσi := hσ i
          simp only [mS, sigS, Sum.elim_inl]
          have hxi := hx i
          have hx0 : 0 < ‖1 + (σ i : ℂ) * mFun N σ w‖ := hc.trans_le hxi
          rw [weak_gii_id hσ Xm hw.1 i (norm_pos_iff.1 hx0)]
          have hG := (Gtt_bound hc da hσ Xm hw hx hlog hΞ ∅ (by simp) (Sum.inl i)
            (by simp)).2
          rw [Gm_empty] at hG
          simp only [sigS, Sum.elim_inl] at hG
          have hnum : ‖(σ i : ℂ) * (mN (diagonal σ) Xm w - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i
              + giiErr σ Xm w i‖ ≤ σ i * (ThetaN σ Xm w + (1 + weak_Cpsi τ) * r) := by
            refine norm_add₃_le.trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi]
            have h3 : ‖giiErr σ Xm w i‖ ≤ σ i * (weak_Cpsi τ * r) := by
              calc ‖giiErr σ Xm w i‖ ≤ n * (σ i * ψ ^ 2) := hgii i
                _ = σ i * (n * ψ ^ 2) := by ring
                _ ≤ σ i * (weak_Cpsi τ * r) := mul_le_mul_of_nonneg_left hsq hσi.le
            have h1 : σ i * ‖mN (diagonal σ) Xm w - mFun N σ w‖ = σ i * ThetaN σ Xm w := rfl
            have h2 := mul_le_mul_of_nonneg_left (hZi i) hσi.le
            nlinarith
          have hC0 : 0 ≤ mAsympUpper c τ + 1 :=
            add_nonneg ((inv_pos.2 hc).le.trans (le_max_left _ _)) zero_le_one
          rw [norm_div, norm_mul, norm_neg]
          calc ‖G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i)‖ * ‖(σ i : ℂ) * (mN (diagonal σ) Xm w
                - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i + giiErr σ Xm w i‖
                / ‖1 + (σ i : ℂ) * mFun N σ w‖
              ≤ (mAsympUpper c τ + 1) * σ i * (σ i * (ThetaN σ Xm w + (1 + weak_Cpsi τ) * r))
                / c := by
                gcongr
            _ = σ i * σ i * ((mAsympUpper c τ + 1) / c * (ThetaN σ Xm w
                + (1 + weak_Cpsi τ) * r)) := by
                field_simp
            _ ≤ σ i * σ i * (weak_Kg c τ * (r + ThetaN σ Xm w)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                unfold weak_Kg
                have hq : 0 ≤ (mAsympUpper c τ + 1) / c := by positivity
                have h4 : ThetaN σ Xm w + (1 + weak_Cpsi τ) * r
                    ≤ (1 + weak_Cpsi τ) * (r + ThetaN σ Xm w) := by nlinarith
                calc (mAsympUpper c τ + 1) / c * (ThetaN σ Xm w + (1 + weak_Cpsi τ) * r)
                    ≤ (mAsympUpper c τ + 1) / c * ((1 + weak_Cpsi τ) * (r + ThetaN σ Xm w)) :=
                      mul_le_mul_of_nonneg_left h4 hq
                  _ ≤ ((mAsympUpper c τ + 1) / c + 1) * (1 + weak_Cpsi τ)
                      * (r + ThetaN σ Xm w) := by nlinarith
            _ = weak_Kg c τ * (r + ThetaN σ Xm w) * (σ i * σ i) := by ring
      | inr ν =>
          simp only [mS, sigS, Sum.elim_inr, mul_one]
          have e := norm_sub_le_norm_sub_add_norm_sub
            (G (diagonal σ) Xm w (Sum.inr ν) (Sum.inr ν)) (mN (diagonal σ) Xm w) (mFun N σ w)
          have h1 := hmu ν
          have h2 : ‖mN (diagonal σ) Xm w - mFun N σ w‖ = ThetaN σ Xm w := rfl
          linarith
    · simp only [hst, ite_false, sub_zero]
      calc ‖G (diagonal σ) Xm w s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm w :=
            weak_offdiag_le hσ Xm w hst
        _ ≤ sigS σ s * sigS σ t * (weak_Kg c τ * (r + ThetaN σ Xm w)) := by
            gcongr
            linarith
        _ = _ := by ring

end Det

/-! ## The descent along the lattice -/

section Descent

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `Re z_k = Re z`. -/
private theorem weak_latticePt_re (N : ℕ) (z : ℂ) (k : ℕ) : (latticePt N z k).re = z.re := by
  rw [latticePt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `z_0 = z`. -/
private theorem weak_latticePt_zero (N : ℕ) (z : ℂ) : latticePt N z 0 = z := by
  simp [latticePt]

/-- `‖w − (w + i N⁻⁵)‖ / min(Im w, Im w + N⁻⁵)² ≤ N⁻³` on `𝐃(τ,N)`, `τ ≥ 0`. -/
private theorem weak_step_le {τ : ℝ} (hτ : 0 ≤ τ) (hN : 0 < N) {w : ℂ}
    (hw : w ∈ specDomain τ N) (hw' : shiftUp N w ∈ specDomain τ N) :
    ‖w - shiftUp N w‖ / min w.im (shiftUp N w).im ^ 2 ≤ ((N : ℝ) ^ 3)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlow : ∀ v ∈ specDomain τ N, (N : ℝ)⁻¹ ≤ v.im := fun v hv => by
    have h := hv.2.2.2.1
    have : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have hm : (N : ℝ)⁻¹ ≤ min w.im (shiftUp N w).im := le_min (hlow w hw) (hlow _ hw')
  have hd : ‖w - shiftUp N w‖ = ((N : ℝ) ^ 5)⁻¹ := by
    unfold shiftUp
    rw [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hm0 : 0 < min w.im (shiftUp N w).im := lt_of_lt_of_le (by positivity) hm
  rw [hd, div_le_iff₀ (by positivity)]
  calc ((N : ℝ) ^ 5)⁻¹ = ((N : ℝ) ^ 3)⁻¹ * ((N : ℝ)⁻¹) ^ 2 := by
        field_simp
    _ ≤ ((N : ℝ) ^ 3)⁻¹ * min w.im (shiftUp N w).im ^ 2 := by gcongr

/-- The continuity argument at one `ω`: on the good event along the lattice `z_k`,
`Λ(z) ≤ N^{2ε_r} Φ^{1/4}`. -/
private theorem weak_descent {τ c C₀ C₁ K₀ Cop εr : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hN : 0 < N)
    (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {S : Set ℂ} (hS : SpectralDomain τ N S) (hx : OneXmOn c N σ S)
    (hstab : StableOn C₀ C₁ K₀ N σ S) (hδ : AdmissibleDelta N S (weakDelta N (2 * εr)))
    {z : ℂ} (hz : z ∈ S) (hτN : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hlog1 : (Real.log N)⁻¹ ≤ 1)
    (hn1 : weak_A c τ * weak_Cpsi τ ≤ (N : ℝ) ^ εr)
    (hn2 : weak_Kg c τ * (weak_Cpsi τ + max (max C₀ C₁) 0) ≤ (N : ℝ) ^ εr)
    (hsmall : ∀ w ∈ specDomain τ N, (N : ℝ) ^ εr * (N : ℝ) ^ εr * PhiN N w ^ (1 / 4 : ℝ)
      + (2 + Cop + c⁻¹ ^ 2) * ((N : ℝ) ^ 3)⁻¹ ≤ (Real.log N)⁻¹)
    (hnorm : ‖Xmᵀ * Xm‖ ≤ Cop)
    (hZ : ∀ k ≤ latticeTop N z, ∀ s, xiInd σ Xm (latticePt N z k) *
      (‖ZS σ Xm (latticePt N z k) s‖ + LambdaO σ Xm (latticePt N z k)) ≤
        (N : ℝ) ^ εr * PsiTheta σ Xm (latticePt N z k))
    (hD : ∀ k ≤ latticeTop N z, xiInd σ Xm (latticePt N z k) *
      ‖calDErr σ Xm (latticePt N z k)‖ ≤ (N : ℝ) ^ εr * PsiTheta σ Xm (latticePt N z k) ^ 2)
    (hgii : ∀ k ≤ latticeTop N z, ∀ i, xiInd σ Xm (latticePt N z k) *
      ‖giiErr σ Xm (latticePt N z k) i‖ ≤
        (N : ℝ) ^ εr * (σ i * PsiTheta σ Xm (latticePt N z k) ^ 2))
    (hmu : ∀ k ≤ latticeTop N z, ∀ μ, xiInd σ Xm (latticePt N z k) *
      ‖G (diagonal σ) Xm (latticePt N z k) (Sum.inr μ) (Sum.inr μ) -
        mN (diagonal σ) Xm (latticePt N z k)‖ ≤ (N : ℝ) ^ εr * PsiTheta σ Xm (latticePt N z k))
    (htop : Lambda σ Xm (latticePt N z (latticeTop N z)) ≤ (Real.log N)⁻¹) :
    Lambda σ Xm z ≤ (N : ℝ) ^ εr * (N : ℝ) ^ εr * PhiN N z ^ (1 / 4 : ℝ) := by
  set K := latticeTop N z with hK
  set n := (N : ℝ) ^ εr with hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : 0 ≤ n := Real.rpow_nonneg hN0.le _
  have hP : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hmem : ∀ k ≤ K, latticePt N z k ∈ S := fun k hk => latticePt_mem hS hz hτN hk
  have hmemD : ∀ k ≤ K, latticePt N z k ∈ specDomain τ N := fun k hk => hS.1 (hmem k hk)
  set μ := empMeasure (specOf (Xmᵀ * diagonal σ * Xm)) with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_empMeasure _ hN
  have hrt : ∀ k ≤ K, resolventTransform μ (latticePt N z k) =
      mN (diagonal σ) Xm (latticePt N z k) :=
    fun k hk => (mN_eq_resolventTransform hP Xm (hmemD k hk).1).symm
  -- the bounds at a lattice point of `Ξ`
  have hpt : ∀ k ≤ K, Lambda σ Xm (latticePt N z k) ≤ (Real.log N)⁻¹ →
      ‖fC N σ (mN (diagonal σ) Xm (latticePt N z k)) - latticePt N z k‖ ≤
          weak_A c τ * (n * PsiTheta σ Xm (latticePt N z k)) ∧
        Lambda σ Xm (latticePt N z k) ≤
          weak_Kg c τ * (n * PsiTheta σ Xm (latticePt N z k) + ThetaN σ Xm (latticePt N z k)) ∧
        PsiTheta σ Xm (latticePt N z k) ≤ weak_Cpsi τ * √(PhiN N (latticePt N z k)) := by
    intro k hk hΞ
    have h1 : xiInd σ Xm (latticePt N z k) = 1 := by simp [xiInd, hΞ]
    have hw := hmemD k hk
    have hpt := weak_point hc hN da hσ Xm hw (hx _ (hmem k hk)) hlog hlog1 hΞ hn0
      (fun s => by have := hZ k hk s; rwa [h1, one_mul] at this)
      (by have := hD k hk; rwa [h1, one_mul] at this)
      (fun i => by have := hgii k hk i; rwa [h1, one_mul] at this)
      (fun μ => by have := hmu k hk μ; rwa [h1, one_mul] at this)
    exact ⟨hpt.1, hpt.2, weak_psi_le hN da hσ Xm hw hlog1 hΞ⟩
  -- `Ξ(z_k)` from the bound at `z_{k+1}` and the Lipschitz bound for `Λ`
  have hxi : ∀ k < K, Lambda σ Xm (latticePt N z (k + 1)) ≤
      n * n * PhiN N (latticePt N z (k + 1)) ^ (1 / 4 : ℝ) →
      Lambda σ Xm (latticePt N z k) ≤ (Real.log N)⁻¹ := by
    intro k hk hg
    have hk1 : k ≤ K := hk.le
    have hk2 : k + 1 ≤ K := hk
    have hsh := shiftUp_latticePt N z k
    have hw := hmemD k hk1
    have hw' := hmemD (k + 1) hk2
    have hlip := Lambda_lipschitz hN hσ Xm hc (z := latticePt N z k)
      (w := latticePt N z (k + 1)) (by rw [weak_latticePt_re, weak_latticePt_re]) hw.1 hw'.1
      (hx _ (hmem k hk1)) (hx _ (hmem _ hk2))
    have hstep := weak_step_le hτ.le hN hw (by rw [hsh]; exact hw')
    rw [hsh] at hstep
    have hq0 : 0 ≤ ‖latticePt N z k - latticePt N z (k + 1)‖ /
        min (latticePt N z k).im (latticePt N z (k + 1)).im ^ 2 := by positivity
    have hX0 := norm_nonneg (Xmᵀ * Xm)
    have h1 : (2 + ‖Xmᵀ * Xm‖ + c⁻¹ ^ 2) * ‖latticePt N z k - latticePt N z (k + 1)‖ /
        min (latticePt N z k).im (latticePt N z (k + 1)).im ^ 2 ≤
          (2 + Cop + c⁻¹ ^ 2) * ((N : ℝ) ^ 3)⁻¹ := by
      rw [mul_div_assoc]
      exact mul_le_mul (by linarith) hstep hq0 (by linarith [sq_nonneg c⁻¹])
    have h2 := hsmall _ hw'
    have h3 := (abs_sub_le_iff.1 hlip).1
    linarith
  -- the self-consistent bound `|f(m_N) − z_k| ≤ δ(z_k)` on `Ξ(z_k)`
  have hclose : ∀ k ≤ K, Lambda σ Xm (latticePt N z k) ≤ (Real.log N)⁻¹ →
      ‖fC N σ (resolventTransform μ (latticePt N z k)) - latticePt N z k‖ ≤
        weakDelta N (2 * εr) (latticePt N z k) := by
    intro k hk hΞ
    obtain ⟨hF, -, hψ⟩ := hpt k hk hΞ
    rw [hrt k hk]
    refine hF.trans ?_
    have hs0 : 0 ≤ √(PhiN N (latticePt N z k)) := Real.sqrt_nonneg _
    have hwd : weakDelta N (2 * εr) (latticePt N z k) = n * n * √(PhiN N (latticePt N z k)) := by
      rw [weakDelta, two_mul, Real.rpow_add hN0, Real.sqrt_eq_rpow]
    rw [hwd]
    have hA0 := weak_A_nonneg hτ hc
    calc weak_A c τ * (n * PsiTheta σ Xm (latticePt N z k))
        ≤ weak_A c τ * (n * (weak_Cpsi τ * √(PhiN N (latticePt N z k)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hψ hn0) hA0
      _ = weak_A c τ * weak_Cpsi τ * n * √(PhiN N (latticePt N z k)) := by ring
      _ ≤ n * n * √(PhiN N (latticePt N z k)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn1 hn0) hs0
  -- from stability at `z_k` to `Λ(z_k) ≤ n² Φ^{1/4}`
  have hgood : ∀ k ≤ K, Lambda σ Xm (latticePt N z k) ≤ (Real.log N)⁻¹ →
      ‖resolventTransform μ (latticePt N z k) - mFun N σ (latticePt N z k)‖ ≤
        weakBound C₀ C₁ K₀ N σ (weakDelta N (2 * εr)) (latticePt N z k) →
      Lambda σ Xm (latticePt N z k) ≤ n * n * PhiN N (latticePt N z k) ^ (1 / 4 : ℝ) := by
    intro k hk hΞ hB
    obtain ⟨-, hL, hψ⟩ := hpt k hk hΞ
    rw [hrt k hk] at hB
    have hw := hmemD k hk
    obtain ⟨hΦ0, -⟩ := weak_Phi_le hN hw
    set w := latticePt N z k with hwdef
    set q := PhiN N w ^ (1 / 4 : ℝ) with hq
    have hq0 : 0 ≤ q := Real.rpow_nonneg hΦ0 _
    have hq1 : q ≤ 1 := Real.rpow_le_one hΦ0 (weak_Phi_le_one hτ.le hN hw) (by norm_num)
    have hsq : √(PhiN N w) = q * q := (weak_quarter_sq hΦ0).symm
    have hδw : weakDelta N (2 * εr) w = (n * q) * (n * q) := by
      rw [weakDelta, two_mul, Real.rpow_add hN0, ← Real.sqrt_eq_rpow, hsq]
      ring
    have hnq : 0 ≤ n * q := mul_nonneg hn0 hq0
    have hθ : ThetaN σ Xm w ≤ max (max C₀ C₁) 0 * (n * q) := by
      have hmim : 0 ≤ (mFun N σ w).im := (mFun_spec N σ (fun i => (hσ i).le) hw.1).1.le
      have hd0 : 0 ≤ weakDelta N (2 * εr) w := by rw [hδw]; exact mul_self_nonneg _
      have h1 := twoRegime_le_max (C₀ := C₀) (C₁ := C₁) (K₀ := K₀) (κ := kappa N σ w.re)
        (η := w.im) hd0 hmim
      have hsqrt : √(weakDelta N (2 * εr) w) = n * q := by
        rw [hδw]
        exact Real.sqrt_mul_self hnq
      have hquot : weakDelta N (2 * εr) w / ((mFun N σ w).im + √(weakDelta N (2 * εr) w))
          ≤ n * q := by
        rw [hsqrt, hδw]
        rcases hnq.eq_or_lt with h0 | h0
        · rw [← h0]
          simp
        · rw [div_le_iff₀ (by linarith)]
          nlinarith
      have hquot0 : 0 ≤ weakDelta N (2 * εr) w /
          ((mFun N σ w).im + √(weakDelta N (2 * εr) w)) :=
        div_nonneg hd0 (add_nonneg hmim (Real.sqrt_nonneg _))
      calc ThetaN σ Xm w = ‖mN (diagonal σ) Xm w - mFun N σ w‖ := rfl
        _ ≤ weakBound C₀ C₁ K₀ N σ (weakDelta N (2 * εr)) w := hB
        _ ≤ max C₀ C₁ * (weakDelta N (2 * εr) w /
            ((mFun N σ w).im + √(weakDelta N (2 * εr) w))) := h1
        _ ≤ max (max C₀ C₁) 0 * (weakDelta N (2 * εr) w /
            ((mFun N σ w).im + √(weakDelta N (2 * εr) w))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hquot0
        _ ≤ max (max C₀ C₁) 0 * (n * q) := mul_le_mul_of_nonneg_left hquot (le_max_right _ _)
    have hCψ0 := weak_Cpsi_nonneg τ
    have hψ' : n * PsiTheta σ Xm w ≤ weak_Cpsi τ * (n * q) := by
      rw [hsq] at hψ
      have h1 : PsiTheta σ Xm w ≤ weak_Cpsi τ * q :=
        hψ.trans (mul_le_mul_of_nonneg_left (by nlinarith) hCψ0)
      calc n * PsiTheta σ Xm w ≤ n * (weak_Cpsi τ * q) := mul_le_mul_of_nonneg_left h1 hn0
        _ = weak_Cpsi τ * (n * q) := by ring
    have hKg0 : 0 ≤ weak_Kg c τ := zero_le_one.trans (weak_Kg_ge_one hc)
    calc Lambda σ Xm w ≤ weak_Kg c τ * (n * PsiTheta σ Xm w + ThetaN σ Xm w) := hL
      _ ≤ weak_Kg c τ * (weak_Cpsi τ * (n * q) + max (max C₀ C₁) 0 * (n * q)) :=
          mul_le_mul_of_nonneg_left (add_le_add hψ' hθ) hKg0
      _ = weak_Kg c τ * (weak_Cpsi τ + max (max C₀ C₁) 0) * (n * q) := by ring
      _ ≤ n * (n * q) := mul_le_mul_of_nonneg_right hn2 hnq
      _ = n * n * q := by ring
  have hdesc := stable_descent (B := weakBound C₀ C₁ K₀ N σ) hstab hδ μ z K hmem
    (one_le_im_latticeTop hN z) (fun k => Lambda σ Xm (latticePt N z k) ≤ (Real.log N)⁻¹)
    (fun k => Lambda σ Xm (latticePt N z k) ≤ n * n * PhiN N (latticePt N z k) ^ (1 / 4 : ℝ))
    htop hxi hclose hgood
  have h0 := (hdesc 0 (Nat.zero_le _)).1
  simp only [weak_latticePt_zero] at h0
  exact h0

end Descent

/-! ## Size conditions and the union bound -/

/-- The size conditions on `N`: `N ≥ 6`, `N ≥ 2(1 + τ⁻¹)`, `K₁ ≤ N^{ε_r}`,
`(log N)⁻¹ ≤ min(1, xiThr)`, `N^{−τ/8} + L N⁻³ ≤ (log N)⁻¹` and `1 + N⁻⁵ ≤ τ⁻¹` if `τ < 1`. -/
private theorem weak_threshold {τ c εr L K₁ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hεr : 0 < εr)
    (hL : 0 ≤ L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (6 : ℝ) ≤ N ∧ 2 * (1 + τ⁻¹) ≤ (N : ℝ) ∧ K₁ ≤ (N : ℝ) ^ εr ∧
      (Real.log N)⁻¹ ≤ xiThr c τ ∧ (Real.log N)⁻¹ ≤ 1 ∧
      (N : ℝ) ^ (-(τ / 8)) + L * ((N : ℝ) ^ 3)⁻¹ ≤ (Real.log N)⁻¹ ∧
      (τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1) := by
  have hξ : 0 < xiThr c τ := by
    have := weak_Cm_pos hτ
    unfold xiThr mAsympLower ThetaConst
    positivity
  have e1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 2 * ‖x ^ (τ / 8)‖ :=
    (isLittleO_log_rpow_atTop (by positivity)).def (by norm_num)
  have e2 : ∀ᶠ x : ℝ in atTop, max (max 6 (2 * (1 + τ⁻¹))) (2 * L + 1) ≤ x :=
    eventually_ge_atTop _
  have e3 : ∀ᶠ x : ℝ in atTop, max 1 (xiThr c τ)⁻¹ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have e4 : ∀ᶠ x : ℝ in atTop, K₁ ≤ x ^ εr := (tendsto_rpow_atTop hεr).eventually_ge_atTop _
  have e5 : ∀ᶠ x : ℝ in atTop, τ < 1 → (τ⁻¹ - 1)⁻¹ ≤ x :=
    (eventually_ge_atTop _).mono fun _ hx _ => hx
  have ev := tendsto_natCast_atTop_atTop.eventually ((((e1.and e2).and e3).and e4).and e5)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hN₀ N hN
  set x : ℝ := (N : ℝ) with hxdef
  have h6 : 6 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  have hτx : 2 * (1 + τ⁻¹) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
  have hLx : 2 * L + 1 ≤ x := le_trans (le_max_right _ _) h2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlg1 : 1 ≤ Real.log x := le_trans (le_max_left _ _) h3
  have hlg0 : 0 < Real.log x := by linarith
  refine ⟨h6, hτx, h4, ?_, inv_le_one_of_one_le₀ hlg1, ?_, ?_⟩
  · have := le_trans (le_max_right _ _) h3
    calc (Real.log x)⁻¹ ≤ ((xiThr c τ)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hξ) this
      _ = xiThr c τ := inv_inv _
  · have hp : 0 < x ^ (τ / 8) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlg0, abs_of_pos hp] at h1
    have ha : Real.log x * x ^ (-(τ / 8)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_le_iff₀ hp]
      linarith
    have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
    have hb : Real.log x * (L * (x ^ 3)⁻¹) ≤ 1 / 2 := by
      rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have hxx : 2 * L ≤ x * x := by nlinarith
      have h7 : x * (2 * L) ≤ x * (x * x) := mul_le_mul_of_nonneg_left hxx hx0.le
      nlinarith
    have key : (x ^ (-(τ / 8)) + L * (x ^ 3)⁻¹) * Real.log x ≤ 1 := by nlinarith
    calc x ^ (-(τ / 8)) + L * (x ^ 3)⁻¹
        = (x ^ (-(τ / 8)) + L * (x ^ 3)⁻¹) * Real.log x * (Real.log x)⁻¹ := by
          field_simp
      _ ≤ 1 * (Real.log x)⁻¹ := by gcongr
      _ = (Real.log x)⁻¹ := one_mul _
  · intro hτ1
    have hpos : 0 < τ⁻¹ - 1 := by linarith [(one_lt_inv₀ hτ).2 hτ1]
    have h8 := h5 hτ1
    calc (x ^ 5)⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 (le_self_pow₀ hx1 (by norm_num))
      _ ≤ ((τ⁻¹ - 1)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hpos) h8
      _ = τ⁻¹ - 1 := inv_inv _

/-- `(K + 1) a ≤ N⁹` for `K + 1 ≤ N⁵ + 2`, `a ≤ M + N`, `M ≤ τ⁻¹ N`, `N ≥ 6` and
`N ≥ 2(1 + τ⁻¹)`. -/
private theorem weak_card {τ : ℝ} {N K a : ℕ} (hK : (K : ℝ) + 1 ≤ (N : ℝ) ^ 5 + 2)
    (ha : (a : ℝ) ≤ M + N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (h6 : (6 : ℝ) ≤ N)
    (hτN : 2 * (1 + τ⁻¹) ≤ (N : ℝ)) :
    (((K + 1) * a : ℕ) : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
  have e : (N : ℝ) ^ (9 : ℝ) = (N : ℝ) ^ (9 : ℕ) := by exact_mod_cast Real.rpow_natCast (N : ℝ) 9
  rw [e]
  push_cast
  set x : ℝ := (N : ℝ)
  have hx1 : 1 ≤ x := by linarith
  have h5 : x ≤ x ^ 5 := le_self_pow₀ hx1 (by norm_num)
  have hK' : (K : ℝ) + 1 ≤ 2 * x ^ 5 := by linarith
  have ha' : (a : ℝ) ≤ x * x / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hτN (by linarith : (0 : ℝ) ≤ x)]
  calc ((K : ℝ) + 1) * a ≤ (2 * x ^ 5) * (x * x / 2) :=
        mul_le_mul hK' ha' (Nat.cast_nonneg _) (by positivity)
    _ = x ^ 7 := by ring
    _ ≤ x ^ 9 := pow_le_pow_right₀ hx1 (by norm_num)

/-- Six events of probability at most `N^{−D−1}` each: their union has probability at most
`N^{−D}` once `N ≥ 6`. -/
private theorem weak_union {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : (6 : ℝ) ≤ N)
    {A B₁ B₂ B₃ B₄ B₅ B₆ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₄ : ℙ B₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₅ : ℙ B₅ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₆ : ℙ B₆ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hsub : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃ ∨ ω ∈ B₄ ∨ ω ∈ B₅ ∨ ω ∈ B₆) :
    ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hsub' : A ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ := by
    intro ω hω
    rcases hsub ω hω with h | h | h | h | h | h <;> simp [h]
  set x := ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) with hx
  have hN0 : (0 : ℝ) < N := by linarith
  calc ℙ A ≤ ℙ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆) := measure_mono hsub'
    _ ≤ ℙ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) + ℙ B₆ := measure_union_le _ _
    _ ≤ ℙ (B₁ ∪ B₂ ∪ B₃ ∪ B₄) + ℙ B₅ + ℙ B₆ := by gcongr; exact measure_union_le _ _
    _ ≤ ℙ (B₁ ∪ B₂ ∪ B₃) + ℙ B₄ + ℙ B₅ + ℙ B₆ := by gcongr; exact measure_union_le _ _
    _ ≤ ℙ (B₁ ∪ B₂) + ℙ B₃ + ℙ B₄ + ℙ B₅ + ℙ B₆ := by gcongr; exact measure_union_le _ _
    _ ≤ ℙ B₁ + ℙ B₂ + ℙ B₃ + ℙ B₄ + ℙ B₅ + ℙ B₆ := by gcongr; exact measure_union_le _ _
    _ ≤ x + x + x + x + x + x := by gcongr
    _ = ENNReal.ofReal (6 * (N : ℝ) ^ (-(D + 1))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← hx]
        ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 := Real.rpow_nonneg hN0.le (-D)
        have hN6 : 6 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]
          exact hN
        nlinarith

/-! # Proposition 5.1 (`prop:weak law`) -/

/-- Proposition 5.1 (weak entrywise law). -/
theorem weak_law (τ c C₀ C₁ K₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S →
      ∀ z ∈ S, DomAt N ε D (fun ω => Lambda σ (X ω) z) (fun _ => PhiN N z ^ (1 / 4 : ℝ)) := by
  rcases lt_or_ge 1 τ with hτ1 | hτ1
  · -- `τ > 1`: `τ ≤ M/N ≤ τ⁻¹` is impossible
    refine ⟨0, fun N _ Ω _ _ M σ X S hD _ _ _ z _ => ?_⟩
    exfalso
    have h1 := hD.ratio_ge.trans hD.ratio_le
    have h2 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ1
    linarith
  set εr := min ε τ / 16 with hεr
  have hmin0 : 0 < min ε τ := lt_min hε hτ
  have hεr0 : 0 < εr := by positivity
  have hεrε : εr ≤ ε / 16 := by
    have := min_le_left ε τ
    rw [hεr]
    linarith
  have hεrτ : εr ≤ τ / 16 := by
    have := min_le_right ε τ
    rw [hεr]
    linarith
  obtain ⟨Cop, hCop⟩ := norm_XtX_le hτ hτ1
  set L := 2 + max Cop 0 + c⁻¹ ^ 2 with hL
  have hL0 : 0 ≤ L := by linarith [le_max_right Cop 0, sq_nonneg c⁻¹]
  set K₁ := max (weak_A c τ * weak_Cpsi τ) (weak_Kg c τ * (weak_Cpsi τ + max (max C₀ C₁) 0))
    with hK₁def
  obtain ⟨N₁, h₁⟩ := lambdaO_Z_bound τ c C εr (D + 1 + 9) hτ hc hεr0
  obtain ⟨N₂, h₂⟩ := calD_bound τ c C εr (D + 1 + 9) hτ hc hεr0
  obtain ⟨N₃, h₃⟩ := Gii_2 τ c C εr (D + 1 + 9) hτ hc hεr0
  obtain ⟨N₄, h₄⟩ := Gmumu_m τ c C εr (D + 1 + 9) hτ hc hεr0
  obtain ⟨N₅, h₅⟩ := initial_bound τ c C εr (D + 1) hτ hc hεr0
  obtain ⟨N₆, h₆⟩ := hCop C (D + 1)
  obtain ⟨N₇, h₇⟩ := admissible_weakDelta hτ (a := 2 * εr) (by positivity) (by linarith)
  obtain ⟨N₈, h₈⟩ := weak_threshold (L := L) (K₁ := K₁) hτ hc hεr0 hL0
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈,
    fun N hN Ω _ _ M σ X S hD hS hx hstab z hz => ?_⟩
  obtain ⟨h6, hτN2, hK₁, hlog, hlog1, hsm, hτ5⟩ := h₈ N (by omega)
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN1'
  have hNpos : 0 < N := hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have da := hD.densityAssumptions hτ
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hD.ratio_le
    rwa [div_le_iff₀ hN0] at this
  have hzD : z ∈ specDomain τ N := hS.1 hz
  have hτN : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ := by
    intro him
    have hτlt : τ < 1 := by
      by_contra h
      push Not at h
      have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) := Real.one_le_rpow hN1' (by linarith)
      linarith [hzD.2.2.2.1]
    linarith [hτ5 hτlt]
  set K := latticeTop N z with hK
  set n := (N : ℝ) ^ εr with hn
  have hKN : (K : ℝ) + 1 ≤ (N : ℝ) ^ 5 + 2 := latticeTop_add_one_le hNpos hzD.1
  have hmem : ∀ k ≤ K, latticePt N z k ∈ S := fun k hk => latticePt_mem hS hz hτN hk
  have hmemD : ∀ k ≤ K, latticePt N z k ∈ specDomain τ N := fun k hk => hS.1 (hmem k hk)
  have hk_of : ∀ {ι : Type} (p : ℕ × ι) (s : Finset ι), p ∈ Finset.range (K + 1) ×ˢ s →
      p.1 ≤ K := fun p s hp => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_product.1 hp).1)
  have hk_of' : ∀ k ∈ Finset.range (K + 1), k ≤ K := fun k hk =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  -- the index sets have at most `N⁹` elements
  have hc1 : ((Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin M ⊕ Fin N))).card : ℝ) ≤
      (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    exact weak_card hKN (by push_cast; linarith) hMN h6 hτN2
  have hc2 : ((Finset.range (K + 1)).card : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
    have := weak_card (a := 1) hKN (by push_cast; linarith) hMN h6 hτN2
    rw [Finset.card_range]
    simpa using this
  have hc3 : ((Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin M))).card : ℝ) ≤
      (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact weak_card hKN (by linarith) hMN h6 hτN2
  have hc4 : ((Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin N))).card : ℝ) ≤
      (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact weak_card hKN (by linarith) hMN h6 hτN2
  -- the six events
  have P1 := DomAt.measure_exists_lt (D := D + 1) (C := 9)
    (Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin M ⊕ Fin N))) hN1 hc1
    (ξ := fun p ω => xiInd σ (X ω) (latticePt N z p.1) *
      (‖ZS σ (X ω) (latticePt N z p.1) p.2‖ + LambdaO σ (X ω) (latticePt N z p.1)))
    (ζ := fun p ω => PsiTheta σ (X ω) (latticePt N z p.1))
    (fun p hp => h₁ N (by omega) M σ X hD _ (hmemD _ (hk_of p _ hp))
      (hx _ (hmem _ (hk_of p _ hp))) p.2)
  have P2 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (K + 1)) hN1 hc2
    (ξ := fun k ω => xiInd σ (X ω) (latticePt N z k) * ‖calDErr σ (X ω) (latticePt N z k)‖)
    (ζ := fun k ω => PsiTheta σ (X ω) (latticePt N z k) ^ 2)
    (fun k hk => h₂ N (by omega) M σ X hD _ (hmemD _ (hk_of' k hk)) (hx _ (hmem _ (hk_of' k hk))))
  have P3 := DomAt.measure_exists_lt (D := D + 1) (C := 9)
    (Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin M))) hN1 hc3
    (ξ := fun p ω => xiInd σ (X ω) (latticePt N z p.1) *
      ‖giiErr σ (X ω) (latticePt N z p.1) p.2‖)
    (ζ := fun p ω => σ p.2 * PsiTheta σ (X ω) (latticePt N z p.1) ^ 2)
    (fun p hp => h₃ N (by omega) M σ X hD _ (hmemD _ (hk_of p _ hp))
      (hx _ (hmem _ (hk_of p _ hp))) p.2)
  have P4 := DomAt.measure_exists_lt (D := D + 1) (C := 9)
    (Finset.range (K + 1) ×ˢ (Finset.univ : Finset (Fin N))) hN1 hc4
    (ξ := fun p ω => xiInd σ (X ω) (latticePt N z p.1) *
      ‖G (diagonal σ) (X ω) (latticePt N z p.1) (Sum.inr p.2) (Sum.inr p.2) -
        mN (diagonal σ) (X ω) (latticePt N z p.1)‖)
    (ζ := fun p ω => PsiTheta σ (X ω) (latticePt N z p.1))
    (fun p hp => h₄ N (by omega) M σ X hD _ (hmemD _ (hk_of p _ hp))
      (hx _ (hmem _ (hk_of p _ hp))) p.2)
  have P5 := h₆ N (by omega) M X hD.entries hMN
  have P6 := h₅ N (by omega) M σ X hD (latticePt N z K) (hmemD K le_rfl)
    (one_le_im_latticeTop hNpos z) (hx _ (hmem K le_rfl))
  unfold HighProbAt at P5
  unfold DomAt at P6 ⊢
  -- the deterministic inputs
  have hsmall : ∀ w ∈ specDomain τ N, n * n * PhiN N w ^ (1 / 4 : ℝ) +
      (2 + max Cop 0 + c⁻¹ ^ 2) * ((N : ℝ) ^ 3)⁻¹ ≤ (Real.log N)⁻¹ := by
    intro w hw
    obtain ⟨hΦ0, hΦ⟩ := weak_Phi_le hNpos hw
    have h1 : PhiN N w ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (-τ * (1 / 4)) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow hΦ0 hΦ (by norm_num)
    have h2 : n * n * (N : ℝ) ^ (-τ * (1 / 4)) ≤ (N : ℝ) ^ (-(τ / 8)) := by
      rw [hn, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hnn : 0 ≤ n * n := by positivity
    linarith [(mul_le_mul_of_nonneg_left h1 hnn).trans h2]
  have hnε : n * n ≤ (N : ℝ) ^ ε := by
    rw [hn, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hq0 : 0 ≤ PhiN N z ^ (1 / 4 : ℝ) := Real.rpow_nonneg (weak_Phi_le hNpos hzD).1 _
  refine weak_union h6 P1 P2 P3 P4 P5 P6 (fun ω hω => ?_)
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt, Set.mem_compl_iff,
    not_not] at n1 n2 n3 n4 n5 n6 hω
  have htop : Lambda σ (X ω) (latticePt N z K) ≤ (Real.log N)⁻¹ := by
    have h1 : n * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(τ / 8)) := by
      rw [hn, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h2 : 0 ≤ L * ((N : ℝ) ^ 3)⁻¹ := by positivity
    linarith
  have hdet := weak_descent (Cop := max Cop 0) hτ hc hNpos da hD.pos (X ω) hS hx hstab
    (h₇ N (by omega) S hS.1) hz hτN hlog hlog1 (le_trans (le_max_left _ _) hK₁)
    (le_trans (le_max_right _ _) hK₁) hsmall (n5.trans (le_max_left _ _))
    (fun k hk s => n1 (k, s) (Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega),
      Finset.mem_univ _⟩))
    (fun k hk => n2 k (Finset.mem_range.2 (by omega)))
    (fun k hk i => n3 (k, i) (Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega),
      Finset.mem_univ _⟩))
    (fun k hk μ => n4 (k, μ) (Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega),
      Finset.mem_univ _⟩))
    htop
  have := mul_le_mul_of_nonneg_right hnε hq0
  linarith

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `S = {2i}` -/

section Checks

/-- Proposition 5.1 at `τ = 1/2`, `c = 1`, `C₀ = C₁ = 4`, `K₀ = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X → SpectralDomain (1 / 2) N S → OneXmOn 1 N σ S →
    StableOn 4 4 1 N σ S →
    ∀ z ∈ S, DomAt N 1 1 (fun ω => Lambda σ (X ω) z) (fun _ => PhiN N z ^ (1 / 4 : ℝ)) :=
  weak_law (1 / 2) 1 4 4 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

end Checks

end Anisotropic

#print axioms Anisotropic.weak_law
