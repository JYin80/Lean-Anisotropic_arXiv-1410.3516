module

public import Anisotropic.Entrywise.SelfCons
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Probability.NormBound.Main

@[expose] public section

/-! # Lemma 5.5: the initial estimate `Λ ≺ N^{−1/2}` for `η ≥ 1`

`Σ = diag(σ)`, at fixed `N`, pointwise in `z ∈ 𝐃(τ,N)` with `Im z ≥ 1`.

For `η ≥ 1`, (opbound) gives `|G_{ss}| ≤ K_op σ̲_s` deterministically, and
(Lambda_o_Z_bound_initial) gives `|Z_s| + Λ_o ≤ N^e Ψ_Θ ≤ r := N^e (K_ψ/N)^{1/2}`.
With `B = −z − N⁻¹ Σ_i G_{ii}`, `A_i = 1 + m_N σ_i` and
`ρ_i = N⁻¹ Σ_μ G_{μi} G_{iμ} − G_{ii} Z_i`, (Gii_exp), (Gmumu_exp) and (Gstu) give the exact
identities `B G_{νν} − 1 = G_{νν} Z_ν − N⁻¹ Σ_i G_{iν} G_{νi}` and `G_{ii} A_i = σ_i (ρ_i − 1)`.
Hence `|B m_N − 1| = O(r)`, `|A_i| ≥ (2K_op)⁻¹`, and
`f(m_N) − z = (B − 1/m_N) + N⁻¹ Σ_i σ_i ρ_i / A_i = O(r)`. Since `Im z ≥ 1`, the case `Im z ≥ h`
of Lemma A.5 (`h = 1`) gives `|m_N − m| ≤ 2 |f(m_N) − z|` without any stability assumption, and
`Λ = O(r)` follows from
`G_{ii} − m_i = σ_i ρ_i / A_i + σ_i² (m_N − m) / (A_i (1 + σ_i m))` and
`G_{νν} − m_N = N⁻¹ Σ_μ (G_{νν} − G_{μμ})`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Constants -/

/-- `K_op = 1 + 10 τ⁻¹`: `|G_{ss}| ≤ K_op σ̲_s` for `η ≥ 1` on `𝐃(τ,N)`. -/
private def initial_Kop (τ : ℝ) : ℝ := 1 + 10 * τ⁻¹

/-- The constant of `|ρ_i| ≤ σ_i L r` and `|B G_{νν} − 1| ≤ L r`. -/
private def initial_L (τ : ℝ) : ℝ := initial_Kop τ + τ⁻¹ + τ⁻¹ ^ 3

/-- The bound `|B| ≤ K_B`. -/
private def initial_KB (τ : ℝ) : ℝ := 2 * τ⁻¹ + τ⁻¹ ^ 2 * initial_Kop τ

/-- The constant of `|f(m_N) − z| ≤ F r`. -/
private def initial_F (τ : ℝ) : ℝ :=
  2 * initial_KB τ * initial_L τ + 2 * initial_Kop τ * initial_L τ * τ⁻¹ ^ 3

/-- The smallness condition is `2 S r ≤ 1`. -/
private def initial_S (τ : ℝ) : ℝ := 1 + τ⁻¹ * initial_L τ + initial_L τ + initial_F τ

/-- The constant of `Λ ≤ K_Λ r`. -/
private def initial_KL (c τ : ℝ) : ℝ :=
  1 + 6 * initial_Kop τ * initial_L τ + 2 * initial_F τ
    + 4 * initial_Kop τ * initial_F τ / c

/-- The constant of `Ψ_Θ ≤ (K_ψ / N)^{1/2}`. -/
private def initial_Kpsi (c τ : ℝ) : ℝ :=
  2 * mBoundConst τ + initial_Kop τ + initial_Kop τ * τ⁻¹ + τ⁻¹ / c

private theorem initial_Kop_ge {τ : ℝ} (hτ : 0 < τ) : 1 ≤ initial_Kop τ := by
  unfold initial_Kop
  have := (inv_pos.2 hτ).le
  linarith

private theorem initial_L_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ initial_L τ := by
  have := initial_Kop_ge hτ
  unfold initial_L
  positivity

private theorem initial_KB_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ initial_KB τ := by
  have := initial_Kop_ge hτ
  unfold initial_KB
  positivity

private theorem initial_F_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ initial_F τ := by
  have := initial_Kop_ge hτ
  have := initial_L_nonneg hτ
  have := initial_KB_nonneg hτ
  unfold initial_F
  positivity

private theorem initial_S_ge {τ : ℝ} (hτ : 0 < τ) : 1 ≤ initial_S τ := by
  have := initial_L_nonneg hτ
  have := initial_F_nonneg hτ
  have : 0 ≤ τ⁻¹ * initial_L τ := by positivity
  unfold initial_S
  linarith

private theorem initial_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

private theorem initial_KL_nonneg {c τ : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 0 ≤ initial_KL c τ := by
  have := initial_Kop_ge hτ
  have := initial_L_nonneg hτ
  have := initial_F_nonneg hτ
  unfold initial_KL
  positivity

private theorem initial_Kpsi_nonneg {c τ : ℝ} (hτ : 0 < τ) (hc : 0 < c) :
    0 ≤ initial_Kpsi c τ := by
  have := initial_Kop_ge hτ
  have := initial_Cm_pos hτ
  unfold initial_Kpsi
  positivity

/-! ## Deterministic bounds -/

section Det

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `σ̲_s > 0`. -/
private theorem initial_sigS_pos (hσ : ∀ i, 0 < σ i) (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `|z| ≤ 2 τ⁻¹` on `𝐃(τ,N)`. -/
private theorem initial_norm_z {τ : ℝ} {z : ℂ} (hz : z ∈ specDomain τ N) : ‖z‖ ≤ 2 * τ⁻¹ := by
  obtain ⟨h0, -, hre, -, him⟩ := hz
  have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos h0] at h1
  linarith

/-- `(1 + 5|z|)/η ≤ K_op` on `𝐃(τ,N)` with `η ≥ 1`. -/
private theorem initial_Kz {τ : ℝ} {z : ℂ} (hτ : 0 < τ) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) : (1 + 5 * ‖z‖) / z.im ≤ initial_Kop τ := by
  have h1 := initial_norm_z hz
  have h0 : 0 < z.im := hz.1
  rw [div_le_iff₀ h0]
  unfold initial_Kop
  have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  nlinarith [mul_nonneg hτi (sub_nonneg.2 hη), norm_nonneg z]

/-- (opbound) for `η ≥ 1`: `|G_{ss}| ≤ K_op σ̲_s`. -/
private theorem initial_diag_le {τ : ℝ} (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im)
    (s : Fin M ⊕ Fin N) : ‖G (diagonal σ) Xm z s s‖ ≤ initial_Kop τ * sigS σ s := by
  have hs := initial_sigS_pos (N := N) hσ s
  have hP : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hb := opbound hP Xm hz.1 (eI s) (eI s)
  rw [ent_eI_eI] at hb
  have hq : eI s ⬝ᵥ SigU (n := Fin N) (diagonal σ) *ᵥ eI s = sigS σ s := by
    have : eI s ⬝ᵥ SigU (n := Fin N) (diagonal σ) *ᵥ eI s
        = SigU (n := Fin N) (diagonal σ) s s := by
      simp [eI, dotProduct, mulVec, Pi.single_apply]
    rw [this]
    cases s with
    | inl i => simp [SigU, sigS]
    | inr μ => simp [SigU, sigS]
  rw [hq, mul_assoc, Real.mul_self_sqrt hs.le] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (initial_Kz hτ hz hη) hs.le)

/-- `Λ_o ≥ 0`. -/
private theorem initial_LambdaO_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) : 0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (initial_sigS_pos hσ _) (initial_sigS_pos hσ _)).le

/-- `|G_{st}| ≤ σ̲_s σ̲_t Λ_o` for `s ≠ t`. -/
private theorem initial_offdiag_le (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (initial_sigS_pos hσ s) (initial_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
    unfold LambdaO
    exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `‖N⁻¹ Σ_j f_j‖ ≤ (#ι / N) K` when every `‖f_j‖ ≤ K`. -/
private theorem initial_avg_le {ι : Type*} [Fintype ι] (hN : 0 < N) (f : ι → ℂ) {K : ℝ}
    (hK : ∀ j, ‖f j‖ ≤ K) :
    ‖(N : ℂ)⁻¹ * ∑ j, f j‖ ≤ (Fintype.card ι : ℝ) / N * K := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, f j‖ ≤ (N : ℝ)⁻¹ * ∑ _j : ι, K := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hK j)
    _ = (Fintype.card ι : ℝ) / N * K := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- `B = −z − N⁻¹ Σ_i G_{ii}`. -/
private def initial_B (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  -z - (N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)

/-- `ρ_i = N⁻¹ Σ_μ G_{μi} G_{iμ} − G_{ii} Z_i`. -/
private def initial_rho (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) : ℂ :=
  (N : ℂ)⁻¹ * ∑ μ, G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
      * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
    - G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) * Zi σ Xm z i

/-- From (Gmumu_exp) and (Gstu): `B G_{νν} − 1 = G_{νν} Z_ν − N⁻¹ Σ_i G_{iν} G_{νi}`. -/
private theorem initial_mu_id (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (ν : Fin N) :
    initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - 1
      = G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) * Zmu σ Xm z ν
        - (N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν)
          * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i) := by
  have e1 := Gmumu_exp hσ Xm hz ν
  have e2 : ∀ i : Fin M, G1 (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i) (Sum.inl i)
      = G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)
        - G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν) * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i)
          / G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) := fun i =>
    Gstu (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inr ν) (Sum.inl i) (Sum.inl i) (by simp) (by simp)
  simp only [e2, Finset.sum_sub_distrib, ← Finset.sum_div] at e1
  have h0 := G_diag_ne_zero (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inr ν)
  unfold initial_B
  field_simp at e1
  linear_combination -e1

/-- From (Gii_exp) and (Gstu): `G_{ii} (1 + m_N σ_i) = σ_i (ρ_i − 1)`. -/
private theorem initial_i_id (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (i : Fin M) :
    G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) * (1 + mN (diagonal σ) Xm z * σ i)
      = σ i * (initial_rho σ Xm z i - 1) := by
  have e1 := Gii_exp hσ Xm hz i
  have e2 : ∀ μ : Fin N, G1 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr μ)
      = G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
          / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) := fun μ =>
    Gstu (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inl i) (Sum.inr μ) (Sum.inr μ) (by simp) (by simp)
  simp only [e2, Finset.sum_sub_distrib, ← Finset.sum_div] at e1
  have h0 := G_diag_ne_zero (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inl i)
  have hσ0 : (σ i : ℂ) ≠ 0 := by exact_mod_cast (hσ i).ne'
  unfold initial_rho mN
  field_simp at e1
  linear_combination e1

/-- The deterministic setting at a point `ω` of the good event: `|Z_s| ≤ r`, `Λ_o ≤ r` and
`2 S r ≤ 1`. -/
private structure initial_Ctx (τ c : ℝ) (N : ℕ) (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (r : ℝ) : Prop where
  hτ : 0 < τ
  hc : 0 < c
  hN : 0 < N
  pos : ∀ i, 0 < σ i
  le : ∀ i, σ i ≤ τ⁻¹
  ratio : (M : ℝ) / N ≤ τ⁻¹
  hz : z ∈ specDomain τ N
  hη : 1 ≤ z.im
  hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖
  hr0 : 0 ≤ r
  hrS : 2 * initial_S τ * r ≤ 1
  hZ : ∀ s, ‖ZS σ Xm z s‖ ≤ r
  hLo : LambdaO σ Xm z ≤ r

namespace initial_Ctx

variable {τ c r : ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

private theorem gdiag (h : initial_Ctx τ c N σ Xm z r) (s : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z s s‖ ≤ initial_Kop τ * sigS σ s :=
  initial_diag_le h.hτ h.pos Xm h.hz h.hη s

private theorem gi (h : initial_Ctx τ c N σ Xm z r) (i : Fin M) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ ≤ initial_Kop τ * σ i := by
  simpa [sigS] using h.gdiag (Sum.inl i)

private theorem gmu (h : initial_Ctx τ c N σ Xm z r) (μ : Fin N) :
    ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ ≤ initial_Kop τ := by
  simpa [sigS] using h.gdiag (Sum.inr μ)

private theorem small (h : initial_Ctx τ c N σ Xm z r) :
    r ≤ 1 ∧ τ⁻¹ * initial_L τ * r ≤ 1 / 2 ∧ initial_L τ * r ≤ 1 / 2 ∧
      initial_F τ * r ≤ 1 / 2 := by
  have hτ := h.hτ
  have hL := initial_L_nonneg hτ
  have hF := initial_F_nonneg hτ
  have h1 : 0 ≤ τ⁻¹ * initial_L τ := by positivity
  have hr := h.hr0
  have hS := h.hrS
  unfold initial_S at hS
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem zi (h : initial_Ctx τ c N σ Xm z r) (i : Fin M) : ‖Zi σ Xm z i‖ ≤ r := by
  simpa [ZS] using h.hZ (Sum.inl i)

private theorem zmu (h : initial_Ctx τ c N σ Xm z r) (μ : Fin N) : ‖Zmu σ Xm z μ‖ ≤ r := by
  simpa [ZS] using h.hZ (Sum.inr μ)

/-- `|N⁻¹ Σ_i G_{iν} G_{νi}| ≤ τ⁻³ r`. -/
private theorem sum_i (h : initial_Ctx τ c N σ Xm z r) (ν : Fin N) :
    ‖(N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν)
      * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i)‖ ≤ τ⁻¹ ^ 3 * r := by
  have hτ := h.hτ
  have hr := h.hr0
  have hr1 := h.small.1
  have hterm : ∀ i : Fin M, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν)
      * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i)‖ ≤ τ⁻¹ ^ 2 * r := by
    intro i
    have h1 := initial_offdiag_le h.pos Xm z (s := Sum.inl i) (t := Sum.inr ν) (by simp)
    have h2 := initial_offdiag_le h.pos Xm z (s := Sum.inr ν) (t := Sum.inl i) (by simp)
    simp only [sigS, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one] at h1 h2
    have hσi := h.pos i
    have hσle := h.le i
    have hLo := h.hLo
    rw [norm_mul]
    calc ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν)‖
          * ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i)‖
        ≤ (τ⁻¹ * r) * (τ⁻¹ * r) := by
          have hLo0 : 0 ≤ LambdaO σ Xm z := initial_LambdaO_nonneg h.pos Xm z
          have a1 : σ i * LambdaO σ Xm z ≤ τ⁻¹ * r := mul_le_mul hσle hLo hLo0 (by positivity)
          exact mul_le_mul (h1.trans a1) (h2.trans a1) (norm_nonneg _) (by positivity)
      _ ≤ τ⁻¹ ^ 2 * r := by
          have : r * r ≤ r := by nlinarith
          calc τ⁻¹ * r * (τ⁻¹ * r) = τ⁻¹ ^ 2 * (r * r) := by ring
            _ ≤ τ⁻¹ ^ 2 * r := by gcongr
  have havg := initial_avg_le h.hN _ hterm
  rw [Fintype.card_fin] at havg
  refine havg.trans ?_
  calc (M : ℝ) / N * (τ⁻¹ ^ 2 * r) ≤ τ⁻¹ * (τ⁻¹ ^ 2 * r) := by
        gcongr
        exact h.ratio
    _ = τ⁻¹ ^ 3 * r := by ring

/-- `|B G_{νν} − 1| ≤ L r`. -/
private theorem bg (h : initial_Ctx τ c N σ Xm z r) (ν : Fin N) :
    ‖initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - 1‖
      ≤ initial_L τ * r := by
  rw [initial_mu_id h.pos Xm h.hz.1 ν]
  have h1 := h.sum_i ν
  have h2 : ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) * Zmu σ Xm z ν‖
      ≤ initial_Kop τ * r := by
    rw [norm_mul]
    exact mul_le_mul (h.gmu ν) (h.zmu ν) (norm_nonneg _)
      (zero_le_one.trans (initial_Kop_ge h.hτ))
  have h3 := norm_sub_le (G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) * Zmu σ Xm z ν)
    ((N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inr ν)
      * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inl i))
  have : 0 ≤ τ⁻¹ * r := mul_nonneg (inv_pos.2 h.hτ).le h.hr0
  unfold initial_L
  nlinarith

/-- `|ρ_i| ≤ σ_i L r`. -/
private theorem rho (h : initial_Ctx τ c N σ Xm z r) (i : Fin M) :
    ‖initial_rho σ Xm z i‖ ≤ σ i * (initial_L τ * r) := by
  have hτ := h.hτ
  have hr := h.hr0
  have hr1 := h.small.1
  have hσi := h.pos i
  have hσle := h.le i
  have hterm : ∀ μ : Fin N, ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
      * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖ ≤ σ i * (τ⁻¹ * r) := by
    intro μ
    have h1 := initial_offdiag_le h.pos Xm z (s := Sum.inr μ) (t := Sum.inl i) (by simp)
    have h2 := initial_offdiag_le h.pos Xm z (s := Sum.inl i) (t := Sum.inr μ) (by simp)
    simp only [sigS, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one] at h1 h2
    have hLo := h.hLo
    have hLo0 : 0 ≤ LambdaO σ Xm z := initial_LambdaO_nonneg h.pos Xm z
    rw [norm_mul]
    have a1 : σ i * LambdaO σ Xm z ≤ σ i * r := mul_le_mul_of_nonneg_left hLo hσi.le
    calc ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)‖
          * ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖
        ≤ (σ i * r) * (σ i * r) :=
          mul_le_mul (h1.trans a1) (h2.trans a1) (norm_nonneg _) (by positivity)
      _ = σ i * (σ i * (r * r)) := by ring
      _ ≤ σ i * (τ⁻¹ * r) := by
          have h3 : r * r ≤ r := by nlinarith
          have h4 : σ i * (r * r) ≤ τ⁻¹ * r :=
            mul_le_mul hσle h3 (by positivity) (inv_pos.2 hτ).le
          exact mul_le_mul_of_nonneg_left h4 hσi.le
  have havg := initial_avg_le h.hN _ hterm
  rw [Fintype.card_fin, div_self (by exact_mod_cast h.hN.ne' : (N : ℝ) ≠ 0), one_mul] at havg
  have h2 : ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) * Zi σ Xm z i‖
      ≤ σ i * (initial_Kop τ * r) := by
    rw [norm_mul]
    calc ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ * ‖Zi σ Xm z i‖
        ≤ (initial_Kop τ * σ i) * r :=
          mul_le_mul (h.gi i) (h.zi i) (norm_nonneg _) (by
            have := initial_Kop_ge hτ; positivity)
      _ = σ i * (initial_Kop τ * r) := by ring
  unfold initial_rho
  refine (norm_sub_le _ _).trans ?_
  have : 0 ≤ σ i * (τ⁻¹ ^ 3 * r) := by positivity
  unfold initial_L
  nlinarith

/-- `|B| ≤ K_B`. -/
private theorem B_le (h : initial_Ctx τ c N σ Xm z r) : ‖initial_B σ Xm z‖ ≤ initial_KB τ := by
  have hτ := h.hτ
  have hK := initial_Kop_ge hτ
  have hterm : ∀ i : Fin M, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖
      ≤ initial_Kop τ * τ⁻¹ := fun i =>
    (h.gi i).trans (mul_le_mul_of_nonneg_left (h.le i) (by positivity))
  have havg := initial_avg_le h.hN _ hterm
  rw [Fintype.card_fin] at havg
  have h2 : ‖(N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖
      ≤ τ⁻¹ ^ 2 * initial_Kop τ := by
    refine havg.trans ?_
    calc (M : ℝ) / N * (initial_Kop τ * τ⁻¹) ≤ τ⁻¹ * (initial_Kop τ * τ⁻¹) := by
          gcongr
          exact h.ratio
      _ = τ⁻¹ ^ 2 * initial_Kop τ := by ring
  have h1 := initial_norm_z h.hz
  unfold initial_B initial_KB
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  linarith

/-- `|B| ≥ (2 K_op)⁻¹`. -/
private theorem B_ge (h : initial_Ctx τ c N σ Xm z r) :
    (2 * initial_Kop τ)⁻¹ ≤ ‖initial_B σ Xm z‖ := by
  have hK := initial_Kop_ge h.hτ
  have hb := h.bg ⟨0, h.hN⟩
  have hs := h.small.2.2.1
  have h1 : 1 / 2 ≤ ‖initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ⟨0, h.hN⟩)
      (Sum.inr ⟨0, h.hN⟩)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - initial_B σ Xm z
      * G (diagonal σ) Xm z (Sum.inr ⟨0, h.hN⟩) (Sum.inr ⟨0, h.hN⟩))
    rw [norm_sub_rev] at hb
    simp only [sub_sub_cancel, norm_one] at this
    linarith
  rw [norm_mul] at h1
  have h2 := h.gmu ⟨0, h.hN⟩
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h2 (norm_nonneg (initial_B σ Xm z))
  nlinarith

/-- `B m_N − 1 = N⁻¹ Σ_ν (B G_{νν} − 1)`, so `|B m_N − 1| ≤ L r`. -/
private theorem bm (h : initial_Ctx τ c N σ Xm z r) :
    ‖initial_B σ Xm z * mN (diagonal σ) Xm z - 1‖ ≤ initial_L τ * r := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h.hN.ne'
  have e : initial_B σ Xm z * mN (diagonal σ) Xm z - 1
      = (N : ℂ)⁻¹ * ∑ ν, (initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mN, mul_one]
    field_simp
  rw [e]
  have havg := initial_avg_le h.hN _ h.bg
  rwa [Fintype.card_fin, div_self (by exact_mod_cast h.hN.ne' : (N : ℝ) ≠ 0), one_mul] at havg

/-- `|m_N|⁻¹ ≤ 2 K_B`, in particular `m_N ≠ 0`. -/
private theorem mN_inv (h : initial_Ctx τ c N σ Xm z r) :
    mN (diagonal σ) Xm z ≠ 0 ∧ ‖mN (diagonal σ) Xm z‖⁻¹ ≤ 2 * initial_KB τ := by
  have hb := h.bm
  have hs := h.small.2.2.1
  have h1 : 1 / 2 ≤ ‖initial_B σ Xm z * mN (diagonal σ) Xm z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - initial_B σ Xm z * mN (diagonal σ) Xm z)
    rw [norm_sub_rev] at hb
    simp only [sub_sub_cancel, norm_one] at this
    linarith
  rw [norm_mul] at h1
  have hB := h.B_le
  have hm0 : 0 < ‖mN (diagonal σ) Xm z‖ := by
    by_contra hc
    have : ‖mN (diagonal σ) Xm z‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this, mul_zero] at h1
    linarith
  refine ⟨norm_pos_iff.1 hm0, ?_⟩
  rw [inv_le_iff_one_le_mul₀ hm0]
  have := mul_le_mul_of_nonneg_right hB hm0.le
  nlinarith

/-- `|A_i| ≥ (2 K_op)⁻¹` for `A_i = 1 + m_N σ_i`. -/
private theorem A_inv (h : initial_Ctx τ c N σ Xm z r) (i : Fin M) :
    1 + mN (diagonal σ) Xm z * σ i ≠ 0 ∧
      ‖1 + mN (diagonal σ) Xm z * σ i‖⁻¹ ≤ 2 * initial_Kop τ := by
  have hσi := h.pos i
  have hK := initial_Kop_ge h.hτ
  have hid := congrArg norm (initial_i_id h.pos Xm h.hz.1 i)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi] at hid
  have hρ := h.rho i
  have hs := h.small.2.1
  have hρ' : ‖initial_rho σ Xm z i‖ ≤ 1 / 2 := by
    refine hρ.trans ?_
    calc σ i * (initial_L τ * r) ≤ τ⁻¹ * (initial_L τ * r) := by
          gcongr
          · exact mul_nonneg (initial_L_nonneg h.hτ) h.hr0
          · exact h.le i
      _ ≤ 1 / 2 := by linarith [hs, show τ⁻¹ * (initial_L τ * r) = τ⁻¹ * initial_L τ * r by ring]
  have h1 : 1 / 2 ≤ ‖initial_rho σ Xm z i - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - initial_rho σ Xm z i)
    simp only [sub_sub_cancel, norm_one] at this
    rw [norm_sub_rev]
    linarith
  have hg := h.gi i
  set a := ‖1 + mN (diagonal σ) Xm z * σ i‖ with ha
  have ha0 : 0 < a := by
    by_contra hc
    have : a = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this, mul_zero] at hid
    nlinarith
  refine ⟨norm_pos_iff.1 ha0, ?_⟩
  rw [inv_le_iff_one_le_mul₀ ha0]
  have h2 : σ i / 2 ≤ initial_Kop τ * σ i * a := by
    have := mul_le_mul_of_nonneg_right hg ha0.le
    nlinarith
  nlinarith

/-- `f(m_N) − z = (B − 1/m_N) + N⁻¹ Σ_i σ_i ρ_i / A_i`, so `|f(m_N) − z| ≤ F r`. -/
private theorem f_le (h : initial_Ctx τ c N σ Xm z r) :
    ‖fC N σ (mN (diagonal σ) Xm z) - z‖ ≤ initial_F τ * r := by
  have hτ := h.hτ
  have hK := initial_Kop_ge hτ
  have hL := initial_L_nonneg hτ
  have hKB := initial_KB_nonneg hτ
  have hr := h.hr0
  obtain ⟨hm0, hminv⟩ := h.mN_inv
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h.hN.ne'
  set m := mN (diagonal σ) Xm z with hm
  have e : fC N σ m - z = (initial_B σ Xm z * m - 1) / m
      + (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i) := by
    have hG : ∀ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)
        = (σ i : ℂ) * (initial_rho σ Xm z i - 1) / (1 + m * σ i) := fun i => by
      rw [eq_div_iff (h.A_inv i).1]
      exact initial_i_id h.pos Xm h.hz.1 i
    have hsplit : ∀ i, (σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i)
        = G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) + (σ i : ℂ) / (1 + m * σ i) := fun i => by
      rw [hG i]
      have := (h.A_inv i).1
      field_simp
      ring
    simp only [hsplit, Finset.sum_add_distrib, fC, initial_B]
    have hfc : ∑ i, (σ i : ℂ) / (N * (1 + σ i * m))
        = (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) / (1 + m * σ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (σ i : ℂ) m]
      field_simp
    rw [hfc]
    field_simp
    ring
  rw [e]
  have t1 : ‖(initial_B σ Xm z * m - 1) / m‖ ≤ 2 * initial_KB τ * initial_L τ * r := by
    rw [norm_div, div_eq_mul_inv]
    calc ‖initial_B σ Xm z * m - 1‖ * ‖m‖⁻¹ ≤ (initial_L τ * r) * (2 * initial_KB τ) :=
          mul_le_mul h.bm hminv (inv_nonneg.2 (norm_nonneg _)) (by positivity)
      _ = _ := by ring
  have hterm : ∀ i, ‖(σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i)‖
      ≤ τ⁻¹ * (τ⁻¹ * (initial_L τ * r)) * (2 * initial_Kop τ) := by
    intro i
    have hσi := h.pos i
    have hσle := h.le i
    rw [norm_div, div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσi]
    have hρ : ‖initial_rho σ Xm z i‖ ≤ τ⁻¹ * (initial_L τ * r) :=
      (h.rho i).trans (mul_le_mul_of_nonneg_right hσle (by positivity))
    have : σ i * ‖initial_rho σ Xm z i‖ ≤ τ⁻¹ * (τ⁻¹ * (initial_L τ * r)) :=
      mul_le_mul hσle hρ (norm_nonneg _) (by positivity)
    exact mul_le_mul this (h.A_inv i).2 (inv_nonneg.2 (norm_nonneg _)) (by positivity)
  have havg := initial_avg_le h.hN _ hterm
  rw [Fintype.card_fin] at havg
  have t2 : ‖(N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i)‖
      ≤ 2 * initial_Kop τ * initial_L τ * τ⁻¹ ^ 3 * r := by
    refine havg.trans ?_
    calc (M : ℝ) / N * (τ⁻¹ * (τ⁻¹ * (initial_L τ * r)) * (2 * initial_Kop τ))
        ≤ τ⁻¹ * (τ⁻¹ * (τ⁻¹ * (initial_L τ * r)) * (2 * initial_Kop τ)) := by
          gcongr
          exact h.ratio
      _ = _ := by ring
  refine (norm_add_le _ _).trans ?_
  unfold initial_F
  linarith

/-- `Θ_N = |m_N − m| ≤ 2 F r`, by the case `Im z ≥ 1` of Lemma A.5. -/
private theorem thetaN (h : initial_Ctx τ c N σ Xm z r) :
    ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ 2 * (initial_F τ * r) := by
  have hP : (diagonal σ).PosDef := posDef_diagonal_iff.2 h.pos
  have hu : 0 < (mN (diagonal σ) Xm z).im := by
    rw [mN_eq_resolventTransform hP Xm h.hz.1]
    have := isProbabilityMeasure_empMeasure (specOf (Xmᵀ * diagonal σ * Xm)) h.hN
    exact im_resolventTransform_pos _ h.hz.1
  have hf := h.f_le
  have hs := h.small.2.2.2
  have := norm_sub_mFun_le_of_im_ge (fun i => (h.pos i).le) h.hN one_pos h.hη hu
    (by linarith)
  rw [one_pow, div_one] at this
  linarith

/-- `|G_{νν} − m_N| ≤ 4 K_op L r`. -/
private theorem dmu (h : initial_Ctx τ c N σ Xm z r) (ν : Fin N) :
    ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - mN (diagonal σ) Xm z‖
      ≤ 4 * initial_Kop τ * initial_L τ * r := by
  have hK := initial_Kop_ge h.hτ
  have hL := initial_L_nonneg h.hτ
  have hr := h.hr0
  have hB := h.B_ge
  have hB0 : 0 < ‖initial_B σ Xm z‖ := lt_of_lt_of_le (by positivity) hB
  have hdiff : ∀ μ : Fin N, ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
      - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ ≤ 4 * initial_Kop τ * initial_L τ * r := by
    intro μ
    have e : initial_B σ Xm z * (G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ))
        = (initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - 1)
          - (initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - 1) := by ring
    have h1 := congrArg norm e
    rw [norm_mul] at h1
    have h2 := norm_sub_le (initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - 1)
      (initial_B σ Xm z * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - 1)
    have h3 : ‖initial_B σ Xm z‖ * ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ ≤ 2 * (initial_L τ * r) := by
      linarith [h.bg ν, h.bg μ]
    set d := ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖
    have hd0 : 0 ≤ d := norm_nonneg _
    have h4 : (2 * initial_Kop τ)⁻¹ * d ≤ 2 * (initial_L τ * r) :=
      (mul_le_mul_of_nonneg_right hB hd0).trans h3
    have h5 : d = 2 * initial_Kop τ * ((2 * initial_Kop τ)⁻¹ * d) := by
      field_simp
    rw [h5]
    calc 2 * initial_Kop τ * ((2 * initial_Kop τ)⁻¹ * d)
        ≤ 2 * initial_Kop τ * (2 * (initial_L τ * r)) := by gcongr
      _ = 4 * initial_Kop τ * initial_L τ * r := by ring
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h.hN.ne'
  have e : G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν) - mN (diagonal σ) Xm z
      = (N : ℂ)⁻¹ * ∑ μ, (G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mN, mul_sub, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
  rw [e]
  have havg := initial_avg_le h.hN _ hdiff
  rwa [Fintype.card_fin, div_self (by exact_mod_cast h.hN.ne' : (N : ℝ) ≠ 0), one_mul] at havg

/-- `|G_{ii} − m_i| ≤ σ_i² (2 K_op L + 4 K_op F / c) r`, from
`G_{ii} − m_i = σ_i ρ_i / A_i + σ_i² (m_N − m) / (A_i (1 + σ_i m))`. -/
private theorem gii_sub (h : initial_Ctx τ c N σ Xm z r) (i : Fin M) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i‖
      ≤ σ i * σ i * ((2 * initial_Kop τ * initial_L τ
        + 4 * initial_Kop τ * initial_F τ / c) * r) := by
  have hτ := h.hτ
  have hc := h.hc
  have hK := initial_Kop_ge hτ
  have hL := initial_L_nonneg hτ
  have hF := initial_F_nonneg hτ
  have hr := h.hr0
  have hσi := h.pos i
  obtain ⟨hA0, hAinv⟩ := h.A_inv i
  have hx := h.hx i
  have hx0 : 0 < ‖1 + (σ i : ℂ) * mFun N σ z‖ := hc.trans_le hx
  have hx0' : 1 + (σ i : ℂ) * mFun N σ z ≠ 0 := norm_pos_iff.1 hx0
  set m := mN (diagonal σ) Xm z with hm
  have hG : G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)
      = (σ i : ℂ) * (initial_rho σ Xm z i - 1) / (1 + m * σ i) := by
    rw [eq_div_iff hA0]
    exact initial_i_id h.pos Xm h.hz.1 i
  have e : G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i
      = (σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i)
        + (σ i : ℂ) * σ i * (m - mFun N σ z) / ((1 + m * σ i) * (1 + σ i * mFun N σ z)) := by
    have hA0' : 1 + (σ i : ℂ) * m ≠ 0 := by rwa [mul_comm]
    rw [hG, mI]
    field_simp
    ring
  rw [e]
  have t1 : ‖(σ i : ℂ) * initial_rho σ Xm z i / (1 + m * σ i)‖
      ≤ σ i * σ i * (2 * initial_Kop τ * initial_L τ * r) := by
    rw [norm_div, div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσi]
    calc σ i * ‖initial_rho σ Xm z i‖ * ‖1 + m * σ i‖⁻¹
        ≤ σ i * (σ i * (initial_L τ * r)) * (2 * initial_Kop τ) := by
          gcongr
          exact h.rho i
      _ = _ := by ring
  have t2 : ‖(σ i : ℂ) * σ i * (m - mFun N σ z) / ((1 + m * σ i) * (1 + σ i * mFun N σ z))‖
      ≤ σ i * σ i * (4 * initial_Kop τ * initial_F τ / c * r) := by
    rw [norm_div, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hσi, mul_inv]
    have hθ := h.thetaN
    have hxi : ‖1 + (σ i : ℂ) * mFun N σ z‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hx
    calc σ i * σ i * ‖m - mFun N σ z‖ * (‖1 + m * σ i‖⁻¹ * ‖1 + (σ i : ℂ) * mFun N σ z‖⁻¹)
        ≤ σ i * σ i * (2 * (initial_F τ * r)) * (2 * initial_Kop τ * c⁻¹) := by
          gcongr
      _ = _ := by field_simp; ring
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ σ i * σ i * (2 * initial_Kop τ * initial_L τ * r)
        + σ i * σ i * (4 * initial_Kop τ * initial_F τ / c * r) := add_le_add t1 t2
    _ = _ := by ring

/-- `Λ ≤ K_Λ r`. -/
private theorem lambda_le (h : initial_Ctx τ c N σ Xm z r) :
    Lambda σ Xm z ≤ initial_KL c τ * r := by
  have hτ := h.hτ
  have hc := h.hc
  have hK := initial_Kop_ge hτ
  have hL := initial_L_nonneg hτ
  have hF := initial_F_nonneg hτ
  have hr := h.hr0
  have hKL : 1 ≤ initial_KL c τ := by
    unfold initial_KL
    have : 0 ≤ 6 * initial_Kop τ * initial_L τ + 2 * initial_F τ
        + 4 * initial_Kop τ * initial_F τ / c := by positivity
    linarith
  have h0 : 0 ≤ initial_KL c τ * r := by positivity
  unfold Lambda
  refine Real.iSup_le (fun s => Real.iSup_le (fun t => ?_) h0) h0
  have hst0 : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (initial_sigS_pos h.pos s) (initial_sigS_pos h.pos t)
  rw [div_le_iff₀ hst0]
  by_cases hst : s = t
  · subst hst
    simp only [ite_true]
    cases s with
    | inl i =>
        have hσi := h.pos i
        simp only [mS, sigS, Sum.elim_inl]
        refine (h.gii_sub i).trans ?_
        rw [mul_comm (initial_KL c τ * r)]
        gcongr
        unfold initial_KL
        have : 0 ≤ 4 * initial_Kop τ * initial_L τ * r + 2 * initial_F τ * r + r := by
          positivity
        nlinarith
    | inr ν =>
        simp only [mS, sigS, Sum.elim_inr, mul_one]
        have e := norm_sub_le_norm_sub_add_norm_sub
          (G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)) (mN (diagonal σ) Xm z) (mFun N σ z)
        have h1 := h.dmu ν
        have h2 := h.thetaN
        unfold initial_KL
        have : 0 ≤ 2 * initial_Kop τ * initial_L τ * r + r
            + 4 * initial_Kop τ * initial_F τ / c * r := by positivity
        nlinarith
  · simp only [hst, ite_false, sub_zero]
    have h1 := initial_offdiag_le h.pos Xm z hst
    calc ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := h1
      _ ≤ sigS σ s * sigS σ t * (initial_KL c τ * r) := by
          gcongr
          exact h.hLo.trans (le_mul_of_one_le_left hr hKL)
      _ = _ := by ring

end initial_Ctx

/-- `Ψ_Θ ≤ (K_ψ / N)^{1/2}` for `η ≥ 1`: `Im m ≤ C_m`, `Θ_N ≤ K_op + C_m`,
`Θ_M ≤ K_op τ⁻¹ + τ⁻¹ / c` and `Φ ≤ N⁻¹`. -/
private theorem initial_psi_le {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (hle : ∀ i, σ i ≤ τ⁻¹)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im)
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) :
    PsiTheta σ Xm z ≤ √(initial_Kpsi c τ / N) := by
  obtain ⟨-, hm, him⟩ := gen_prop_m_specDomain da hz
  have hCm := initial_Cm_pos hτ
  have hK := initial_Kop_ge hτ
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have him0 : 0 ≤ (mFun N σ z).im := le_trans (by have := hz.1; positivity) him
  have him1 : (mFun N σ z).im ≤ mBoundConst τ := (Complex.im_le_norm _).trans hm
  have hmN : ‖mN (diagonal σ) Xm z‖ ≤ initial_Kop τ := by
    have h1 : ∀ μ : Fin N, ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ ≤ initial_Kop τ :=
      fun μ => by simpa [sigS] using initial_diag_le hτ hσ Xm hz hη (Sum.inr μ)
    have havg := initial_avg_le hN _ h1
    rwa [Fintype.card_fin, div_self hN'.ne', one_mul] at havg
  have hθN : ThetaN σ Xm z ≤ initial_Kop τ + mBoundConst τ := by
    unfold ThetaN
    exact (norm_sub_le _ _).trans (add_le_add hmN hm)
  have hθM : ThetaM σ Xm z ≤ initial_Kop τ * τ⁻¹ + τ⁻¹ / c := by
    have h1 : ∀ i, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i‖
        ≤ initial_Kop τ * τ⁻¹ + τ⁻¹ / c := by
      intro i
      have hσi := hσ i
      have hg : ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ ≤ initial_Kop τ * τ⁻¹ := by
        have := initial_diag_le hτ hσ Xm hz hη (Sum.inl i)
        simp only [sigS, Sum.elim_inl] at this
        exact this.trans (mul_le_mul_of_nonneg_left (hle i) (by positivity))
      have hmi : ‖mI N σ z i‖ ≤ τ⁻¹ / c := by
        rw [mI, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi]
        exact div_le_div₀ (by positivity) (hle i) hc (hx i)
      exact (norm_sub_le _ _).trans (add_le_add hg hmi)
    have havg := initial_avg_le hM _ h1
    unfold ThetaM
    rwa [Fintype.card_fin, div_self (by exact_mod_cast hM.ne' : (M : ℝ) ≠ 0), one_mul] at havg
  have hθ0 : 0 ≤ Theta σ Xm z := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΦ : PhiN N z ≤ (N : ℝ)⁻¹ := by
    unfold PhiN
    exact inv_anti₀ hN' (le_mul_of_one_le_right hN'.le hη)
  have hΦ0 : 0 ≤ PhiN N z := by
    unfold PhiN
    have := hz.1
    positivity
  unfold PsiTheta
  apply Real.sqrt_le_sqrt
  have hsum : (mFun N σ z).im + Theta σ Xm z ≤ initial_Kpsi c τ := by
    unfold Theta initial_Kpsi
    linarith
  rw [div_eq_mul_inv]
  exact mul_le_mul hsum hΦ hΦ0 (initial_Kpsi_nonneg hτ hc)

end Det

/-! ## From the deterministic bounds to stochastic domination -/

section Prob

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If `ξ ≤ N^ε ζ` holds wherever `Y_s ≤ N^e ψ` for every index `s` of a family of at most `N²`
indices, and each `Y_s ≺ ψ` at `(e, D + 2)`, then `ξ ≺ ζ` at `(ε, D)`. -/
private theorem initial_dom_of_det {ι : Type} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) {e ε D : ℝ}
    (hcard : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ (2 : ℝ)) {Y : ι → Ω → ℝ} {ψ ξ ζ : Ω → ℝ}
    (hY : ∀ s, DomAt N e (D + 2) (Y s) ψ)
    (hdet : ∀ ω, (∀ s, Y s ω ≤ (N : ℝ) ^ e * ψ ω) → ξ ω ≤ (N : ℝ) ^ ε * ζ ω) :
    DomAt N ε D ξ ζ := by
  unfold DomAt
  refine le_trans (measure_mono ?_) (DomAt.measure_exists_lt (ζ := fun _ => ψ) Finset.univ hN
    (by simpa using hcard) (fun s _ => hY s))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact absurd (hdet ω hcon) (not_le.2 hω)

end Prob

/-- `#(𝓘_M ⊔ 𝓘_N) = M + N ≤ N²` once `N ≥ 1 + τ⁻¹`. -/
private theorem initial_card_le {τ : ℝ} {N : ℕ} (hM : (M : ℝ) / N ≤ τ⁻¹) (hN : 1 ≤ N)
    (hNτ : 1 + τ⁻¹ ≤ (N : ℝ)) :
    (Fintype.card (Fin M ⊕ Fin N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN0] at hM
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Real.rpow_two, Nat.cast_add]
  nlinarith

/-- The size conditions on `N`: `N ≥ 1`, `N ≥ 1 + τ⁻¹`, `K₁ ≤ N^e` and `K₂ ≤ N^{1/4}`. -/
private theorem initial_threshold {τ e : ℝ} (he : 0 < e) (K₁ K₂ : ℝ) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 1 ≤ N ∧ 1 + τ⁻¹ ≤ (N : ℝ) ∧ K₁ ≤ (N : ℝ) ^ e ∧
      K₂ ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have t1 : Tendsto (fun N : ℕ => (N : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ev := ((eventually_ge_atTop 1).and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 + τ⁻¹))).and
    ((t1.eventually_ge_atTop K₁).and (t2.eventually_ge_atTop K₂))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ev
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1.1, (hN₁ N hN).1.2, (hN₁ N hN).2.1, (hN₁ N hN).2.2⟩⟩

/-! # Lemma 5.5 (`lem:initial`) -/

/-- Lemma 5.5, with the exponent `1/2`. -/
theorem initial_bound (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, 1 ≤ z.im → (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      DomAt N ε D (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  set e := min ε 1 / 4 with he
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 4 := by
    have := min_le_right ε 1
    linarith
  have he2 : 2 * e ≤ ε := by
    have := min_le_left ε 1
    linarith
  have hKψ := initial_Kpsi_nonneg hτ hc
  have hKL := initial_KL_nonneg hτ hc
  have hS := initial_S_ge hτ
  obtain ⟨N₁, h₁⟩ := lambdaO_Z_bound_initial τ C e (D + 2) hτ he0
  obtain ⟨N₂, h₂⟩ := initial_threshold (τ := τ) he0 (initial_KL c τ * √(initial_Kpsi c τ))
    (2 * initial_S τ * √(initial_Kpsi c τ))
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M σ X hD z hz hη hx => ?_⟩
  obtain ⟨hN1, hNτ, hK1, hK2⟩ := h₂ N (le_of_max_le_right hN)
  have da := hD.densityAssumptions hτ
  have hNpos : 0 < N := hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · have := hD.ratio_ge
      rw [h0, Nat.cast_zero, zero_div] at this
      linarith
    · exact h0
  refine initial_dom_of_det (Y := fun s ω => ‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z)
    (ψ := fun ω => PsiTheta σ (X ω) z) hN1 (initial_card_le hD.ratio_le hN1 hNτ)
    (h₁ N (le_of_max_le_left hN) M σ X hD z hz hη) fun ω hall => ?_
  -- the deterministic radius `r = N^e (K_ψ/N)^{1/2}`
  set a := (N : ℝ) ^ (1 / 4 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hsqrtN : √(N : ℝ) = a * a := by
    rw [Real.sqrt_eq_rpow, ha, ← Real.rpow_add hN0]
    norm_num
  have hNe : (N : ℝ) ^ e ≤ a := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) he1
  have hNe0 : 0 < (N : ℝ) ^ e := Real.rpow_pos_of_pos hN0 _
  set r := (N : ℝ) ^ e * √(initial_Kpsi c τ / N) with hr
  have hr' : r = (N : ℝ) ^ e * √(initial_Kpsi c τ) / (a * a) := by
    rw [hr, Real.sqrt_div' _ hN0.le, hsqrtN]
    ring
  have hr0 : 0 ≤ r := by positivity
  have hψ := initial_psi_le hτ hc hNpos hM da hD.pos hD.le (X ω) hz hη hx
  have hYr : ∀ s, ‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z ≤ r := fun s =>
    (hall s).trans (mul_le_mul_of_nonneg_left hψ hNe0.le)
  have hLo0 := initial_LambdaO_nonneg hD.pos (X ω) z
  have hrS : 2 * initial_S τ * r ≤ 1 := by
    rw [hr']
    have hq : 0 ≤ √(initial_Kpsi c τ) := Real.sqrt_nonneg _
    rw [show 2 * initial_S τ * ((N : ℝ) ^ e * √(initial_Kpsi c τ) / (a * a))
        = (2 * initial_S τ * √(initial_Kpsi c τ)) * (N : ℝ) ^ e / (a * a) by ring,
      div_le_one (by positivity)]
    exact mul_le_mul hK2 hNe hNe0.le ha0.le
  have ctx : initial_Ctx τ c N σ (X ω) z r :=
    { hτ := hτ, hc := hc, hN := hNpos, pos := hD.pos, le := hD.le, ratio := hD.ratio_le,
      hz := hz, hη := hη, hx := hx, hr0 := hr0, hrS := hrS
      hZ := fun s => by linarith [hYr s]
      hLo := by
        linarith [hYr (Sum.inr ⟨0, hNpos⟩), norm_nonneg (ZS σ (X ω) z (Sum.inr ⟨0, hNpos⟩))] }
  have hNhalf : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (a * a)⁻¹ := by
    rw [Real.rpow_neg hN0.le, ← hsqrtN, Real.sqrt_eq_rpow]
  have hNε : (N : ℝ) ^ e * (N : ℝ) ^ e ≤ (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
  calc Lambda σ (X ω) z ≤ initial_KL c τ * r := ctx.lambda_le
    _ = (initial_KL c τ * √(initial_Kpsi c τ)) * (N : ℝ) ^ e * (a * a)⁻¹ := by
        rw [hr']
        ring
    _ ≤ (N : ℝ) ^ e * (N : ℝ) ^ e * (a * a)⁻¹ := by gcongr
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [hNhalf]
        gcongr

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` for every `N ≥ 1` -/

section Checks

/-- Lemma 5.5 at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, 1 ≤ z.im → (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    DomAt N 1 1 (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
  initial_bound (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

end Checks

end Anisotropic

#print axioms Anisotropic.initial_bound
