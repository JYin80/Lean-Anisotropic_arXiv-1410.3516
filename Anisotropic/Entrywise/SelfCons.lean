import Anisotropic.Entrywise.LambdaOBound

/-! # (Gii_2), (Gmumu_2), (Gmumu-m) and Lemma 5.3 for `Σ = diag(σ)`

`Σ = diag(σ)`, at fixed `N`, pointwise in `z ∈ 𝐃`. The error terms of (Gii_2), (Gmumu_2) and
(calD_bound) are the explicit random variables `giiErr`, `gmmErr`, `calDErr`, i.e. the
defining differences.

On `Ξ`, with `e_i = −N⁻¹ Σ_μ G_{μi} G_{iμ} / G_{ii}` ((Gii_exp) and (Gstu)),
`giiErr_i = σ_i e_i` and `gmmErr_μ = N⁻¹ Σ_i G_{iμ} G_{μi} / G_{μμ}`, both of order `Λ_o²`.
(Gmumu-m) follows from `G_{μμ} − G_{νν} = G_{μμ} G_{νν} (1/G_{νν} − 1/G_{μμ})` and
`G_{μμ} − m_N = N⁻¹ Σ_ν (G_{μμ} − G_{νν})`. For (calD_bound), with `A_i = 1 + m_N σ_i`,
`u_i = σ_i Z_i + giiErr_i`, `D_i = −σ_i / G_{ii} = A_i + u_i` and `d_μ = G_{μμ} − m_N`,
`f(m_N) − z − [Z]_N − [Z]_M = N⁻¹ Σ_i σ_i giiErr_i / A_i² − N⁻¹ Σ_i σ_i u_i² / (A_i² D_i)
  − N⁻¹ Σ_μ gmmErr_μ + N⁻¹ Σ_μ d_μ² / (m_N² G_{μμ})`,
where `Σ_μ d_μ = 0` is used. All inputs come from (Lambda_o_Z_bound) at `(ε/4, D + 2)`, with a
union bound over the `M + N ≤ N²` indices `s`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # (Gii_2), (Gmumu_2), (Gmumu-m), Lemma 5.3 (`lem:calD_est`) -/

/-- `[Z]_N`. -/
def ZN {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ μ, Zmu σ Xm z μ

/-- `[Z]_M` of Lemma 5.3 (normalised by `N`). -/
def ZM {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm z * σ i) ^ 2 * Zi σ Xm z i

/-- `M⁻¹ Σ_i σ_i² (1 + m_N σ_i)⁻² Z_i`, (avg_conclusion2). -/
def ZMavg {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ i, (σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm z * σ i) ^ 2 * Zi σ Xm z i

/-- The error of (calD_bound): `f(m_N) − z − [Z]_N − [Z]_M`. -/
def calDErr {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  fC N σ (mN (diagonal σ) Xm z) - z - ZN σ Xm z - ZM σ Xm z

/-- The error of (Gii_2): `−σ_i/G_ii − (1 + m_N σ_i + σ_i Z_i)`. -/
def giiErr {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) : ℂ :=
  -(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)
    - (1 + mN (diagonal σ) Xm z * σ i + σ i * Zi σ Xm z i)

/-- The error of (Gmumu_2): `1/G_μμ − (−z − N⁻¹ Σ_i G_ii − Z_μ)`. -/
def gmmErr {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) : ℂ :=
  1 / G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
    - (-z - (N : ℂ)⁻¹ * ∑ i, G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - Zmu σ Xm z μ)

/-! ## Exact identities -/

section Identities

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `giiErr_i = −σ_i N⁻¹ Σ_μ G_{μi} G_{iμ} / G_{ii}`, from (Gii_exp) and (Gstu). -/
private theorem sc_giiErr_eq (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (i : Fin M) :
    giiErr σ Xm z i = -(σ i : ℂ) * ((N : ℂ)⁻¹ * ∑ μ,
      G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
        / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)) := by
  have e1 := Gii_exp hσ Xm hz i
  have e2 : ∀ μ : Fin N, G1 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr μ)
      = G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
        - G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
          / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) := fun μ =>
    Gstu (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inl i) (Sum.inr μ) (Sum.inr μ) (by simp) (by simp)
  simp only [e2, Finset.sum_sub_distrib] at e1
  have hσ0 : (σ i : ℂ) ≠ 0 := by exact_mod_cast (hσ i).ne'
  unfold giiErr mN
  rw [neg_div, div_eq_mul_one_div (σ i : ℂ), e1]
  field_simp
  ring

/-- `gmmErr_μ = N⁻¹ Σ_i G_{iμ} G_{μi} / G_{μμ}`, from (Gmumu_exp) and (Gstu). -/
private theorem sc_gmmErr_eq (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) :
    gmmErr σ Xm z μ = (N : ℂ)⁻¹ * ∑ i,
      G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
        / G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) := by
  have e1 := Gmumu_exp hσ Xm hz μ
  have e2 : ∀ i : Fin M, G1 (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i) (Sum.inl i)
      = G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)
        - G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
          / G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) := fun i =>
    Gstu (posDef_diagonal_iff.2 hσ) Xm hz (Sum.inr μ) (Sum.inl i) (Sum.inl i) (by simp) (by simp)
  simp only [e2, Finset.sum_sub_distrib] at e1
  unfold gmmErr
  rw [e1]
  ring

/-- The algebra of (calD_bound): with `m = N⁻¹ Σ_μ h_μ`, `A_i = 1 + m σ_i`,
`e_i = −σ_i/g_i − (A_i + σ_i ζ_i)` and `γ_μ = 1/h_μ − (−z − N⁻¹ Σ_i g_i − ζ'_μ)`,
`f(m) − z − N⁻¹ Σ_μ ζ'_μ − N⁻¹ Σ_i σ_i² A_i⁻² ζ_i` equals
`N⁻¹ Σ_i σ_i e_i / A_i² − N⁻¹ Σ_i σ_i (σ_i ζ_i + e_i)² / (A_i² (−σ_i/g_i)) − N⁻¹ Σ_μ γ_μ
  + N⁻¹ Σ_μ (h_μ − m)² / (m² h_μ)`. -/
private theorem sc_calD_identity {N : ℕ} (hN : (N : ℂ) ≠ 0) (σ : Fin M → ℝ) (g : Fin M → ℂ)
    (h : Fin N → ℂ) (zi : Fin M → ℂ) (zm : Fin N → ℂ) (z : ℂ) (hg : ∀ i, g i ≠ 0)
    (hh : ∀ μ, h μ ≠ 0) (hσ : ∀ i, (σ i : ℂ) ≠ 0) (hm : (N : ℂ)⁻¹ * ∑ μ, h μ ≠ 0)
    (hA : ∀ i, 1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i ≠ 0) :
    fC N σ ((N : ℂ)⁻¹ * ∑ μ, h μ) - z - (N : ℂ)⁻¹ * ∑ μ, zm μ
        - (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) ^ 2 / (1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i) ^ 2 * zi i
      = (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (-(σ i : ℂ) / g i
            - (1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i + σ i * zi i))
            / (1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i) ^ 2
        - (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * zi i + (-(σ i : ℂ) / g i
            - (1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i + σ i * zi i))) ^ 2
            / ((1 + ((N : ℂ)⁻¹ * ∑ μ, h μ) * σ i) ^ 2 * (-(σ i : ℂ) / g i))
        - (N : ℂ)⁻¹ * ∑ μ, (1 / h μ - (-z - (N : ℂ)⁻¹ * ∑ i, g i - zm μ))
        + (N : ℂ)⁻¹ * ∑ μ, (h μ - (N : ℂ)⁻¹ * ∑ ν, h ν) ^ 2
            / (((N : ℂ)⁻¹ * ∑ ν, h ν) ^ 2 * h μ) := by
  set m := (N : ℂ)⁻¹ * ∑ μ, h μ with hm_def
  set a := (N : ℂ)⁻¹ with ha
  have han : a * N = 1 := inv_mul_cancel₀ hN
  -- (F1) `f(m) = −m⁻¹ + N⁻¹ Σ_i σ_i / A_i`
  have F1 : fC N σ m = -m⁻¹ + a * ∑ i, (σ i : ℂ) / (1 + m * σ i) := by
    rw [fC, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha, mul_comm m (σ i : ℂ)]
    field_simp
  -- (F2) `−Σ_i g_i` expanded around `A_i`
  have F2 : ∑ i, -g i = ∑ i, (σ i : ℂ) / (1 + m * σ i)
      - ∑ i, (σ i : ℂ) ^ 2 / (1 + m * σ i) ^ 2 * zi i
      - ∑ i, (σ i : ℂ) * (-(σ i : ℂ) / g i - (1 + m * σ i + σ i * zi i)) / (1 + m * σ i) ^ 2
      + ∑ i, (σ i : ℂ) * (σ i * zi i + (-(σ i : ℂ) / g i - (1 + m * σ i + σ i * zi i))) ^ 2
          / ((1 + m * σ i) ^ 2 * (-(σ i : ℂ) / g i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hA i
    have h2 := hg i
    have h3 := hσ i
    generalize 1 + m * (σ i : ℂ) = A at h1 ⊢
    field_simp
    ring
  -- (F3) `Σ_μ 1/h_μ = N/m + Σ_μ d_μ² / (m² h_μ)`, since `Σ_μ d_μ = 0`
  have F3 : ∑ μ, 1 / h μ = N / m + ∑ μ, (h μ - m) ^ 2 / (m ^ 2 * h μ) := by
    have hd : ∑ μ, (h μ - m) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hm_def, ← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]
    have e : ∀ μ, 1 / h μ = 1 / m - (h μ - m) / m ^ 2 + (h μ - m) ^ 2 / (m ^ 2 * h μ) := by
      intro μ
      have := hh μ
      field_simp
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hd,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- (F4) `Σ_μ γ_μ = Σ_μ 1/h_μ + N z + N a Σ_i g_i + Σ_μ ζ'_μ`
  have F4 : ∑ μ, (1 / h μ - (-z - a * ∑ i, g i - zm μ))
      = ∑ μ, 1 / h μ + N * z + N * a * ∑ i, g i + ∑ μ, zm μ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [F1, F4]
  rw [Finset.sum_neg_distrib] at F2
  linear_combination (m⁻¹ + z + a * ∑ i, g i) * han + a * F3 - a * F2

end Identities

/-! ## Deterministic bounds on `Ξ` -/

section Det

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `σ̲_s > 0`. -/
private theorem sc_sigS_pos (hσ : ∀ i, 0 < σ i) (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Λ ≥ 0`. -/
private theorem sc_Lambda_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    0 ≤ Lambda σ Xm z :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun t =>
    div_nonneg (norm_nonneg _) (mul_pos (sc_sigS_pos hσ s) (sc_sigS_pos hσ t)).le

/-- `Λ_o ≥ 0`. -/
private theorem sc_LambdaO_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (sc_sigS_pos hσ _) (sc_sigS_pos hσ _)).le

/-- `|G_{st}| ≤ σ̲_s σ̲_t Λ_o` for `s ≠ t`. -/
private theorem sc_offdiag_le (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t := mul_pos (sc_sigS_pos hσ s) (sc_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
    unfold LambdaO
    exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `Λ_o ≤ Λ`. -/
private theorem sc_LambdaO_le (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    LambdaO σ Xm z ≤ Lambda σ Xm z := by
  refine Real.iSup_le (fun p => ?_) (sc_Lambda_nonneg hσ Xm z)
  unfold Lambda
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove p.1.1)
  refine le_trans (le_of_eq ?_) (le_ciSup (f := fun t =>
    ‖G (diagonal σ) Xm z p.1.1 t - (if p.1.1 = t then mS N σ z p.1.1 else 0)‖
      / (sigS σ p.1.1 * sigS σ t)) (Set.finite_range _).bddAbove p.1.2)
  simp [p.2]

/-- `c_as > 0`. -/
private theorem sc_ca_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mAsympLower τ := by
  unfold mAsympLower mBoundConst genPropConst
  positivity

/-- `C_m > 0`. -/
private theorem sc_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

/-- `‖N⁻¹ Σ_j f_j‖ ≤ (#ι / N) K` when every `‖f_j‖ ≤ K`. -/
private theorem sc_avg_le {ι : Type*} [Fintype ι] (hN : 0 < N) (f : ι → ℂ) {K : ℝ}
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

/-- The deterministic setting of the bounds on `Ξ`. -/
private structure sc_Ctx (τ c : ℝ) (N : ℕ) (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) : Prop where
  hc : 0 < c
  da : DensityAssumptions τ N σ
  pos : ∀ i, 0 < σ i
  hz : z ∈ specDomain τ N
  hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖
  hlog : (Real.log N)⁻¹ ≤ xiThr c τ
  hlog1 : (Real.log N)⁻¹ ≤ 1
  hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹
  hN : 0 < N

namespace sc_Ctx

variable {τ c : ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

private theorem diag (h : sc_Ctx τ c N σ Xm z) (t : Fin M ⊕ Fin N) :
    mAsympLower τ / 2 * sigS σ t ≤ ‖G (diagonal σ) Xm z t t‖ ∧
      ‖G (diagonal σ) Xm z t t‖ ≤ (mAsympUpper c τ + 1) * sigS σ t := by
  have := Gtt_bound h.hc h.da h.pos Xm h.hz h.hx h.hlog h.hΞ ∅ (by simp) t
    (Finset.notMem_empty t)
  rwa [Gm_empty] at this

private theorem G_ne (h : sc_Ctx τ c N σ Xm z) (t : Fin M ⊕ Fin N) :
    G (diagonal σ) Xm z t t ≠ 0 := by
  have h1 := (h.diag t).1
  have h2 : 0 < mAsympLower τ / 2 * sigS σ t :=
    mul_pos (half_pos (sc_ca_pos h.da.pos)) (sc_sigS_pos h.pos t)
  exact norm_pos_iff.1 (h2.trans_le h1)

private theorem LO_le_one (h : sc_Ctx τ c N σ Xm z) : LambdaO σ Xm z ≤ 1 :=
  ((sc_LambdaO_le h.pos Xm z).trans h.hΞ).trans h.hlog1

private theorem M_div_N (h : sc_Ctx τ c N σ Xm z) : (M : ℝ) / N ≤ τ⁻¹ := h.da.phi_upper

end sc_Ctx

/-- The constant of (Gii_2): `|giiErr_i| ≤ (2/c_as) σ_i² Λ_o²`. -/
private def sc_Ke (τ : ℝ) : ℝ := 2 / mAsympLower τ

/-- The constant of (Gmumu_2): `|gmmErr_μ| ≤ τ⁻³ (2/c_as) Λ_o²`. -/
private def sc_Kg (τ : ℝ) : ℝ := τ⁻¹ * (τ⁻¹ ^ 2 * sc_Ke τ)

/-- The constant of (Gmumu-m). -/
private def sc_Kd (c τ : ℝ) : ℝ := (mAsympUpper c τ + 1) ^ 2 * (2 + 2 * sc_Kg τ)

/-- The constant of (calD_bound). -/
private def sc_K4 (c τ : ℝ) : ℝ :=
  τ⁻¹ * (τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2)
    + τ⁻¹ * ((τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹) * (2 / c) ^ 2)
    + sc_Kg τ + sc_Kd c τ ^ 2 * (2 * mBoundConst τ) ^ 2 * (2 / mAsympLower τ)

variable {τ c : ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- (Gii_2) on `Ξ`: `|giiErr_i| ≤ (2/c_as) σ_i² Λ_o²`. -/
private theorem sc_giiErr_le (h : sc_Ctx τ c N σ Xm z) (i : Fin M) :
    ‖giiErr σ Xm z i‖ ≤ sc_Ke τ * σ i ^ 2 * LambdaO σ Xm z ^ 2 := by
  have hca := sc_ca_pos h.da.pos
  have hσi := h.pos i
  have hLo := sc_LambdaO_nonneg h.pos Xm z
  have hgi := (h.diag (Sum.inl i)).1
  simp only [sigS, Sum.elim_inl] at hgi
  have hgi0 : 0 < mAsympLower τ / 2 * σ i := by positivity
  rw [sc_giiErr_eq h.pos Xm h.hz.1 i, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hσi]
  have hterm : ∀ μ : Fin N, ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
      * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
      / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ ≤ sc_Ke τ * σ i * LambdaO σ Xm z ^ 2 := by
    intro μ
    have h1 := sc_offdiag_le h.pos Xm z (s := Sum.inr μ) (t := Sum.inl i) (by simp)
    have h2 := sc_offdiag_le h.pos Xm z (s := Sum.inl i) (t := Sum.inr μ) (by simp)
    simp only [sigS, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one] at h1 h2
    rw [norm_div, norm_mul, div_le_iff₀ (hgi0.trans_le hgi)]
    calc ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)‖
          * ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖
        ≤ (σ i * LambdaO σ Xm z) * (σ i * LambdaO σ Xm z) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = sc_Ke τ * σ i * LambdaO σ Xm z ^ 2 * (mAsympLower τ / 2 * σ i) := by
          unfold sc_Ke
          field_simp
      _ ≤ sc_Ke τ * σ i * LambdaO σ Xm z ^ 2
            * ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ := by
          have : 0 ≤ sc_Ke τ * σ i * LambdaO σ Xm z ^ 2 := by unfold sc_Ke; positivity
          gcongr
  have havg := sc_avg_le h.hN _ hterm
  rw [Fintype.card_fin, div_self (by exact_mod_cast h.hN.ne' : (N : ℝ) ≠ 0), one_mul] at havg
  calc σ i * ‖(N : ℂ)⁻¹ * ∑ μ, G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
        * G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
        / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖
      ≤ σ i * (sc_Ke τ * σ i * LambdaO σ Xm z ^ 2) := by gcongr
    _ = sc_Ke τ * σ i ^ 2 * LambdaO σ Xm z ^ 2 := by ring

/-- (Gmumu_2) on `Ξ`: `|gmmErr_μ| ≤ τ⁻³ (2/c_as) Λ_o²`. -/
private theorem sc_gmmErr_le (h : sc_Ctx τ c N σ Xm z) (μ : Fin N) :
    ‖gmmErr σ Xm z μ‖ ≤ sc_Kg τ * LambdaO σ Xm z ^ 2 := by
  have hτ := h.da.pos
  have hca := sc_ca_pos hτ
  have hLo := sc_LambdaO_nonneg h.pos Xm z
  have hgm := (h.diag (Sum.inr μ)).1
  simp only [sigS, Sum.elim_inr, mul_one] at hgm
  have hgm0 : 0 < mAsympLower τ / 2 := by positivity
  rw [sc_gmmErr_eq h.pos Xm h.hz.1 μ]
  have hterm : ∀ i : Fin M, ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
      * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)
      / G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ ≤ τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2 := by
    intro i
    have h1 := sc_offdiag_le h.pos Xm z (s := Sum.inl i) (t := Sum.inr μ) (by simp)
    have h2 := sc_offdiag_le h.pos Xm z (s := Sum.inr μ) (t := Sum.inl i) (by simp)
    simp only [sigS, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one] at h1 h2
    have hσi := h.pos i
    have hσle := h.da.bound_Sigma i
    rw [norm_div, norm_mul, div_le_iff₀ (hgm0.trans_le hgm)]
    calc ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖
          * ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inl i)‖
        ≤ (σ i * LambdaO σ Xm z) * (σ i * LambdaO σ Xm z) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (τ⁻¹ * LambdaO σ Xm z) * (τ⁻¹ * LambdaO σ Xm z) := by gcongr
      _ = τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2 * (mAsympLower τ / 2) := by
          unfold sc_Ke
          field_simp
      _ ≤ τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2
            * ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ := by
          have : 0 ≤ τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2 := by unfold sc_Ke; positivity
          gcongr
  have havg := sc_avg_le h.hN _ hterm
  rw [Fintype.card_fin] at havg
  refine havg.trans ?_
  have : 0 ≤ τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2 := by unfold sc_Ke; positivity
  calc (M : ℝ) / N * (τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2)
      ≤ τ⁻¹ * (τ⁻¹ ^ 2 * sc_Ke τ * LambdaO σ Xm z ^ 2) := by
        gcongr
        exact h.M_div_N
    _ = sc_Kg τ * LambdaO σ Xm z ^ 2 := by unfold sc_Kg; ring

/-- `Λ_o² ≤ a` and `Λ_o² ≤ a²` when `Λ_o ≤ a` on `Ξ`. -/
private theorem sc_LO_sq_le (h : sc_Ctx τ c N σ Xm z) {a : ℝ} (hLo : LambdaO σ Xm z ≤ a) :
    LambdaO σ Xm z ^ 2 ≤ a ∧ LambdaO σ Xm z ^ 2 ≤ a ^ 2 := by
  have h0 := sc_LambdaO_nonneg h.pos Xm z
  have h1 := h.LO_le_one
  constructor
  · nlinarith
  · nlinarith

/-- (Gmumu-m) on `Ξ`: `|G_{μμ} − m_N| ≤ K_d a` when `|Z_ν| ≤ a` for all `ν` and `Λ_o ≤ a`. -/
private theorem sc_d_le (h : sc_Ctx τ c N σ Xm z) {a : ℝ}
    (hZm : ∀ ν, ‖Zmu σ Xm z ν‖ ≤ a) (hLo : LambdaO σ Xm z ≤ a) (μ : Fin N) :
    ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z‖ ≤ sc_Kd c τ * a := by
  have hτ := h.da.pos
  have hca := sc_ca_pos hτ
  have hKg : 0 ≤ sc_Kg τ := by unfold sc_Kg sc_Ke; positivity
  have hCG : 0 ≤ mAsympUpper c τ + 1 := by
    have : 0 < c⁻¹ := inv_pos.2 h.hc
    have := le_max_left c⁻¹ (mBoundConst τ)
    unfold mAsympUpper
    linarith
  have hLa := (sc_LO_sq_le h hLo).1
  have hdiff : ∀ ν : Fin N, ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
      - G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)‖ ≤ sc_Kd c τ * a := by
    intro ν
    have hμ0 := h.G_ne (Sum.inr μ)
    have hν0 := h.G_ne (Sum.inr ν)
    have key : G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
        - G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
        = G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) * G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)
          * ((Zmu σ Xm z μ - Zmu σ Xm z ν) + (gmmErr σ Xm z ν - gmmErr σ Xm z μ)) := by
      unfold gmmErr
      field_simp
      ring
    have hgμ := (h.diag (Sum.inr μ)).2
    have hgν := (h.diag (Sum.inr ν)).2
    simp only [sigS, Sum.elim_inr, mul_one] at hgμ hgν
    have hsum : ‖(Zmu σ Xm z μ - Zmu σ Xm z ν) + (gmmErr σ Xm z ν - gmmErr σ Xm z μ)‖
        ≤ 2 * a + 2 * (sc_Kg τ * a) := by
      have e1 := norm_sub_le (Zmu σ Xm z μ) (Zmu σ Xm z ν)
      have e2 := norm_sub_le (gmmErr σ Xm z ν) (gmmErr σ Xm z μ)
      have e3 := norm_add_le (Zmu σ Xm z μ - Zmu σ Xm z ν) (gmmErr σ Xm z ν - gmmErr σ Xm z μ)
      have g1 := (sc_gmmErr_le h μ).trans (mul_le_mul_of_nonneg_left hLa hKg)
      have g2 := (sc_gmmErr_le h ν).trans (mul_le_mul_of_nonneg_left hLa hKg)
      linarith [hZm μ, hZm ν]
    rw [key, norm_mul, norm_mul]
    calc ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖
          * ‖G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)‖
          * ‖(Zmu σ Xm z μ - Zmu σ Xm z ν) + (gmmErr σ Xm z ν - gmmErr σ Xm z μ)‖
        ≤ (mAsympUpper c τ + 1) * (mAsympUpper c τ + 1) * (2 * a + 2 * (sc_Kg τ * a)) := by
          gcongr
      _ = sc_Kd c τ * a := by unfold sc_Kd; ring
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h.hN.ne'
  have e : G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z
      = (N : ℂ)⁻¹ * ∑ ν, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
        - G (diagonal σ) Xm z (Sum.inr ν) (Sum.inr ν)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mN, mul_sub, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
  rw [e]
  have havg := sc_avg_le h.hN _ hdiff
  rwa [Fintype.card_fin, div_self (by exact_mod_cast h.hN.ne' : (N : ℝ) ≠ 0), one_mul] at havg

/-- `‖x / A²‖ ≤ ‖x‖ (2/c)²` when `‖A‖ ≥ c/2 > 0`. -/
private theorem sc_div_sq_le {x A : ℂ} (hc : 0 < c) (hA : c / 2 ≤ ‖A‖) :
    ‖x / A ^ 2‖ ≤ ‖x‖ * (2 / c) ^ 2 := by
  have hA0 : 0 < ‖A‖ := (half_pos hc).trans_le hA
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  have h1 : (c / 2) ^ 2 ≤ ‖A‖ ^ 2 := by gcongr
  have h2 : (2 / c) ^ 2 * (c / 2) ^ 2 = 1 := by field_simp
  have h3 : 0 ≤ ‖x‖ := norm_nonneg _
  have h4 : (2 / c) ^ 2 * (c / 2) ^ 2 ≤ (2 / c) ^ 2 * ‖A‖ ^ 2 := by gcongr
  nlinarith

/-- (calD_bound) on `Ξ`: `|calDErr| ≤ K₄ a²` when `|Z_s| ≤ a` for all `s` and `Λ_o ≤ a`. -/
private theorem sc_calD_le (h : sc_Ctx τ c N σ Xm z) {a : ℝ}
    (hZi : ∀ i, ‖Zi σ Xm z i‖ ≤ a) (hZm : ∀ ν, ‖Zmu σ Xm z ν‖ ≤ a)
    (hLo : LambdaO σ Xm z ≤ a) :
    ‖calDErr σ Xm z‖ ≤ sc_K4 c τ * a ^ 2 := by
  have hτ := h.da.pos
  have hca := sc_ca_pos hτ
  have hCm := sc_Cm_pos hτ
  have hc := h.hc
  have ha : 0 ≤ a := (sc_LambdaO_nonneg h.pos Xm z).trans hLo
  have hKe : 0 ≤ sc_Ke τ := by unfold sc_Ke; positivity
  have hKg : 0 ≤ sc_Kg τ := by unfold sc_Kg; positivity
  have hCG : 0 ≤ mAsympUpper c τ + 1 := by
    have : 0 < c⁻¹ := inv_pos.2 h.hc
    have := le_max_left c⁻¹ (mBoundConst τ)
    unfold mAsympUpper
    linarith
  obtain ⟨hLa, hLa2⟩ := sc_LO_sq_le h hLo
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h.hN.ne'
  have hN1 : (N : ℝ) / N = 1 := div_self (by exact_mod_cast h.hN.ne')
  obtain ⟨hA, hm⟩ := oneAddMN_ge h.hc h.da h.pos Xm h.hz h.hx h.hlog h.hΞ
  have hm0 : mN (diagonal σ) Xm z ≠ 0 :=
    norm_pos_iff.1 ((inv_pos.2 (by positivity : (0 : ℝ) < 2 * mBoundConst τ)).trans_le hm)
  have hA0 : ∀ i, 1 + mN (diagonal σ) Xm z * σ i ≠ 0 := fun i =>
    norm_pos_iff.1 ((half_pos h.hc).trans_le (hA i))
  have hσ0 : ∀ i, (σ i : ℂ) ≠ 0 := fun i => by exact_mod_cast (h.pos i).ne'
  have hid : calDErr σ Xm z
      = (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * giiErr σ Xm z i / (1 + mN (diagonal σ) Xm z * σ i) ^ 2
        - (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
            / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
              * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)))
        - (N : ℂ)⁻¹ * ∑ μ, gmmErr σ Xm z μ
        + (N : ℂ)⁻¹ * ∑ μ, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z) ^ 2
            / (mN (diagonal σ) Xm z ^ 2 * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)) :=
    sc_calD_identity hNc σ (fun i => G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i))
      (fun μ => G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)) (Zi σ Xm z) (Zmu σ Xm z) z
      (fun i => h.G_ne _) (fun μ => h.G_ne _) hσ0 hm0 hA0
  -- the four terms
  have hT1 : ‖(N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * giiErr σ Xm z i
      / (1 + mN (diagonal σ) Xm z * σ i) ^ 2‖
      ≤ τ⁻¹ * (τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2) * a ^ 2 := by
    have hterm : ∀ i, ‖(σ i : ℂ) * giiErr σ Xm z i / (1 + mN (diagonal σ) Xm z * σ i) ^ 2‖
        ≤ τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2 * a ^ 2 := by
      intro i
      refine (sc_div_sq_le h.hc (hA i)).trans ?_
      have hσi := h.pos i
      have hσle := h.da.bound_Sigma i
      have he : ‖giiErr σ Xm z i‖ ≤ sc_Ke τ * τ⁻¹ ^ 2 * a ^ 2 := by
        refine (sc_giiErr_le h i).trans ?_
        gcongr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi]
      calc σ i * ‖giiErr σ Xm z i‖ * (2 / c) ^ 2
          ≤ τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2 * a ^ 2) * (2 / c) ^ 2 := by gcongr
        _ = τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2 * a ^ 2 := by ring
    have havg := sc_avg_le h.hN _ hterm
    rw [Fintype.card_fin] at havg
    refine havg.trans ?_
    have : 0 ≤ τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2 * a ^ 2 := by positivity
    calc (M : ℝ) / N * (τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2 * a ^ 2)
        ≤ τ⁻¹ * (τ⁻¹ * (sc_Ke τ * τ⁻¹ ^ 2) * (2 / c) ^ 2 * a ^ 2) := by
          gcongr
          exact h.M_div_N
      _ = _ := by ring
  have hT2 : ‖(N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
      / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
        * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)))‖
      ≤ τ⁻¹ * ((τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹) * (2 / c) ^ 2)
        * a ^ 2 := by
    have hterm : ∀ i, ‖(σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
        / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
          * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)))‖
        ≤ (τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹) * (2 / c) ^ 2
          * a ^ 2 := by
      intro i
      have hσi := h.pos i
      have hσle := h.da.bound_Sigma i
      have hg0 := h.G_ne (Sum.inl i)
      have hA0i := hA0 i
      have hσ0i := hσ0 i
      have e : (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
          / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
            * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)))
          = -((σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
            * G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i))
            / (1 + mN (diagonal σ) Xm z * σ i) ^ 2 := by
        field_simp
      rw [e]
      refine (sc_div_sq_le h.hc (hA i)).trans ?_
      have hu : ‖(σ i : ℂ) * Zi σ Xm z i + giiErr σ Xm z i‖ ≤ (τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) * a := by
        have e1 := norm_add_le ((σ i : ℂ) * Zi σ Xm z i) (giiErr σ Xm z i)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi] at e1
        have e2 : σ i * ‖Zi σ Xm z i‖ ≤ τ⁻¹ * a :=
          mul_le_mul hσle (hZi i) (norm_nonneg _) (inv_pos.2 hτ).le
        have e3 : ‖giiErr σ Xm z i‖ ≤ sc_Ke τ * τ⁻¹ ^ 2 * a := by
          refine (sc_giiErr_le h i).trans ?_
          gcongr
        nlinarith
      have hg := (h.diag (Sum.inl i)).2
      simp only [sigS, Sum.elim_inl] at hg
      have hg' : ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ ≤ (mAsympUpper c τ + 1) * τ⁻¹ :=
        hg.trans (by gcongr)
      rw [norm_neg, norm_mul, norm_pow]
      calc ‖(σ i : ℂ) * Zi σ Xm z i + giiErr σ Xm z i‖ ^ 2
            * ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ * (2 / c) ^ 2
          ≤ ((τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) * a) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹) * (2 / c) ^ 2 := by
            gcongr
        _ = _ := by ring
    have havg := sc_avg_le h.hN _ hterm
    rw [Fintype.card_fin] at havg
    refine havg.trans ?_
    have : 0 ≤ (τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹) * (2 / c) ^ 2
        * a ^ 2 := by positivity
    calc (M : ℝ) / N * ((τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹)
          * (2 / c) ^ 2 * a ^ 2)
        ≤ τ⁻¹ * ((τ⁻¹ + sc_Ke τ * τ⁻¹ ^ 2) ^ 2 * ((mAsympUpper c τ + 1) * τ⁻¹)
          * (2 / c) ^ 2 * a ^ 2) := by
          gcongr
          exact h.M_div_N
      _ = _ := by ring
  have hT3 : ‖(N : ℂ)⁻¹ * ∑ μ, gmmErr σ Xm z μ‖ ≤ sc_Kg τ * a ^ 2 := by
    have hterm : ∀ μ, ‖gmmErr σ Xm z μ‖ ≤ sc_Kg τ * a ^ 2 := fun μ =>
      (sc_gmmErr_le h μ).trans (mul_le_mul_of_nonneg_left hLa2 hKg)
    have havg := sc_avg_le h.hN _ hterm
    rwa [Fintype.card_fin, hN1, one_mul] at havg
  have hT4 : ‖(N : ℂ)⁻¹ * ∑ μ, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
      - mN (diagonal σ) Xm z) ^ 2
      / (mN (diagonal σ) Xm z ^ 2 * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ))‖
      ≤ sc_Kd c τ ^ 2 * (2 * mBoundConst τ) ^ 2 * (2 / mAsympLower τ) * a ^ 2 := by
    have hterm : ∀ μ, ‖(G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)
        - mN (diagonal σ) Xm z) ^ 2
        / (mN (diagonal σ) Xm z ^ 2 * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ))‖
        ≤ sc_Kd c τ ^ 2 * (2 * mBoundConst τ) ^ 2 * (2 / mAsympLower τ) * a ^ 2 := by
      intro μ
      have hd := sc_d_le h hZm hLo μ
      have hgm := (h.diag (Sum.inr μ)).1
      simp only [sigS, Sum.elim_inr, mul_one] at hgm
      have hmpos : 0 < (2 * mBoundConst τ)⁻¹ := by positivity
      have hm2 : (2 * mBoundConst τ)⁻¹ ^ 2 ≤ ‖mN (diagonal σ) Xm z‖ ^ 2 := by gcongr
      have hden : (2 * mBoundConst τ)⁻¹ ^ 2 * (mAsympLower τ / 2)
          ≤ ‖mN (diagonal σ) Xm z‖ ^ 2 * ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)‖ := by
        gcongr
      have hden0 : 0 < (2 * mBoundConst τ)⁻¹ ^ 2 * (mAsympLower τ / 2) := by positivity
      rw [norm_div, norm_mul, norm_pow, norm_pow, div_le_iff₀ (hden0.trans_le hden)]
      have hKd : 0 ≤ sc_Kd c τ := by unfold sc_Kd; positivity
      have hd2 : ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z‖ ^ 2
          ≤ (sc_Kd c τ * a) ^ 2 := by gcongr
      have hK0 : 0 ≤ sc_Kd c τ ^ 2 * (2 * mBoundConst τ) ^ 2 * (2 / mAsympLower τ) * a ^ 2 := by
        positivity
      calc ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z‖ ^ 2
          ≤ (sc_Kd c τ * a) ^ 2 := hd2
        _ = sc_Kd c τ ^ 2 * (2 * mBoundConst τ) ^ 2 * (2 / mAsympLower τ) * a ^ 2
            * ((2 * mBoundConst τ)⁻¹ ^ 2 * (mAsympLower τ / 2)) := by
            field_simp
        _ ≤ _ := by gcongr
    have havg := sc_avg_le h.hN _ hterm
    rwa [Fintype.card_fin, hN1, one_mul] at havg
  rw [hid]
  have t1 := norm_add_le
    ((N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * giiErr σ Xm z i / (1 + mN (diagonal σ) Xm z * σ i) ^ 2
      - (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
          / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
            * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)))
      - (N : ℂ)⁻¹ * ∑ μ, gmmErr σ Xm z μ)
    ((N : ℂ)⁻¹ * ∑ μ, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm z) ^ 2
      / (mN (diagonal σ) Xm z ^ 2 * G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)))
  have t2 := norm_sub_le
    ((N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * giiErr σ Xm z i / (1 + mN (diagonal σ) Xm z * σ i) ^ 2
      - (N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
          / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
            * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i))))
    ((N : ℂ)⁻¹ * ∑ μ, gmmErr σ Xm z μ)
  have t3 := norm_sub_le
    ((N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * giiErr σ Xm z i / (1 + mN (diagonal σ) Xm z * σ i) ^ 2)
    ((N : ℂ)⁻¹ * ∑ i, (σ i : ℂ) * (σ i * Zi σ Xm z i + giiErr σ Xm z i) ^ 2
          / ((1 + mN (diagonal σ) Xm z * σ i) ^ 2
            * (-(σ i : ℂ) / G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i))))
  unfold sc_K4
  linarith

end Det

/-! ## From the deterministic bounds to stochastic domination -/

section Prob

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If `ξ ≤ N^ε ζ` holds wherever `Y_s ≤ N^e ψ` for every index `s` of a family of at most `N²`
indices, and each `Y_s ≺ ψ` at `(e, D + 2)`, then `ξ ≺ ζ` at `(ε, D)`. -/
private theorem sc_dom_of_det {ι : Type} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) {e ε D : ℝ}
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

/-- `xiThr c τ > 0`. -/
private theorem sc_xiThr_pos {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 0 < xiThr c τ := by
  have h1 := sc_ca_pos hτ
  have h2 := sc_Cm_pos hτ
  have h3 : 0 < ThetaConst τ := by unfold ThetaConst; positivity
  unfold xiThr
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

/-- The size conditions on `N`: `N ≥ 1`, `(log N)⁻¹ ≤ min(xiThr c τ, 1)`, `N ≥ 1 + τ⁻¹` and
`K ≤ N^{ε/2}`. -/
private theorem sc_threshold {τ c ε : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) (K : ℝ) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 1 ≤ N ∧ (Real.log N)⁻¹ ≤ xiThr c τ ∧ (Real.log N)⁻¹ ≤ 1 ∧
      1 + τ⁻¹ ≤ (N : ℝ) ∧ K ≤ (N : ℝ) ^ (ε / 2) := by
  have tl : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have tp : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have ev := (((eventually_ge_atTop 1).and ((tendsto_order.1 tl).2 _ (sc_xiThr_pos hτ hc))).and
    ((tendsto_order.1 tl).2 1 one_pos)).and
    ((tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 + τ⁻¹)).and (tp.eventually_ge_atTop K))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ev
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1.1.1, (hN₁ N hN).1.1.2.le, (hN₁ N hN).1.2.le,
    (hN₁ N hN).2.1, (hN₁ N hN).2.2⟩⟩

/-- `#(𝓘_M ⊔ 𝓘_N) = M + N ≤ N²` once `N ≥ 1 + τ⁻¹`. -/
private theorem sc_card_le {τ : ℝ} {N : ℕ} (hM : (M : ℝ) / N ≤ τ⁻¹) (hN : 1 ≤ N)
    (hNτ : 1 + τ⁻¹ ≤ (N : ℝ)) :
    (Fintype.card (Fin M ⊕ Fin N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN0] at hM
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Real.rpow_two, Nat.cast_add]
  nlinarith

/-- `(N^{ε/4})² = N^{ε/2}` and `N^{ε/2} N^{ε/2} = N^ε`. -/
private theorem sc_rpow_facts {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 ≤ ε) :
    ((N : ℝ) ^ (ε / 4)) ^ 2 = (N : ℝ) ^ (ε / 2) ∧
      (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε ∧
      (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 4) ≤ (N : ℝ) ^ ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  · rw [← Real.rpow_add hN0]
    ring_nf
  · rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- On the event where every `1_Ξ (|Z_s| + Λ_o) ≤ a`: either `1_Ξ = 0`, or `Ξ` holds and
`|Z_i|, |Z_μ|, Λ_o ≤ a`. -/
private theorem sc_good {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ}
    {z : ℂ} (hc : 0 < c) (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hlog1 : (Real.log N)⁻¹ ≤ 1) (hN : 1 ≤ N) {a : ℝ}
    (hall : ∀ s, xiInd σ Xm z * (‖ZS σ Xm z s‖ + LambdaO σ Xm z) ≤ a) :
    xiInd σ Xm z = 0 ∨ (xiInd σ Xm z = 1 ∧ sc_Ctx τ c N σ Xm z ∧
      (∀ i, ‖Zi σ Xm z i‖ ≤ a) ∧ (∀ μ, ‖Zmu σ Xm z μ‖ ≤ a) ∧ LambdaO σ Xm z ≤ a) := by
  unfold xiInd at hall ⊢
  split_ifs at hall ⊢ with hΞ
  · simp only [one_mul] at hall
    have hLo0 := sc_LambdaO_nonneg hσ Xm z
    refine Or.inr ⟨rfl, ⟨hc, da, hσ, hz, hx, hlog, hlog1, hΞ, hN⟩, fun i => ?_, fun μ => ?_, ?_⟩
    · have := hall (Sum.inl i)
      simp only [ZS, Sum.elim_inl] at this
      linarith
    · have := hall (Sum.inr μ)
      simp only [ZS, Sum.elim_inr] at this
      linarith
    · have := hall (Sum.inr ⟨0, hN⟩)
      linarith [norm_nonneg (ZS σ Xm z (Sum.inr ⟨0, hN⟩))]
  · exact Or.inl rfl

/-! ## The four estimates -/

/-- (Gii_2). -/
theorem Gii_2 (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) → ∀ i : Fin M,
      DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖giiErr σ (X ω) z i‖)
        (fun ω => σ i * PsiTheta σ (X ω) z ^ 2) := by
  obtain ⟨N₁, h₁⟩ := lambdaO_Z_bound τ c C (ε / 4) (D + 2) hτ hc (by positivity)
  obtain ⟨N₂, h₂⟩ := sc_threshold hτ hc hε (sc_Ke τ * τ⁻¹)
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M σ X hD z hz hx i => ?_⟩
  obtain ⟨hN1, hlog, hlog1, hNτ, hK⟩ := h₂ N (le_of_max_le_right hN)
  have da := hD.densityAssumptions hτ
  obtain ⟨f1, f2, -⟩ := sc_rpow_facts hN1 hε.le
  refine sc_dom_of_det (Y := fun s ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
    hN1 (sc_card_le hD.ratio_le hN1 hNτ) (h₁ N (le_of_max_le_left hN) M σ X hD z hz hx)
    fun ω hall => ?_
  have hΨ : 0 ≤ PsiTheta σ (X ω) z := Real.sqrt_nonneg _
  have hσi := hD.pos i
  rcases sc_good hc da hD.pos hz hx hlog hlog1 hN1 hall with h0 | ⟨h1, ctx, -, -, hLo⟩
  · rw [h0, zero_mul]
    positivity
  · rw [h1, one_mul]
    have hKe : 0 ≤ sc_Ke τ := by have := sc_ca_pos hτ; unfold sc_Ke; positivity
    have hσ2 : σ i ^ 2 ≤ τ⁻¹ * σ i := by nlinarith [hD.le i]
    obtain ⟨-, hLa2⟩ := sc_LO_sq_le ctx hLo
    calc ‖giiErr σ (X ω) z i‖ ≤ sc_Ke τ * σ i ^ 2 * LambdaO σ (X ω) z ^ 2 := sc_giiErr_le ctx i
      _ ≤ sc_Ke τ * (τ⁻¹ * σ i) * ((N : ℝ) ^ (ε / 4) * PsiTheta σ (X ω) z) ^ 2 := by gcongr
      _ = sc_Ke τ * τ⁻¹ * (σ i * ((N : ℝ) ^ (ε / 2) * PsiTheta σ (X ω) z ^ 2)) := by
          rw [mul_pow, f1]
          ring
      _ ≤ (N : ℝ) ^ (ε / 2) * (σ i * ((N : ℝ) ^ (ε / 2) * PsiTheta σ (X ω) z ^ 2)) := by
          gcongr
      _ = (N : ℝ) ^ ε * (σ i * PsiTheta σ (X ω) z ^ 2) := by
          rw [← f2]
          ring

/-- (Gmumu-m). -/
theorem Gmumu_m (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) → ∀ μ : Fin N,
      DomAt N ε D
        (fun ω => xiInd σ (X ω) z *
          ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) (X ω) z‖)
        (fun ω => PsiTheta σ (X ω) z) := by
  obtain ⟨N₁, h₁⟩ := lambdaO_Z_bound τ c C (ε / 4) (D + 2) hτ hc (by positivity)
  obtain ⟨N₂, h₂⟩ := sc_threshold hτ hc hε (sc_Kd c τ)
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M σ X hD z hz hx μ => ?_⟩
  obtain ⟨hN1, hlog, hlog1, hNτ, hK⟩ := h₂ N (le_of_max_le_right hN)
  have da := hD.densityAssumptions hτ
  obtain ⟨-, -, f3⟩ := sc_rpow_facts hN1 hε.le
  refine sc_dom_of_det (Y := fun s ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
    hN1 (sc_card_le hD.ratio_le hN1 hNτ) (h₁ N (le_of_max_le_left hN) M σ X hD z hz hx)
    fun ω hall => ?_
  have hΨ : 0 ≤ PsiTheta σ (X ω) z := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases sc_good hc da hD.pos hz hx hlog hlog1 hN1 hall with h0 | ⟨h1, ctx, -, hZm, hLo⟩
  · rw [h0, zero_mul]
    positivity
  · rw [h1, one_mul]
    calc ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) (X ω) z‖
        ≤ sc_Kd c τ * ((N : ℝ) ^ (ε / 4) * PsiTheta σ (X ω) z) := sc_d_le ctx hZm hLo μ
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 4) * PsiTheta σ (X ω) z) := by gcongr
      _ = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 4) * PsiTheta σ (X ω) z := by ring
      _ ≤ (N : ℝ) ^ ε * PsiTheta σ (X ω) z := by gcongr

/-- Lemma 5.3, (calD_bound). -/
theorem calD_bound (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖calDErr σ (X ω) z‖)
        (fun ω => PsiTheta σ (X ω) z ^ 2) := by
  obtain ⟨N₁, h₁⟩ := lambdaO_Z_bound τ c C (ε / 4) (D + 2) hτ hc (by positivity)
  obtain ⟨N₂, h₂⟩ := sc_threshold hτ hc hε (sc_K4 c τ)
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M σ X hD z hz hx => ?_⟩
  obtain ⟨hN1, hlog, hlog1, hNτ, hK⟩ := h₂ N (le_of_max_le_right hN)
  have da := hD.densityAssumptions hτ
  obtain ⟨f1, f2, -⟩ := sc_rpow_facts hN1 hε.le
  refine sc_dom_of_det (Y := fun s ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
    hN1 (sc_card_le hD.ratio_le hN1 hNτ) (h₁ N (le_of_max_le_left hN) M σ X hD z hz hx)
    fun ω hall => ?_
  have hΨ : 0 ≤ PsiTheta σ (X ω) z := Real.sqrt_nonneg _
  rcases sc_good hc da hD.pos hz hx hlog hlog1 hN1 hall with h0 | ⟨h1, ctx, hZi, hZm, hLo⟩
  · rw [h0, zero_mul]
    positivity
  · rw [h1, one_mul]
    calc ‖calDErr σ (X ω) z‖ ≤ sc_K4 c τ * ((N : ℝ) ^ (ε / 4) * PsiTheta σ (X ω) z) ^ 2 :=
          sc_calD_le ctx hZi hZm hLo
      _ = sc_K4 c τ * ((N : ℝ) ^ (ε / 2) * PsiTheta σ (X ω) z ^ 2) := by rw [mul_pow, f1]
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * PsiTheta σ (X ω) z ^ 2) := by gcongr
      _ = (N : ℝ) ^ ε * PsiTheta σ (X ω) z ^ 2 := by
          rw [← f2]
          ring

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` for every `N ≥ 1` -/

section Checks

/-- (Gii_2) at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) → ∀ i : Fin M,
    DomAt N 1 1 (fun ω => xiInd σ (X ω) z * ‖giiErr σ (X ω) z i‖)
      (fun ω => σ i * PsiTheta σ (X ω) z ^ 2) :=
  Gii_2 (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- (Gmumu-m) at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) → ∀ μ : Fin N,
    DomAt N 1 1
      (fun ω => xiInd σ (X ω) z *
        ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) (X ω) z‖)
      (fun ω => PsiTheta σ (X ω) z) :=
  Gmumu_m (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- Lemma 5.3, (calD_bound), at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    DomAt N 1 1 (fun ω => xiInd σ (X ω) z * ‖calDErr σ (X ω) z‖)
      (fun ω => PsiTheta σ (X ω) z ^ 2) :=
  calD_bound (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- `[Z]_M = (M/N) M⁻¹ Σ_i σ_i² (1 + m_N σ_i)⁻² Z_i` for `M, N ≥ 1`. -/
example {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (hM : M ≠ 0)
    (hN : N ≠ 0) : ZM σ Xm z = (M : ℂ) / N * ZMavg σ Xm z := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  unfold ZM ZMavg
  rw [← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ hM', one_div]

/-- `f(m_N) − z = [Z]_N + [Z]_M + calDErr`, the form in which (calD_bound) is used. -/
example {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    fC N σ (mN (diagonal σ) Xm z) - z = ZN σ Xm z + ZM σ Xm z + calDErr σ Xm z := by
  unfold calDErr
  ring

end Checks

end Anisotropic

#print axioms Anisotropic.ZN
#print axioms Anisotropic.ZM
#print axioms Anisotropic.ZMavg
#print axioms Anisotropic.calDErr
#print axioms Anisotropic.giiErr
#print axioms Anisotropic.gmmErr
#print axioms Anisotropic.Gii_2
#print axioms Anisotropic.Gmumu_m
#print axioms Anisotropic.calD_bound
