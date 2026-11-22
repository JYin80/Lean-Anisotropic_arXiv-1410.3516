module

public import Anisotropic.Entrywise.Weak
public import Anisotropic.Entrywise.Iterate
public import Anisotropic.Entrywise.FA.Main

@[expose] public section

/-! # Theorem 3.22: the entrywise and averaged local laws for `Σ = diag(σ)`

`Σ = diag(σ)`, at fixed `N`, on a spectral domain `S` (Definition 3.20) on which (1+xm) and the
stability of Definition 5.4 hold. Write `Φ = (Nη)⁻¹`, `θ_0 = Φ^{1/4}`,
`θ_{k+1} = Φ + (θ_k Φ)^{1/2}` and `X = (Im m + θ_k) Φ`.

*One step of the iteration* (Section 5.2, end of the proof of Theorem 3.22, which refers to the
iteration of [BEKYY, Section 4.2]). Assume `Θ ≤ N^a θ_k` with high probability on `S`. At every
point `w` of the lattice `z_k = z + i k N⁻⁵` set `Υ = (N^a X + N⁻¹)^{1/2}`; then
`N^{−1/2} ≤ Υ ≤ N^{−τ/4}`, `Λ ≺ N^{−τ/4}` (Proposition 5.1) and `Λ_o ≺ Υ` (Lemma 5.2 and
`Ψ_Θ ≤ Υ`), so Lemma 5.6 gives `|[Z]_N| + |[Z]_M| ≺ Υ²`. With Lemma 5.3,
`|f(m_N) − w| ≤ δ(w) = N^{a+2b} X(w)`. The stability of Definition 5.4 along the lattice gives
`Θ_N ≤ max(C₀, C₁) δ/(Im m + √δ) ≤ max(C₀, C₁) N^{a+2b} θ_{k+1}`. With `A_i = 1 + m_N σ_i` and
(Gii_2), `G_{ii} − m_i = σ_i² Z_i / A_i² + R_i` with `|R_i| ≤ K N^{b/2} (Θ_N + Ψ_Θ²)`, so that
`Θ_M ≤ |M⁻¹ Σ_i σ_i² Z_i / A_i²| + K N^{b/2} (Θ_N + Ψ_Θ²)` and `Θ ≤ N^{a+3b} θ_{k+1}`.

*Theorem 3.22.* Starting from Proposition 5.1 (`Θ ≤ C Λ ≺ θ_0`), finitely many steps give
`Θ ≺ Φ`, which is the averaged law. The entrywise law follows from Proposition 5.1, Lemma 5.2,
(Gii_2), (Gmumu-m) and `Ψ_Θ ≤ N^{ε/4} Ψ` once `Θ ≤ N^{ε/4} Φ`. -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Elementary facts on `𝐃(τ, N)` -/

/-- `C_m > 0`. -/
private theorem em_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

/-- `C_as ≥ 0`. -/
private theorem em_Cas_nonneg {c τ : ℝ} (hc : 0 < c) : 0 ≤ mAsympUpper c τ :=
  (inv_pos.2 hc).le.trans (le_max_left _ _)

/-- `0 < Φ ≤ N^{−τ}` and `τ N⁻¹ ≤ Φ` on `𝐃(τ,N)`. -/
private theorem em_Phi {τ : ℝ} {N : ℕ} (hN : 0 < N) {w : ℂ}
    (hw : w ∈ specDomain τ N) :
    0 < PhiN N w ∧ PhiN N w ≤ (N : ℝ) ^ (-τ) ∧ τ * (N : ℝ)⁻¹ ≤ PhiN N w := by
  obtain ⟨h0, -, -, hη, hη'⟩ := hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by unfold PhiN; positivity, ?_, ?_⟩
  · have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
    have hx : (N : ℝ) ^ τ ≤ (N : ℝ) * w.im := by
      rw [← e]
      exact mul_le_mul_of_nonneg_left hη hN0.le
    unfold PhiN
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hx
  · unfold PhiN
    rw [mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc τ = (τ⁻¹)⁻¹ := (inv_inv τ).symm
      _ ≤ w.im⁻¹ := inv_anti₀ h0 hη'

/-- `0 < Im m ≤ C_m` and `N⁻¹ ≤ C_m Im m Φ` on `𝐃(τ,N)`. -/
private theorem em_imm {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (da : DensityAssumptions τ N σ) {w : ℂ} (hw : w ∈ specDomain τ N) :
    0 < (mFun N σ w).im ∧ (mFun N σ w).im ≤ mBoundConst τ ∧
      (N : ℝ)⁻¹ ≤ mBoundConst τ * ((mFun N σ w).im * PhiN N w) := by
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain da hw
  have hC := em_Cm_pos da.pos
  have hη := hw.1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have him : 0 < (mFun N σ w).im := (mFun_spec N σ da.nonneg hη).1
  refine ⟨him, (Complex.im_le_norm _).trans hm2, ?_⟩
  have e : mBoundConst τ * ((mBoundConst τ)⁻¹ * w.im * PhiN N w) = (N : ℝ)⁻¹ := by
    unfold PhiN
    field_simp
  rw [← e]
  gcongr
  unfold PhiN
  positivity

/-- `θ_k(Φ) ≤ 3` and `θ_k(Φ) ≥ 0` for `0 ≤ Φ ≤ 1`. -/
private theorem em_theta_le {k : ℕ} {Φ : ℝ} (h0 : 0 ≤ Φ) (h1 : Φ ≤ 1) :
    0 ≤ iterTheta k Φ ∧ iterTheta k Φ ≤ 3 := by
  refine ⟨?_, ?_⟩
  · cases k with
    | zero => exact Real.rpow_nonneg h0 _
    | succ k => simp only [iterTheta]; positivity
  · refine (iterTheta_le k h0 h1).trans ?_
    have hpow : ((1 : ℝ) / 2) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : Φ ^ (1 - 3 / 4 * ((1 : ℝ) / 2) ^ k) ≤ 1 := Real.rpow_le_one h0 h1 (by linarith)
    linarith

/-! ## Size conditions -/

/-- `K ≤ N^p` for all large `N`. -/
private theorem em_ev_rpow {p : ℝ} (hp : 0 < p) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K ≤ (N : ℝ) ^ p := by
  have := (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.1 (this.eventually_ge_atTop K)
  exact ⟨N₀, h⟩

/-- `(log N)⁻¹ ≤ x`, `(log N)⁻¹ ≤ 1` and `N^{−p} ≤ (log N)⁻¹` for all large `N`. -/
private theorem em_ev_log {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (Real.log N)⁻¹ ≤ x ∧ (Real.log N)⁻¹ ≤ 1 ∧
      (N : ℝ) ^ (-p) ≤ (Real.log N)⁻¹ := by
  have e1 : ∀ᶠ y : ℝ in atTop, ‖Real.log y‖ ≤ 1 * ‖y ^ p‖ :=
    (isLittleO_log_rpow_atTop hp).def one_pos
  have e2 : ∀ᶠ y : ℝ in atTop, max 1 x⁻¹ ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have e3 : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ y := eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually ((e1.and e2).and e3))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN₀ N hN
  set y : ℝ := (N : ℝ)
  have hy0 : 0 < y := by linarith
  have hlg1 : 1 ≤ Real.log y := le_trans (le_max_left _ _) h2
  have hlg0 : 0 < Real.log y := by linarith
  refine ⟨?_, inv_le_one_of_one_le₀ hlg1, ?_⟩
  · calc (Real.log y)⁻¹ ≤ (x⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hx) (le_trans (le_max_right _ _) h2)
      _ = x := inv_inv x
  · have hp' : 0 < y ^ p := Real.rpow_pos_of_pos hy0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlg0, abs_of_pos hp', one_mul] at h1
    rw [Real.rpow_neg hy0.le]
    exact inv_anti₀ hlg0 h1

/-- `N⁻⁵ ≤ τ⁻¹ − 1` when `τ < 1`, for all large `N`. -/
private theorem em_ev_tau {τ : ℝ} (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1 := by
  refine ⟨⌈(τ⁻¹ - 1)⁻¹⌉₊ + 1, fun N hN hτ1 => ?_⟩
  have hpos : 0 < τ⁻¹ - 1 := by linarith [(one_lt_inv₀ hτ).2 hτ1]
  have hx : (τ⁻¹ - 1)⁻¹ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(τ⁻¹ - 1)⁻¹⌉₊ ≤ N))
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  calc ((N : ℝ) ^ 5)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ (by positivity) (le_self_pow₀ hx1 (by norm_num))
    _ ≤ ((τ⁻¹ - 1)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hpos) hx
    _ = τ⁻¹ - 1 := inv_inv _

/-- `1 + N⁻⁵ ≤ τ⁻¹` when `Im z < 1` on `𝐃(τ,N)`. -/
private theorem em_top {τ : ℝ} {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ specDomain τ N)
    (h : τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1) : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ := by
  intro him
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hτlt : τ < 1 := by
    by_contra hc
    push Not at hc
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) := Real.one_le_rpow hN1 (by linarith)
    linarith [hz.2.2.2.1]
  linarith [h hτlt]

/-- The index sets: `N⁵ + 2 ≤ N⁹`, `M + N ≤ N⁹` and `M ≤ N⁹`. -/
private theorem em_card {τ : ℝ} {N : ℕ} (hM : (M : ℝ) ≤ τ⁻¹ * N) (h2 : 2 ≤ N)
    (hτN : 2 * (1 + τ⁻¹) ≤ (N : ℝ)) :
    (N : ℝ) ^ 5 + 2 ≤ (N : ℝ) ^ (9 : ℝ) ∧ (M : ℝ) + N ≤ (N : ℝ) ^ (9 : ℝ) ∧
      (M : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
  have e : (N : ℝ) ^ (9 : ℝ) = (N : ℝ) ^ (9 : ℕ) := by exact_mod_cast Real.rpow_natCast (N : ℝ) 9
  rw [e]
  have hx2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
  set x : ℝ := (N : ℝ)
  have hx2 : (2 : ℝ) ≤ x := hx2'
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h9 : x ^ 2 ≤ x ^ 9 := pow_le_pow_right₀ hx1 (by norm_num)
  have hτ0 : 0 ≤ τ⁻¹ := by
    by_contra hc
    push Not at hc
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hMN : (M : ℝ) + x ≤ x ^ 2 := by nlinarith
  refine ⟨?_, hMN.trans h9, ?_⟩
  · have h5 : x ^ 5 * 2 ≤ x ^ 5 * x ^ 4 := by
      have : (2 : ℝ) ≤ x ^ 4 := by nlinarith [pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 4)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h1 : (1 : ℝ) ≤ x ^ 5 := one_le_pow₀ hx1
    have : x ^ 9 = x ^ 5 * x ^ 4 := by ring
    nlinarith
  · have : (0 : ℝ) ≤ x := by linarith
    linarith

/-- `n` events of probability at most `N^{−(D+1)}` each, `n ≤ N`: their union has probability at
most `N^{−D}`. -/
private theorem em_union {Ω : Type} [MeasureSpace Ω] {N n : ℕ} {D : ℝ} (hN : 1 ≤ N)
    (hn : n ≤ N) (B : Fin n → Set Ω) (hB : ∀ j, ℙ (B j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    {A : Set Ω} (hA : ∀ ω ∈ A, ∃ j, ω ∈ B j) : ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : A ⊆ ⋃ j, B j := fun ω hω => Set.mem_iUnion.2 (hA ω hω)
  calc ℙ A ≤ ℙ (⋃ j, B j) := measure_mono hsub
    _ ≤ ∑ j, ℙ (B j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun j _ => hB j
    _ = ENNReal.ofReal (n * (N : ℝ) ^ (-(D + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
        have e : (N : ℝ) * (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) := by
          rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
          field_simp
        rw [← e]
        exact mul_le_mul_of_nonneg_right hn' (Real.rpow_nonneg hN0.le _)

/-- `τ ≤ 1` under the density assumptions. -/
private theorem em_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (da : DensityAssumptions τ N σ) :
    τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := da.phi_lower.trans da.phi_upper
  by_contra hc
  push Not at hc
  linarith [inv_lt_one_of_one_lt₀ hc]

/-- `Φ^{1/4} ≤ N^{−τ/4}` on `𝐃(τ,N)`. -/
private theorem em_Phi_quarter {τ : ℝ} {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : w ∈ specDomain τ N) :
    PhiN N w ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (-(τ / 4)) := by
  obtain ⟨hΦ0, hΦ, -⟩ := em_Phi hN hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc PhiN N w ^ (1 / 4 : ℝ) ≤ ((N : ℝ) ^ (-τ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hΦ0.le hΦ (by norm_num)
    _ = (N : ℝ) ^ (-(τ / 4)) := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring

/-- `Λ ≤ N^{τ/8} Φ^{1/4}` gives `Ξ` once `N^{−τ/8} ≤ (log N)⁻¹`. -/
private theorem em_xi {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {w : ℂ} (hw : w ∈ specDomain τ N) (hsmall : (N : ℝ) ^ (-(τ / 8)) ≤ (Real.log N)⁻¹)
    (hL : Lambda σ Xm w ≤ (N : ℝ) ^ (τ / 8) * PhiN N w ^ (1 / 4 : ℝ)) :
    Lambda σ Xm w ≤ (Real.log N)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (N : ℝ) ^ (τ / 8) * (N : ℝ) ^ (-(τ / 4)) = (N : ℝ) ^ (-(τ / 8)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc Lambda σ Xm w ≤ (N : ℝ) ^ (τ / 8) * PhiN N w ^ (1 / 4 : ℝ) := hL
    _ ≤ (N : ℝ) ^ (τ / 8) * (N : ℝ) ^ (-(τ / 4)) :=
        mul_le_mul_of_nonneg_left (em_Phi_quarter hN hw) (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (-(τ / 8)) := h2
    _ ≤ (Real.log N)⁻¹ := hsmall

/-- `xiInd = 1` on `Ξ`. -/
private theorem em_xiInd {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {w : ℂ}
    (h : Lambda σ Xm w ≤ (Real.log N)⁻¹) : xiInd σ Xm w = 1 := by
  simp [xiInd, h]

/-- `‖M⁻¹ Σ_i f_i‖ ≤ K` when every `‖f_i‖ ≤ K`, `K ≥ 0`. -/
private theorem em_avg_le (f : Fin M → ℂ) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, ‖f i‖ ≤ K) :
    ‖(M : ℂ)⁻¹ * ∑ i, f i‖ ≤ K := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simpa using hK0
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (M : ℝ)⁻¹ * ‖∑ i, f i‖ ≤ (M : ℝ)⁻¹ * ∑ _i : Fin M, K := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hK i)
      _ = K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-- `‖[Z]_M‖ ≤ τ⁻¹ ‖M⁻¹ Σ_i σ_i² (1 + m_N σ_i)⁻² Z_i‖`. -/
private theorem em_ZM_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (da : DensityAssumptions τ N σ) (Xm : Matrix (Fin M) (Fin N) ℝ) (w : ℂ) :
    ‖ZM σ Xm w‖ ≤ τ⁻¹ * ‖ZMavg σ Xm w‖ := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [ZM, ZMavg]
  · have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have e : ZM σ Xm w = ((M : ℂ) / N) * ZMavg σ Xm w := by
      unfold ZM ZMavg
      field_simp
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right da.phi_upper (norm_nonneg _)

/-! ## One step of the iteration: deterministic part -/

/-- The self-consistent bound at a lattice point: on `Ξ`, with Lemma 5.3, Lemma 5.6 and
`Θ ≤ N^a θ`, `|f(m_N) − w| ≤ N^{a+2b} (Im m + θ) Φ`. -/
private theorem em_close {τ a b θ Y : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (da : DensityAssumptions τ N σ) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ}
    (hw : w ∈ specDomain τ N) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : 1 + (1 + τ⁻¹) * (1 + mBoundConst τ) ≤ (N : ℝ) ^ b)
    (hxi : xiInd σ Xm w = 1)
    (hD : xiInd σ Xm w * ‖calDErr σ Xm w‖ ≤ (N : ℝ) ^ b * PsiTheta σ Xm w ^ 2)
    (hZN : ‖ZN σ Xm w‖ ≤ (N : ℝ) ^ b * Y ^ 2) (hZM : ‖ZMavg σ Xm w‖ ≤ (N : ℝ) ^ b * Y ^ 2)
    (hY : Y ^ 2 = (N : ℝ) ^ a * (((mFun N σ w).im + θ) * PhiN N w) + (N : ℝ)⁻¹)
    (hT : Theta σ Xm w ≤ (N : ℝ) ^ a * θ) :
    ‖fC N σ (mN (diagonal σ) Xm w) - w‖ ≤
      (N : ℝ) ^ (a + 2 * b) * (((mFun N σ w).im + θ) * PhiN N w) := by
  have hτ := da.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hΦ0, -, -⟩ := em_Phi hN hw
  obtain ⟨him, -, hinv⟩ := em_imm hN da hw
  have hC := em_Cm_pos hτ
  have hP1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha
  have hQ1 : 1 ≤ (N : ℝ) ^ b := Real.one_le_rpow hN1 hb
  have hPQ : (N : ℝ) ^ (a + 2 * b) = (N : ℝ) ^ a * (N : ℝ) ^ b * (N : ℝ) ^ b := by
    rw [Real.rpow_add hN0, two_mul, Real.rpow_add hN0]
    ring
  set P := (N : ℝ) ^ a with hPdef
  set Q := (N : ℝ) ^ b with hQdef
  set X := ((mFun N σ w).im + θ) * PhiN N w with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hθ0 : 0 ≤ Theta σ Xm w := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpsi : PsiTheta σ Xm w ^ 2 ≤ P * X := by
    unfold PsiTheta
    rw [Real.sq_sqrt (by positivity)]
    have h1 : (mFun N σ w).im + Theta σ Xm w ≤ P * ((mFun N σ w).im + θ) := by nlinarith
    calc ((mFun N σ w).im + Theta σ Xm w) * PhiN N w
        ≤ P * ((mFun N σ w).im + θ) * PhiN N w := mul_le_mul_of_nonneg_right h1 hΦ0.le
      _ = P * X := by rw [hXdef]; ring
  have hImX : (mFun N σ w).im * PhiN N w ≤ X := by
    have : 0 ≤ θ * PhiN N w := by positivity
    rw [hXdef]
    nlinarith
  have hPX : X ≤ P * X := le_mul_of_one_le_left hX0 hP1
  have hY2 : Y ^ 2 ≤ (1 + mBoundConst τ) * (P * X) := by
    rw [hY]
    have h1 : (N : ℝ)⁻¹ ≤ mBoundConst τ * X :=
      hinv.trans (mul_le_mul_of_nonneg_left hImX hC.le)
    have h2 : mBoundConst τ * X ≤ mBoundConst τ * (P * X) := mul_le_mul_of_nonneg_left hPX hC.le
    nlinarith
  have e : fC N σ (mN (diagonal σ) Xm w) - w = calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w := by
    unfold calDErr
    ring
  rw [hxi, one_mul] at hD
  have hZM' := em_ZM_le hN da Xm w
  have hQ0 : 0 ≤ Q := by linarith
  have b1 : ‖calDErr σ Xm w‖ ≤ Q * (P * X) := hD.trans (mul_le_mul_of_nonneg_left hpsi hQ0)
  have b2 : ‖ZN σ Xm w‖ ≤ Q * ((1 + mBoundConst τ) * (P * X)) :=
    hZN.trans (mul_le_mul_of_nonneg_left hY2 hQ0)
  have b3 : ‖ZM σ Xm w‖ ≤ τ⁻¹ * (Q * ((1 + mBoundConst τ) * (P * X))) :=
    hZM'.trans (mul_le_mul_of_nonneg_left (hZM.trans (mul_le_mul_of_nonneg_left hY2 hQ0))
      (inv_pos.2 hτ).le)
  rw [e, hPQ]
  calc ‖calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w‖
      ≤ ‖calDErr σ Xm w‖ + ‖ZN σ Xm w‖ + ‖ZM σ Xm w‖ := norm_add₃_le
    _ ≤ Q * (P * X) + Q * ((1 + mBoundConst τ) * (P * X)) +
          τ⁻¹ * (Q * ((1 + mBoundConst τ) * (P * X))) := add_le_add (add_le_add b1 b2) b3
    _ = (1 + (1 + τ⁻¹) * (1 + mBoundConst τ)) * (P * Q * X) := by ring
    _ ≤ Q * (P * Q * X) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = P * Q * Q * X := by ring

/-- `δ/(I + √δ) ≤ s (Φ + √(tΦ))` for `δ = s (I + t) Φ`, `s ≥ 1`. -/
private theorem em_quot {I t Φ s : ℝ} (hI : 0 ≤ I) (ht : 0 ≤ t) (hΦ : 0 ≤ Φ) (hs : 1 ≤ s) :
    s * (I + t) * Φ / (I + √(s * (I + t) * Φ)) ≤ s * (Φ + √(t * Φ)) := by
  set δ := s * (I + t) * Φ with hδ
  set x := s * t * Φ with hx
  have hs0 : 0 ≤ s := by linarith
  have hx0 : 0 ≤ x := by positivity
  have e : δ = s * I * Φ + x := by rw [hδ, hx]; ring
  have hxδ : x ≤ δ := by
    have : 0 ≤ s * I * Φ := by positivity
    rw [e]
    linarith
  have hsd := Real.sqrt_nonneg δ
  rcases (add_nonneg hI hsd).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    have := Real.sqrt_nonneg (t * Φ)
    positivity
  · rw [div_le_iff₀ hpos]
    have h1 : s * I * Φ ≤ s * Φ * (I + √δ) := by
      have : 0 ≤ s * Φ * √δ := by positivity
      nlinarith
    have h2 : x ≤ √x * (I + √δ) := by
      have hsx : √x * √x = x := Real.mul_self_sqrt hx0
      have : √x ≤ √δ := Real.sqrt_le_sqrt hxδ
      nlinarith [Real.sqrt_nonneg x]
    have h3 : √x ≤ s * √(t * Φ) := by
      have : x = s * (t * Φ) := by rw [hx]; ring
      rw [this, Real.sqrt_mul hs0]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      calc √s ≤ √(s * s) := Real.sqrt_le_sqrt (by nlinarith)
        _ = s := Real.sqrt_mul_self hs0
    calc δ = s * I * Φ + x := e
      _ ≤ s * Φ * (I + √δ) + √x * (I + √δ) := add_le_add h1 h2
      _ ≤ s * Φ * (I + √δ) + s * √(t * Φ) * (I + √δ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right h3 hpos.le)
      _ = s * (Φ + √(t * Φ)) * (I + √δ) := by ring

/-- The constant of the bound on `Θ_M`. -/
private def em_KR (c τ : ℝ) : ℝ :=
  τ⁻¹ ^ 2 * (mAsympUpper c τ + 1) / c + 10 * τ⁻¹ ^ 3 * (mAsympUpper c τ + 1) / c ^ 2

private theorem em_KR_nonneg {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) : 0 ≤ em_KR c τ := by
  have := em_Cas_nonneg (τ := τ) hc
  unfold em_KR
  positivity

/-- `G_{ii} − m_i − σ_i² Z_i / A_i²` in terms of `G_{ii}`, `m_N − m`, `Z_i` and the error `E_i` of
(Gii_2), with `A_i = 1 + m_N σ_i`. -/
private theorem em_gii_split (g s Z E mN m : ℂ) (hg : g ≠ 0) (hs : s ≠ 0) (hw : 1 + s * m ≠ 0)
    (hA : 1 + mN * s ≠ 0) (hE : E = -s / g - (1 + mN * s + s * Z)) :
    g - (-s / (1 + s * m)) - s ^ 2 / (1 + mN * s) ^ 2 * Z =
      -s * g * (mN - m) / (1 + s * m) - g * E / (1 + s * m)
        - s ^ 2 * Z * g * (mN - m) / ((1 + mN * s) * (1 + s * m))
        + s * Z * g * (s * Z + E) / (1 + mN * s) ^ 2 := by
  subst hE
  obtain ⟨A, rfl⟩ : ∃ A, mN = (A - 1) / s := ⟨1 + mN * s, by field_simp; ring⟩
  obtain ⟨w, rfl⟩ : ∃ w, m = (w - 1) / s := ⟨1 + s * m, by field_simp; ring⟩
  have e1 : 1 + (A - 1) / s * s = A := by field_simp; ring
  have e2 : 1 + s * ((w - 1) / s) = w := by field_simp; ring
  rw [e1] at hA ⊢
  rw [e2] at hw ⊢
  field_simp
  ring

/-- The bound `|R_i| ≤ K n² (Θ_N + Ψ_Θ²)` on the remainder. -/
private theorem em_R_le {c T CD σ t n p : ℝ} {g s Z E mN m : ℂ} (hc : 0 < c) (hσ : 0 < σ)
    (hσT : σ ≤ T) (hCD : 0 ≤ CD) (hs : ‖s‖ = σ) (hg : ‖g‖ ≤ CD * σ)
    (hw : c ≤ ‖1 + s * m‖) (hA : c / 2 ≤ ‖1 + mN * s‖) (ht : ‖mN - m‖ = t)
    (hZ : ‖Z‖ ≤ n * p) (hE : ‖E‖ ≤ n * (σ * p ^ 2)) (hp0 : 0 ≤ p) (hp : p ≤ 1) (hn : 1 ≤ n) :
    ‖-s * g * (mN - m) / (1 + s * m) - g * E / (1 + s * m)
        - s ^ 2 * Z * g * (mN - m) / ((1 + mN * s) * (1 + s * m))
        + s * Z * g * (s * Z + E) / (1 + mN * s) ^ 2‖
      ≤ (T ^ 2 * CD / c + 10 * T ^ 3 * CD / c ^ 2) * n ^ 2 * (t + p ^ 2) := by
  have hT : 0 < T := lt_of_lt_of_le hσ hσT
  have hw0 : 0 < ‖1 + s * m‖ := lt_of_lt_of_le hc hw
  have hA0 : 0 < ‖1 + mN * s‖ := lt_of_lt_of_le (half_pos hc) hA
  have ht0 : 0 ≤ t := ht ▸ norm_nonneg _
  have hn0 : 0 ≤ n := by linarith
  have hσ2 : σ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hσ.le hσT 2
  have hσ3 : σ ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hσ.le hσT 3
  have b1 : ‖-s * g * (mN - m) / (1 + s * m)‖ ≤ T ^ 2 * CD / c * t := by
    rw [norm_div, norm_mul, norm_mul, norm_neg, hs, ht]
    calc σ * ‖g‖ * t / ‖1 + s * m‖ ≤ σ * (CD * σ) * t / c := by gcongr
      _ = CD * σ ^ 2 * t / c := by ring
      _ ≤ CD * T ^ 2 * t / c := by gcongr
      _ = T ^ 2 * CD / c * t := by ring
  have b2 : ‖g * E / (1 + s * m)‖ ≤ T ^ 2 * CD / c * (n * p ^ 2) := by
    rw [norm_div, norm_mul]
    calc ‖g‖ * ‖E‖ / ‖1 + s * m‖ ≤ (CD * σ) * (n * (σ * p ^ 2)) / c := by gcongr
      _ = CD * σ ^ 2 * (n * p ^ 2) / c := by ring
      _ ≤ CD * T ^ 2 * (n * p ^ 2) / c := by gcongr
      _ = T ^ 2 * CD / c * (n * p ^ 2) := by ring
  have b3 : ‖s ^ 2 * Z * g * (mN - m) / ((1 + mN * s) * (1 + s * m))‖ ≤
      2 * (T ^ 3 * CD / c ^ 2) * (n * t) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, hs, ht]
    calc σ ^ 2 * ‖Z‖ * ‖g‖ * t / (‖1 + mN * s‖ * ‖1 + s * m‖)
        ≤ σ ^ 2 * (n * p) * (CD * σ) * t / (c / 2 * c) := by gcongr
      _ = 2 * (CD * σ ^ 3 / c ^ 2) * (n * t) * p := by field_simp
      _ ≤ 2 * (CD * T ^ 3 / c ^ 2) * (n * t) * 1 := by gcongr
      _ = 2 * (T ^ 3 * CD / c ^ 2) * (n * t) := by ring
  have hsZE : ‖s * Z + E‖ ≤ σ * (n * p) * 2 := by
    calc ‖s * Z + E‖ ≤ ‖s * Z‖ + ‖E‖ := norm_add_le _ _
      _ ≤ σ * (n * p) + n * (σ * p ^ 2) := by
          rw [norm_mul, hs]
          exact add_le_add (mul_le_mul_of_nonneg_left hZ hσ.le) hE
      _ ≤ σ * (n * p) * 2 := by
          have : n * (σ * p ^ 2) ≤ σ * (n * p) := by
            have h1 : p ^ 2 ≤ p := by nlinarith
            calc n * (σ * p ^ 2) = σ * n * p ^ 2 := by ring
              _ ≤ σ * n * p := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = σ * (n * p) := by ring
          linarith
  have b4 : ‖s * Z * g * (s * Z + E) / (1 + mN * s) ^ 2‖ ≤
      8 * (T ^ 3 * CD / c ^ 2) * (n ^ 2 * p ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, hs]
    calc σ * ‖Z‖ * ‖g‖ * ‖s * Z + E‖ / ‖1 + mN * s‖ ^ 2
        ≤ σ * (n * p) * (CD * σ) * (σ * (n * p) * 2) / (c / 2) ^ 2 := by gcongr
      _ = 8 * (CD * σ ^ 3 / c ^ 2) * (n ^ 2 * p ^ 2) := by field_simp; ring
      _ ≤ 8 * (CD * T ^ 3 / c ^ 2) * (n ^ 2 * p ^ 2) := by gcongr
      _ = 8 * (T ^ 3 * CD / c ^ 2) * (n ^ 2 * p ^ 2) := by ring
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add b1 b2)) b3)) b4)
  refine hsum.trans ?_
  set α := T ^ 2 * CD / c
  set β := T ^ 3 * CD / c ^ 2
  have hα : 0 ≤ α := by positivity
  have hβ : 0 ≤ β := by positivity
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn1 : 1 ≤ n ^ 2 := by nlinarith
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have e : (T ^ 2 * CD / c + 10 * T ^ 3 * CD / c ^ 2) = α + 10 * β := by
    simp only [α, β]; ring
  rw [e]
  have c1 : α * t ≤ α * (n ^ 2 * t) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht0 hn1) hα
  have c2 : α * (n * p ^ 2) ≤ α * (n ^ 2 * p ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn2 hp2) hα
  have c3 : 2 * β * (n * t) ≤ 10 * β * (n ^ 2 * t) := by
    have h0 : n * t ≤ n ^ 2 * t := mul_le_mul_of_nonneg_right hn2 ht0
    have h1 : 2 * β * (n * t) ≤ 2 * β * (n ^ 2 * t) := mul_le_mul_of_nonneg_left h0 (by positivity)
    have h2 : 0 ≤ β * (n ^ 2 * t) := by positivity
    linarith
  have c4 : 8 * β * (n ^ 2 * p ^ 2) ≤ 10 * β * (n ^ 2 * p ^ 2) := by
    have h2 : 0 ≤ β * (n ^ 2 * p ^ 2) := by positivity
    linarith
  have e2 : (α + 10 * β) * n ^ 2 * (t + p ^ 2) =
      α * (n ^ 2 * t) + α * (n ^ 2 * p ^ 2) + 10 * β * (n ^ 2 * t) + 10 * β * (n ^ 2 * p ^ 2) := by
    ring
  rw [e2]
  linarith

/-- The bound on `Θ_M` on `Ξ`: `Θ_M ≤ |M⁻¹ Σ_i σ_i² Z_i / A_i²| + K n² (Θ_N + Ψ_Θ²)`, when
`|Z_i| ≤ n Ψ_Θ`, `|giiErr_i| ≤ n σ_i Ψ_Θ²` and `Ψ_Θ ≤ 1`. -/
private theorem em_thetaM {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ}
    (hw : w ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm w ≤ (Real.log N)⁻¹) {n : ℝ}
    (hn : 1 ≤ n) (hp1 : PsiTheta σ Xm w ≤ 1)
    (hZ : ∀ i, ‖Zi σ Xm w i‖ ≤ n * PsiTheta σ Xm w)
    (hgii : ∀ i, ‖giiErr σ Xm w i‖ ≤ n * (σ i * PsiTheta σ Xm w ^ 2)) :
    ThetaM σ Xm w ≤ ‖ZMavg σ Xm w‖ + em_KR c τ * n ^ 2 * (ThetaN σ Xm w + PsiTheta σ Xm w ^ 2) := by
  have hτ := da.pos
  have hA := (oneAddMN_ge hc da hσ Xm hw hx hlog hΞ).1
  have hKR := em_KR_nonneg hc hτ
  set R : Fin M → ℂ := fun i => G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) - mI N σ w i -
    (σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm w * σ i) ^ 2 * Zi σ Xm w i with hR
  have hRle : ∀ i, ‖R i‖ ≤ em_KR c τ * n ^ 2 * (ThetaN σ Xm w + PsiTheta σ Xm w ^ 2) := by
    intro i
    have hg0 := G_diag_ne_zero (posDef_diagonal_iff.2 hσ) Xm hw.1 (Sum.inl i)
    have hG := (Gtt_bound hc da hσ Xm hw hx hlog hΞ ∅ (by simp) (Sum.inl i) (by simp)).2
    rw [Gm_empty] at hG
    simp only [sigS, Sum.elim_inl] at hG
    have hw0 : 1 + (σ i : ℂ) * mFun N σ w ≠ 0 := norm_pos_iff.1 (hc.trans_le (hx i))
    have hA0 : 1 + mN (diagonal σ) Xm w * σ i ≠ 0 :=
      norm_pos_iff.1 ((half_pos hc).trans_le (hA i))
    have e := em_gii_split (G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i)) (σ i : ℂ) (Zi σ Xm w i)
      (giiErr σ Xm w i) (mN (diagonal σ) Xm w) (mFun N σ w) hg0
      (by exact_mod_cast (hσ i).ne') hw0 hA0 rfl
    have h := em_R_le (T := τ⁻¹) (CD := mAsympUpper c τ + 1) (t := ThetaN σ Xm w) hc (hσ i)
      (da.bound_Sigma i) (by linarith [em_Cas_nonneg (τ := τ) hc])
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ i)]) hG (hx i) (hA i) rfl
      (hZ i) (hgii i) (Real.sqrt_nonneg _) hp1 hn
    rw [← e] at h
    exact h
  have hsum : ∑ i, (G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) - mI N σ w i) =
      ∑ i, (σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm w * σ i) ^ 2 * Zi σ Xm w i + ∑ i, R i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hR]
    ring
  unfold ThetaM
  rw [hsum, mul_add]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact em_avg_le R (mul_nonneg (mul_nonneg hKR (sq_nonneg n))
    (add_nonneg (norm_nonneg _) (sq_nonneg _))) hRle

/-- Three events of probability at most `N^{−(D+1)}`, `N ≥ 3`. -/
private theorem em_union3 {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : 3 ≤ N)
    {A B₁ B₂ B₃ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hA : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃) : ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  refine em_union (n := 3) (by omega) hN ![B₁, B₂, B₃]
    (fun j => by fin_cases j; exacts [h₁, h₂, h₃]) fun ω hω => ?_
  rcases hA ω hω with h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

/-- Five events of probability at most `N^{−(D+1)}`, `N ≥ 5`. -/
private theorem em_union5 {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : 5 ≤ N)
    {A B₁ B₂ B₃ B₄ B₅ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₄ : ℙ B₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₅ : ℙ B₅ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hA : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃ ∨ ω ∈ B₄ ∨ ω ∈ B₅) :
    ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  refine em_union (n := 5) (by omega) hN ![B₁, B₂, B₃, B₄, B₅]
    (fun j => by fin_cases j; exacts [h₁, h₂, h₃, h₄, h₅]) fun ω hω => ?_
  rcases hA ω hω with h | h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]

/-- Seven events of probability at most `N^{−(D+1)}`, `N ≥ 7`. -/
private theorem em_union7 {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : 7 ≤ N)
    {A B₁ B₂ B₃ B₄ B₅ B₆ B₇ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₄ : ℙ B₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₅ : ℙ B₅ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₆ : ℙ B₆ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₇ : ℙ B₇ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hA : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃ ∨ ω ∈ B₄ ∨ ω ∈ B₅ ∨ ω ∈ B₆ ∨ ω ∈ B₇) :
    ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  refine em_union (n := 7) (by omega) hN ![B₁, B₂, B₃, B₄, B₅, B₆, B₇]
    (fun j => by fin_cases j; exacts [h₁, h₂, h₃, h₄, h₅, h₆, h₇]) fun ω hω => ?_
  rcases hA ω hω with h | h | h | h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩, ⟨6, h⟩]

/-- `σ̲_s > 0`. -/
private theorem em_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (s : Fin M ⊕ Fin N) :
    0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Λ_o ≥ 0`. -/
private theorem em_LambdaO_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (em_sigS_pos hσ _) (em_sigS_pos hσ _)).le

/-- `|G_{st}| / (σ̲_s σ̲_t) ≤ Λ_o` for `s ≠ t`. -/
private theorem em_offdiag_le {N : ℕ} {σ : Fin M → ℝ} (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
  unfold LambdaO
  exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
    ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
    (Set.finite_range _).bddAbove ⟨(s, t), hst⟩

/-- `Ψ_Θ² ≤ N^a (Im m + θ) Φ` when `Θ ≤ N^a θ`, `a ≥ 0`. -/
private theorem em_psi_sq {a θ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 1 ≤ N) (hσ : ∀ i, 0 ≤ σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : 0 < w.im) (ha : 0 ≤ a)
    (hT : Theta σ Xm w ≤ (N : ℝ) ^ a * θ) :
    ((mFun N σ w).im + Theta σ Xm w) * PhiN N w ≤
      (N : ℝ) ^ a * (((mFun N σ w).im + θ) * PhiN N w) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha
  have him : 0 < (mFun N σ w).im := (mFun_spec N σ hσ hw).1
  have hΦ0 : 0 ≤ PhiN N w := by unfold PhiN; positivity
  have h1 : (mFun N σ w).im + Theta σ Xm w ≤ (N : ℝ) ^ a * ((mFun N σ w).im + θ) := by nlinarith
  calc ((mFun N σ w).im + Theta σ Xm w) * PhiN N w
      ≤ (N : ℝ) ^ a * ((mFun N σ w).im + θ) * PhiN N w := mul_le_mul_of_nonneg_right h1 hΦ0
    _ = (N : ℝ) ^ a * (((mFun N σ w).im + θ) * PhiN N w) := by ring

/-! ## One step of the iteration: the control parameter `Υ` and the bound at one `ω` -/

/-- `Υ = (N^a (Im m + θ_k) Φ + N⁻¹)^{1/2}`, the control parameter of Lemma 5.6 in the step
from `θ_k` to `θ_{k+1}`. -/
private def em_Ups (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) (a : ℝ) (w : ℂ) : ℝ :=
  √((N : ℝ) ^ a * (((mFun N σ w).im + iterTheta k (PhiN N w)) * PhiN N w) + (N : ℝ)⁻¹)

/-- `Υ² = N^a X + N⁻¹`, `N^{−1/2} ≤ Υ ≤ N^{−τ/4}`, `N^a X ≤ 1` and `θ_k Φ ≤ 1` on `𝐃(τ,N)`,
`X = (Im m + θ_k) Φ`, once `C_m + 4 ≤ N^{τ/4}`. -/
private theorem em_Ups_facts {τ a : ℝ} {N : ℕ} {σ : Fin M → ℝ} (k : ℕ) (hN : 1 ≤ N)
    (da : DensityAssumptions τ N σ) {w : ℂ} (hw : w ∈ specDomain τ N)
    (haτ : a ≤ τ / 4) (hv : mBoundConst τ + 4 ≤ (N : ℝ) ^ (τ / 4)) :
    em_Ups N σ k a w ^ 2 =
        (N : ℝ) ^ a * (((mFun N σ w).im + iterTheta k (PhiN N w)) * PhiN N w) + (N : ℝ)⁻¹ ∧
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ em_Ups N σ k a w ∧ em_Ups N σ k a w ≤ (N : ℝ) ^ (-(τ / 4)) ∧
      (N : ℝ) ^ a * (((mFun N σ w).im + iterTheta k (PhiN N w)) * PhiN N w) ≤ 1 ∧
      iterTheta k (PhiN N w) * PhiN N w ≤ 1 := by
  have hτ := da.pos
  have hτ1 := em_tau_le_one da
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hΦ0, hΦ, -⟩ := em_Phi (by omega) hw
  obtain ⟨him, himC, -⟩ := em_imm (by omega) da hw
  have hC := em_Cm_pos hτ
  have hΦ1 : PhiN N w ≤ 1 :=
    hΦ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  obtain ⟨hθ0, hθ3⟩ := em_theta_le (k := k) hΦ0.le hΦ1
  have hv4 : (N : ℝ) ^ (-τ) = (((N : ℝ) ^ (τ / 4)) ^ 4)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.rpow_neg hN0.le]
    congr 2
    push_cast
    ring
  have hv2 : (N : ℝ) ^ (-(τ / 4)) = ((N : ℝ) ^ (τ / 4))⁻¹ := Real.rpow_neg hN0.le _
  have hNa : (N : ℝ) ^ a ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hN1 haτ
  have hNa0 : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg hN0.le _
  have hNinv : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-τ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  set v := (N : ℝ) ^ (τ / 4) with hvdef
  have hv1 : 4 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  set θ := iterTheta k (PhiN N w) with hθdef
  set X := ((mFun N σ w).im + θ) * PhiN N w with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ (mBoundConst τ + 3) * (v ^ 4)⁻¹ :=
    mul_le_mul (by linarith) (hΦ.trans hv4.le) hΦ0.le (by linarith)
  have hsum0 : 0 ≤ (N : ℝ) ^ a * X + (N : ℝ)⁻¹ := by positivity
  have hsum : (N : ℝ) ^ a * X + (N : ℝ)⁻¹ ≤ (v ^ 2)⁻¹ := by
    calc (N : ℝ) ^ a * X + (N : ℝ)⁻¹
        ≤ v * ((mBoundConst τ + 3) * (v ^ 4)⁻¹) + (v ^ 4)⁻¹ :=
          add_le_add (mul_le_mul hNa hX hX0 hv0.le) (hNinv.trans hv4.le)
      _ = ((mBoundConst τ + 3) * v + 1) / v ^ 4 := by field_simp
      _ ≤ (v * v) / v ^ 4 := by gcongr; nlinarith
      _ = (v ^ 2)⁻¹ := by field_simp
  have hsq : em_Ups N σ k a w ^ 2 = (N : ℝ) ^ a * X + (N : ℝ)⁻¹ := Real.sq_sqrt hsum0
  have hv21 : (v ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  refine ⟨hsq, ?_, ?_, ?_, ?_⟩
  · have e : (N : ℝ) ^ (-(1 / 2 : ℝ)) = √((N : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
    rw [e]
    exact Real.sqrt_le_sqrt (by have := mul_nonneg hNa0 hX0; linarith)
  · rw [hv2]
    calc em_Ups N σ k a w ≤ √((v ^ 2)⁻¹) := Real.sqrt_le_sqrt hsum
      _ = v⁻¹ := by rw [Real.sqrt_inv, Real.sqrt_sq hv0.le]
  · have h0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    linarith
  · calc θ * PhiN N w ≤ 3 * (v ^ 4)⁻¹ := mul_le_mul hθ3 (hΦ.trans hv4.le) hΦ0.le (by norm_num)
      _ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (by positivity)]
          have : v ≤ v ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
          linarith

/-- `Ψ_Θ ≤ Υ` when `Θ ≤ N^a θ_k`. -/
private theorem em_psi_le_ups {a : ℝ} {N : ℕ} {σ : Fin M → ℝ} (k : ℕ) (hN : 1 ≤ N)
    (hσ : ∀ i, 0 ≤ σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : 0 < w.im) (ha : 0 ≤ a)
    (hT : Theta σ Xm w ≤ (N : ℝ) ^ a * iterTheta k (PhiN N w)) :
    PsiTheta σ Xm w ≤ em_Ups N σ k a w := by
  have h := em_psi_sq hN hσ Xm hw ha hT
  unfold PsiTheta em_Ups
  refine Real.sqrt_le_sqrt (h.trans ?_)
  have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  linarith

/-- The constant of the last step of the iteration. -/
private def em_Kfin (c τ C₀ C₁ : ℝ) : ℝ :=
  (1 + mBoundConst τ) ^ 2 + (em_KR c τ + 1) * max (max C₀ C₁) 0 +
    em_KR c τ * (mBoundConst τ + 1)

/-- One step of the iteration at one `ω`: the bounds of Proposition 5.1, Lemma 5.3, Lemma 5.6
and `Θ ≤ N^a θ_k` along the lattice, and those of Lemma 5.2 and (Gii_2) at `z`, give
`Θ(z) ≤ N^{a+3b} θ_{k+1}`. -/
private theorem em_step_det {τ c C₀ C₁ K₀ a b : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    {σ : Fin M → ℝ} (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {S : Set ℂ} (hS : SpectralDomain τ N S)
    (hx : OneXmOn c N σ S) (hstab : StableOn C₀ C₁ K₀ N σ S) (k : ℕ) (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + 3 * b ≤ τ / 4)
    (hδ : AdmissibleDelta N S (iterDelta N σ (a + 2 * b) (iterTheta k)))
    {z : ℂ} (hz : z ∈ S) (hτN : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hsmall : (N : ℝ) ^ (-(τ / 8)) ≤ (Real.log N)⁻¹)
    (hv : mBoundConst τ + 4 ≤ (N : ℝ) ^ (τ / 4))
    (hK6 : 1 + (1 + τ⁻¹) * (1 + mBoundConst τ) ≤ (N : ℝ) ^ b)
    (hK8 : em_Kfin c τ C₀ C₁ ≤ (N : ℝ) ^ (b / 2))
    (hL : ∀ j ≤ latticeTop N z, Lambda σ Xm (latticePt N z j) ≤
      (N : ℝ) ^ (τ / 8) * PhiN N (latticePt N z j) ^ (1 / 4 : ℝ))
    (hD : ∀ j ≤ latticeTop N z, xiInd σ Xm (latticePt N z j) *
      ‖calDErr σ Xm (latticePt N z j)‖ ≤ (N : ℝ) ^ b * PsiTheta σ Xm (latticePt N z j) ^ 2)
    (hZN : ∀ j ≤ latticeTop N z, ‖ZN σ Xm (latticePt N z j)‖ ≤
      (N : ℝ) ^ b * em_Ups N σ k a (latticePt N z j) ^ 2)
    (hZM : ∀ j ≤ latticeTop N z, ‖ZMavg σ Xm (latticePt N z j)‖ ≤
      (N : ℝ) ^ b * em_Ups N σ k a (latticePt N z j) ^ 2)
    (hT : ∀ j ≤ latticeTop N z, Theta σ Xm (latticePt N z j) ≤
      (N : ℝ) ^ a * iterTheta k (PhiN N (latticePt N z j)))
    (hZ : ∀ s, xiInd σ Xm z * (‖ZS σ Xm z s‖ + LambdaO σ Xm z) ≤
      (N : ℝ) ^ (b / 4) * PsiTheta σ Xm z)
    (hgii : ∀ i, xiInd σ Xm z * ‖giiErr σ Xm z i‖ ≤
      (N : ℝ) ^ (b / 4) * (σ i * PsiTheta σ Xm z ^ 2)) :
    Theta σ Xm z ≤ (N : ℝ) ^ (a + 3 * b) * iterTheta (k + 1) (PhiN N z) := by
  have hτ := da.pos
  have hNpos : 0 < N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have haτ : a ≤ τ / 4 := by linarith
  have hτ1 := em_tau_le_one da
  have hC := em_Cm_pos hτ
  have hmem : ∀ j ≤ latticeTop N z, latticePt N z j ∈ S :=
    fun j hj => latticePt_mem hS hz hτN hj
  have hmemD : ∀ j ≤ latticeTop N z, latticePt N z j ∈ specDomain τ N :=
    fun j hj => hS.1 (hmem j hj)
  have hz0 : latticePt N z 0 = z := by simp [latticePt]
  have hzD : z ∈ specDomain τ N := hS.1 hz
  have hP : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hΦ1 : ∀ w ∈ specDomain τ N, PhiN N w ≤ 1 := fun w hw =>
    (em_Phi hNpos hw).2.1.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  -- the self-consistent bound along the lattice
  have : IsProbabilityMeasure (empMeasure (specOf (Xmᵀ * diagonal σ * Xm))) :=
    isProbabilityMeasure_empMeasure _ hNpos
  have hclose : ∀ j ≤ latticeTop N z, True →
      ‖fC N σ (resolventTransform (empMeasure (specOf (Xmᵀ * diagonal σ * Xm)))
          (latticePt N z j)) - latticePt N z j‖ ≤
        iterDelta N σ (a + 2 * b) (iterTheta k) (latticePt N z j) := by
    intro j hj _
    have hw := hmemD j hj
    rw [← mN_eq_resolventTransform hP Xm hw.1]
    obtain ⟨hΦ0, -, -⟩ := em_Phi hNpos hw
    obtain ⟨hθ0, -⟩ := em_theta_le (k := k) hΦ0.le (hΦ1 _ hw)
    have hxi := em_xiInd (em_xi hNpos Xm hw hsmall (hL j hj))
    have h := em_close hNpos da Xm hw hθ0 ha hb.le hK6 hxi (hD j hj) (hZN j hj) (hZM j hj)
      (em_Ups_facts k hN da hw haτ hv).1 (hT j hj)
    have e : iterDelta N σ (a + 2 * b) (iterTheta k) (latticePt N z j) =
        (N : ℝ) ^ (a + 2 * b) * (((mFun N σ (latticePt N z j)).im +
          iterTheta k (PhiN N (latticePt N z j))) * PhiN N (latticePt N z j)) := by
      unfold iterDelta
      ring
    rw [e]
    exact h
  have hdesc := stable_descent (B := weakBound C₀ C₁ K₀ N σ) hstab hδ
    (empMeasure (specOf (Xmᵀ * diagonal σ * Xm))) z (latticeTop N z) hmem
    (one_le_im_latticeTop hNpos z) (fun _ => True) (fun _ => True) trivial
    (fun _ _ _ => trivial) hclose (fun _ _ _ _ => trivial)
  have hstz := (hdesc 0 (Nat.zero_le _)).2
  rw [hz0, ← mN_eq_resolventTransform hP Xm hzD.1] at hstz
  -- the quantities at `z`
  obtain ⟨hΦ0, -, -⟩ := em_Phi hNpos hzD
  obtain ⟨him, himC, hinv⟩ := em_imm hNpos da hzD
  obtain ⟨hθ0, -⟩ := em_theta_le (k := k) hΦ0.le (hΦ1 _ hzD)
  obtain ⟨hY2, -, -, hPX1, hθΦ1⟩ := em_Ups_facts k hN da hzD haτ hv
  have hL0 := hL 0 (Nat.zero_le _)
  have hZM0 := hZM 0 (Nat.zero_le _)
  have hT0 := hT 0 (Nat.zero_le _)
  rw [hz0] at hL0 hZM0 hT0
  have hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹ := em_xi hNpos Xm hzD hsmall hL0
  have hxi := em_xiInd hΞ
  have hpsi2 := em_psi_sq hN (fun i => (hσ i).le) Xm hzD.1 ha hT0
  set Φ := PhiN N z with hΦdef
  set θ := iterTheta k Φ with hθdef
  set P := (N : ℝ) ^ a with hPdef
  set Q := (N : ℝ) ^ b with hQdef
  set m2 := (N : ℝ) ^ (b / 2) with hm2def
  set X := ((mFun N σ z).im + θ) * Φ with hXdef
  set θ' := iterTheta (k + 1) Φ with hθ'def
  set Bp := max (max C₀ C₁) 0 with hBp
  have hθ' : θ' = Φ + √(θ * Φ) := rfl
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 ha
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN1 hb.le
  have hm21 : 1 ≤ m2 := Real.one_le_rpow hN1 (by positivity)
  have hm2Q : m2 * m2 = Q := by
    rw [hm2def, hQdef, ← Real.rpow_add hN0]
    congr 1
    ring
  have hs1 : (N : ℝ) ^ (a + 2 * b) = P * Q * Q := by
    rw [Real.rpow_add hN0, two_mul, Real.rpow_add hN0]
    ring
  have hs2 : (N : ℝ) ^ (a + 3 * b) = P * Q * Q * Q := by
    rw [show a + 3 * b = a + b + b + b by ring, Real.rpow_add hN0, Real.rpow_add hN0,
      Real.rpow_add hN0]
  have hX0 : 0 ≤ X := by positivity
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hKR := em_KR_nonneg hc hτ
  have hsq0 : 0 ≤ √(θ * Φ) := Real.sqrt_nonneg _
  have hθ'0 : 0 ≤ θ' := by rw [hθ']; positivity
  -- `X ≤ (C_m + 1) θ'`
  have hXθ : X ≤ (mBoundConst τ + 1) * θ' := by
    have h1 : θ * Φ ≤ √(θ * Φ) := by
      have h0 : 0 ≤ θ * Φ := by positivity
      have hs := Real.mul_self_sqrt h0
      have hs1 : √(θ * Φ) ≤ 1 := Real.sqrt_le_one.mpr hθΦ1
      nlinarith
    have h2 : (mFun N σ z).im * Φ ≤ mBoundConst τ * Φ := mul_le_mul_of_nonneg_right himC hΦ0.le
    have h3 : Φ ≤ θ' := by rw [hθ']; linarith
    have h3' : √(θ * Φ) ≤ θ' := by rw [hθ']; linarith
    have h4 : mBoundConst τ * Φ ≤ mBoundConst τ * θ' := mul_le_mul_of_nonneg_left h3 hC.le
    have e : X = (mFun N σ z).im * Φ + θ * Φ := by rw [hXdef]; ring
    rw [e]
    linarith
  -- `Θ_N ≤ B⁺ N^{a+2b} θ_{k+1}`
  have hThN : ThetaN σ Xm z ≤ Bp * (P * Q * Q * θ') := by
    have hd0 : 0 ≤ iterDelta N σ (a + 2 * b) (iterTheta k) z := by
      unfold iterDelta
      positivity
    have h1 := twoRegime_le_max (C₀ := C₀) (C₁ := C₁) (K₀ := K₀) (κ := kappa N σ z.re)
      (η := z.im) hd0 him.le
    have hq : iterDelta N σ (a + 2 * b) (iterTheta k) z /
        ((mFun N σ z).im + √(iterDelta N σ (a + 2 * b) (iterTheta k) z)) ≤
        (N : ℝ) ^ (a + 2 * b) * (Φ + √(θ * Φ)) :=
      em_quot him.le hθ0 hΦ0.le (Real.one_le_rpow hN1 (by linarith))
    have hq0 : 0 ≤ iterDelta N σ (a + 2 * b) (iterTheta k) z /
        ((mFun N σ z).im + √(iterDelta N σ (a + 2 * b) (iterTheta k) z)) :=
      div_nonneg hd0 (add_nonneg him.le (Real.sqrt_nonneg _))
    calc ThetaN σ Xm z = ‖mN (diagonal σ) Xm z - mFun N σ z‖ := rfl
      _ ≤ weakBound C₀ C₁ K₀ N σ (iterDelta N σ (a + 2 * b) (iterTheta k)) z := hstz
      _ ≤ max C₀ C₁ * (iterDelta N σ (a + 2 * b) (iterTheta k) z /
          ((mFun N σ z).im + √(iterDelta N σ (a + 2 * b) (iterTheta k) z))) := h1
      _ ≤ Bp * (iterDelta N σ (a + 2 * b) (iterTheta k) z /
          ((mFun N σ z).im + √(iterDelta N σ (a + 2 * b) (iterTheta k) z))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
      _ ≤ Bp * ((N : ℝ) ^ (a + 2 * b) * (Φ + √(θ * Φ))) := mul_le_mul_of_nonneg_left hq hBp0
      _ = Bp * (P * Q * Q * θ') := by rw [hs1, hθ']
  -- `Θ_M`
  have hpsi0 : 0 ≤ PsiTheta σ Xm z := Real.sqrt_nonneg _
  have hpsiP : PsiTheta σ Xm z ^ 2 ≤ P * X := by
    have h1 := (mFun_spec N σ (fun i => (hσ i).le) hzD.1).1
    have h2 : 0 ≤ Theta σ Xm z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    unfold PsiTheta
    rw [Real.sq_sqrt (by positivity)]
    exact hpsi2
  have hpsi1 : PsiTheta σ Xm z ≤ 1 :=
    (pow_le_one_iff_of_nonneg hpsi0 (by norm_num : (2 : ℕ) ≠ 0)).1 (hpsiP.trans hPX1)
  have hn1 : 1 ≤ (N : ℝ) ^ (b / 4) := Real.one_le_rpow hN1 (by positivity)
  have hZi : ∀ i, ‖Zi σ Xm z i‖ ≤ (N : ℝ) ^ (b / 4) * PsiTheta σ Xm z := by
    intro i
    have h := hZ (Sum.inl i)
    rw [hxi, one_mul] at h
    simp only [ZS, Sum.elim_inl] at h
    linarith [em_LambdaO_nonneg hσ Xm z]
  have hgii' : ∀ i, ‖giiErr σ Xm z i‖ ≤ (N : ℝ) ^ (b / 4) * (σ i * PsiTheta σ Xm z ^ 2) := by
    intro i
    have h := hgii i
    rwa [hxi, one_mul] at h
  have hTM := em_thetaM hc da hσ Xm hzD (hx z hz) hlog hΞ hn1 hpsi1 hZi hgii'
  have hn2 : ((N : ℝ) ^ (b / 4)) ^ 2 = m2 := by
    rw [hm2def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  rw [hn2] at hTM
  -- `|M⁻¹ Σ σ_i² Z_i / A_i²| ≤ N^b Υ² ≤ (1 + C_m) N^{a+b} X`
  have hY2' : em_Ups N σ k a z ^ 2 ≤ (1 + mBoundConst τ) * (P * X) := by
    rw [hY2]
    have hImX : (mFun N σ z).im * Φ ≤ X := by
      have h0 : 0 ≤ θ * Φ := by positivity
      have e : X = (mFun N σ z).im * Φ + θ * Φ := by rw [hXdef]; ring
      rw [e]
      linarith
    have h1' : mBoundConst τ * ((mFun N σ z).im * Φ) ≤ mBoundConst τ * X :=
      mul_le_mul_of_nonneg_left hImX hC.le
    have h1 : (N : ℝ)⁻¹ ≤ mBoundConst τ * X := le_trans hinv h1'
    have h2 : mBoundConst τ * X ≤ mBoundConst τ * (P * X) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX0 hP1) hC.le
    have e : (1 + mBoundConst τ) * (P * X) = P * X + mBoundConst τ * (P * X) := by ring
    linarith
  have hZMz : ‖ZMavg σ Xm z‖ ≤ Q * ((1 + mBoundConst τ) * (P * X)) :=
    hZM0.trans (mul_le_mul_of_nonneg_left hY2' (by linarith))
  -- assembling
  have hy0 : 0 ≤ P * θ' := by positivity
  have hPXθ : P * X ≤ (mBoundConst τ + 1) * (P * θ') := by
    have := mul_le_mul_of_nonneg_left hXθ (by linarith : (0 : ℝ) ≤ P)
    linarith
  have hThN0 : 0 ≤ ThetaN σ Xm z := norm_nonneg _
  have t1 : Q * ((1 + mBoundConst τ) * (P * X)) ≤
      (1 + mBoundConst τ) ^ 2 * m2 * (Q * Q * (P * θ')) := by
    have hQ0 : 0 ≤ Q := by linarith
    have hQQ : Q ≤ m2 * (Q * Q) :=
      (le_mul_of_one_le_right hQ0 hQ1).trans (le_mul_of_one_le_left (by positivity) hm21)
    calc Q * ((1 + mBoundConst τ) * (P * X))
        ≤ Q * ((1 + mBoundConst τ) * ((mBoundConst τ + 1) * (P * θ'))) := by gcongr
      _ = (1 + mBoundConst τ) ^ 2 * Q * (P * θ') := by ring
      _ ≤ (1 + mBoundConst τ) ^ 2 * (m2 * (Q * Q)) * (P * θ') := by gcongr
      _ = (1 + mBoundConst τ) ^ 2 * m2 * (Q * Q * (P * θ')) := by ring
  have t2 : (em_KR c τ * m2 + 1) * ThetaN σ Xm z ≤
      (em_KR c τ + 1) * Bp * m2 * (Q * Q * (P * θ')) := by
    have h1 : em_KR c τ * m2 + 1 ≤ (em_KR c τ + 1) * m2 := by
      have e : (em_KR c τ + 1) * m2 = em_KR c τ * m2 + m2 := by ring
      linarith
    calc (em_KR c τ * m2 + 1) * ThetaN σ Xm z
        ≤ ((em_KR c τ + 1) * m2) * (Bp * (P * Q * Q * θ')) := by
          gcongr
      _ = (em_KR c τ + 1) * Bp * m2 * (Q * Q * (P * θ')) := by ring
  have t3 : em_KR c τ * m2 * PsiTheta σ Xm z ^ 2 ≤
      em_KR c τ * (mBoundConst τ + 1) * m2 * (Q * Q * (P * θ')) := by
    have hQQ1 : 1 ≤ Q * Q := one_le_mul_of_one_le_of_one_le hQ1 hQ1
    calc em_KR c τ * m2 * PsiTheta σ Xm z ^ 2 ≤ em_KR c τ * m2 * ((mBoundConst τ + 1) * (P * θ')) :=
          mul_le_mul_of_nonneg_left (hpsiP.trans hPXθ) (by positivity)
      _ = em_KR c τ * (mBoundConst τ + 1) * m2 * (1 * (P * θ')) := by ring
      _ ≤ em_KR c τ * (mBoundConst τ + 1) * m2 * (Q * Q * (P * θ')) := by gcongr
  have hfin : em_Kfin c τ C₀ C₁ * m2 * (Q * Q * (P * θ')) ≤ m2 * m2 * (Q * Q * (P * θ')) := by
    gcongr
  rw [hs2]
  calc Theta σ Xm z = ThetaM σ Xm z + ThetaN σ Xm z := rfl
    _ ≤ (‖ZMavg σ Xm z‖ + em_KR c τ * m2 * (ThetaN σ Xm z + PsiTheta σ Xm z ^ 2)) +
          ThetaN σ Xm z := add_le_add hTM le_rfl
    _ = ‖ZMavg σ Xm z‖ + (em_KR c τ * m2 + 1) * ThetaN σ Xm z +
          em_KR c τ * m2 * PsiTheta σ Xm z ^ 2 := by ring
    _ ≤ (1 + mBoundConst τ) ^ 2 * m2 * (Q * Q * (P * θ')) +
          (em_KR c τ + 1) * Bp * m2 * (Q * Q * (P * θ')) +
          em_KR c τ * (mBoundConst τ + 1) * m2 * (Q * Q * (P * θ')) :=
        add_le_add (add_le_add (hZMz.trans t1) t2) t3
    _ = em_Kfin c τ C₀ C₁ * m2 * (Q * Q * (P * θ')) := by unfold em_Kfin; ring
    _ ≤ m2 * m2 * (Q * Q * (P * θ')) := hfin
    _ = P * Q * Q * Q * θ' := by rw [hm2Q]; ring

/-- `xiThr > 0`. -/
private theorem em_xiThr_pos {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 0 < xiThr c τ := by
  have := em_Cm_pos hτ
  unfold xiThr mAsympLower ThetaConst
  positivity

/-! ## The self-improving iteration -/

/-- One step of the self-improving iteration: `Θ ≺ θ_k` at exponent `a` gives `Θ ≺ θ_{k+1}`
at exponent `a + 3b`. -/
theorem iterate_step (τ c C₀ C₁ K₀ : ℝ) (C : ℕ → ℝ) (k : ℕ) (a b D : ℝ) (hτ : 0 < τ)
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + 3 * b ≤ τ / 4) :
    ∃ D' : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S →
      (∀ z ∈ S, DomAt N a D' (fun ω => Theta σ (X ω) z) (fun _ => iterTheta k (PhiN N z))) →
      ∀ z ∈ S, DomAt N (a + 3 * b) D (fun ω => Theta σ (X ω) z)
        (fun _ => iterTheta (k + 1) (PhiN N z)) := by
  have hc₀ : (0 : ℝ) < τ / 4 := by positivity
  obtain ⟨ε₁, hε₁, D₁, N₁, h₁⟩ := fluct_avg τ c (τ / 4) C b (D + 1 + 9) hτ hc hc₀ hb
  refine ⟨max (D₁ + 2) (D + 10), ?_⟩
  have haτ : a ≤ τ / 4 := by linarith
  obtain ⟨N₂, h₂⟩ := weak_law τ c C₀ C₁ K₀ C (τ / 8) (D + 1 + 9) hτ hc (by positivity)
  obtain ⟨N₃, h₃⟩ := weak_law τ c C₀ C₁ K₀ C ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := weak_law τ c C₀ C₁ K₀ C (τ / 8) (D₁ + 1) hτ hc (by positivity)
  obtain ⟨N₅, h₅⟩ := lambdaO_Z_bound τ c C (ε₁ / 2) (D₁ + 1) hτ hc (by positivity)
  obtain ⟨N₆, h₆⟩ := calD_bound τ c C b (D + 1 + 9) hτ hc hb
  obtain ⟨N₇, h₇⟩ := lambdaO_Z_bound τ c C (b / 4) (D + 1 + 9) hτ hc (by positivity)
  obtain ⟨N₈, h₈⟩ := Gii_2 τ c C (b / 4) (D + 1 + 9) hτ hc (by positivity)
  obtain ⟨N₉, h₉⟩ := admissible_iterDelta hτ (s := a + 2 * b) (by positivity) (by linarith) k
  obtain ⟨N₁₀, h₁₀⟩ := em_ev_log (p := τ / 8) (by positivity) (em_xiThr_pos hτ hc)
  obtain ⟨N₁₁, h₁₁⟩ := em_ev_tau hτ
  obtain ⟨N₁₂, h₁₂⟩ := em_ev_rpow hc₀ (mBoundConst τ + 4)
  obtain ⟨N₁₃, h₁₃⟩ := em_ev_rpow hb (1 + (1 + τ⁻¹) * (1 + mBoundConst τ))
  obtain ⟨N₁₄, h₁₄⟩ := em_ev_rpow (p := b / 2) (by positivity) (em_Kfin c τ C₀ C₁)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉ + N₁₀ + N₁₁ + N₁₂ + N₁₃ + N₁₄ +
    ⌈2 * (1 + τ⁻¹)⌉₊ + 7, fun N hN Ω _ _ M σ X S hD hS hx hstab hT z hz => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hτN2 : 2 * (1 + τ⁻¹) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 * (1 + τ⁻¹)⌉₊ ≤ N))
  have da := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hτ1 := em_tau_le_one da
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hD.ratio_le
    rwa [div_le_iff₀ hN0] at this
  obtain ⟨hlog, -, hsmall⟩ := h₁₀ N (by omega)
  have hzD := hS.1 hz
  have hτN := em_top hN1 hzD (h₁₁ N (by omega))
  have hv := h₁₂ N (by omega)
  have hmem : ∀ j ≤ latticeTop N z, latticePt N z j ∈ S :=
    fun j hj => latticePt_mem hS hz hτN hj
  have hmemD : ∀ j ≤ latticeTop N z, latticePt N z j ∈ specDomain τ N :=
    fun j hj => hS.1 (hmem j hj)
  have hθnn : ∀ w ∈ S, 0 ≤ iterTheta k (PhiN N w) := fun w hw =>
    (em_theta_le (em_Phi hNpos (hS.1 hw)).1.le ((em_Phi hNpos (hS.1 hw)).2.1.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)))).1
  -- the inputs of Lemma 5.6 at every point of `S`
  have hΛ : ∀ w ∈ S, DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) w)
      (fun _ => (N : ℝ) ^ (-(τ / 4))) := fun w hw =>
    DomAt.mono hN1 (fun _ => le_rfl) (fun _ => em_Phi_quarter hNpos (hS.1 hw))
      (fun _ => (Real.rpow_pos_of_pos hN0 _).le) le_rfl le_rfl
      (h₃ N (by omega) M σ X S hD hS hx hstab w hw)
  have hLo : ∀ w ∈ S, DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) w)
      (fun _ => em_Ups N σ k a w) := by
    intro w hw
    have hwD := hS.1 hw
    have E1 := h₄ N (by omega) M σ X S hD hS hx hstab w hw
    have E2 := h₅ N (by omega) M σ X hD w hwD (hx w hw) (Sum.inr ⟨0, hNpos⟩)
    have E3 := DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => hθnn w hw) le_rfl
      (by linarith [le_max_left (D₁ + 2) (D + 10)] : D₁ + 1 ≤ max (D₁ + 2) (D + 10)) (hT w hw)
    unfold DomAt at E1 E2 E3 ⊢
    refine em_union3 (by omega) E1 E2 E3 (fun ω hω => ?_)
    by_contra hcon
    simp only [not_or, Set.mem_ofPred_eq, not_lt] at hcon hω
    obtain ⟨n1, n2, n3⟩ := hcon
    have hxi := em_xiInd (em_xi hNpos (X ω) hwD hsmall n1)
    rw [hxi, one_mul] at n2
    have hps := em_psi_le_ups k hN1 (fun i => (hσ i).le) (X ω) hwD.1 ha n3
    have hlo : LambdaO σ (X ω) w ≤ (N : ℝ) ^ (ε₁ / 2) * PsiTheta σ (X ω) w := by
      linarith [norm_nonneg (ZS σ (X ω) w (Sum.inr ⟨0, hNpos⟩))]
    have hU0 : 0 ≤ em_Ups N σ k a w := Real.sqrt_nonneg _
    have h1 : (N : ℝ) ^ (ε₁ / 2) ≤ (N : ℝ) ^ ε₁ :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h3 : (N : ℝ) ^ (ε₁ / 2) * PsiTheta σ (X ω) w ≤ (N : ℝ) ^ ε₁ * em_Ups N σ k a w :=
      (mul_le_mul_of_nonneg_left hps (Real.rpow_nonneg hN0.le _)).trans
        (mul_le_mul_of_nonneg_right h1 hU0)
    linarith
  -- the seven families of events
  have hcard := em_card hMN (by omega) hτN2
  have hKN : ((latticeTop N z : ℕ) : ℝ) + 1 ≤ (N : ℝ) ^ 5 + 2 := latticeTop_add_one_le hNpos hzD.1
  have hc1 : ((Finset.range (latticeTop N z + 1)).card : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_range]
    push_cast
    linarith [hcard.1]
  have hc2 : ((Finset.univ : Finset (Fin M ⊕ Fin N)).card : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    push_cast
    exact hcard.2.1
  have hc3 : ((Finset.univ : Finset (Fin M)).card : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hcard.2.2
  have hk_of : ∀ j ∈ Finset.range (latticeTop N z + 1), j ≤ latticeTop N z :=
    fun j hj => Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hfa : ∀ j ≤ latticeTop N z,
      DomAt N b (D + 1 + 9) (fun ω => ‖ZN σ (X ω) (latticePt N z j)‖)
        (fun _ => em_Ups N σ k a (latticePt N z j) ^ 2) ∧
      DomAt N b (D + 1 + 9) (fun ω => ‖ZMavg σ (X ω) (latticePt N z j)‖)
        (fun _ => em_Ups N σ k a (latticePt N z j) ^ 2) := fun j hj =>
    h₁ N (by omega) M σ X hD _ (hmemD j hj) (hx _ (hmem j hj)) (em_Ups N σ k a (latticePt N z j))
      (em_Ups_facts k hN1 da (hmemD j hj) haτ hv).2.1
      (em_Ups_facts k hN1 da (hmemD j hj) haτ hv).2.2.1 (hΛ _ (hmem j hj)) (hLo _ (hmem j hj))
  have P1 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => Lambda σ (X ω) (latticePt N z j))
    (ζ := fun j _ => PhiN N (latticePt N z j) ^ (1 / 4 : ℝ))
    (fun j hj => h₂ N (by omega) M σ X S hD hS hx hstab _ (hmem j (hk_of j hj)))
  have P2 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1
    (ξ := fun j ω => xiInd σ (X ω) (latticePt N z j) * ‖calDErr σ (X ω) (latticePt N z j)‖)
    (ζ := fun j ω => PsiTheta σ (X ω) (latticePt N z j) ^ 2)
    (fun j hj => h₆ N (by omega) M σ X hD _ (hmemD j (hk_of j hj)) (hx _ (hmem j (hk_of j hj))))
  have P3 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => ‖ZN σ (X ω) (latticePt N z j)‖)
    (ζ := fun j _ => em_Ups N σ k a (latticePt N z j) ^ 2)
    (fun j hj => (hfa j (hk_of j hj)).1)
  have P4 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => ‖ZMavg σ (X ω) (latticePt N z j)‖)
    (ζ := fun j _ => em_Ups N σ k a (latticePt N z j) ^ 2)
    (fun j hj => (hfa j (hk_of j hj)).2)
  have P5 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => Theta σ (X ω) (latticePt N z j))
    (ζ := fun j _ => iterTheta k (PhiN N (latticePt N z j)))
    (fun j hj => DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => hθnn _ (hmem j (hk_of j hj))) le_rfl
      (by linarith [le_max_right (D₁ + 2) (D + 10)] : D + 1 + 9 ≤ max (D₁ + 2) (D + 10))
      (hT _ (hmem j (hk_of j hj))))
  have P6 := DomAt.measure_exists_lt (D := D + 1) (C := 9)
    (Finset.univ : Finset (Fin M ⊕ Fin N)) hN1 hc2
    (ξ := fun s ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
    (ζ := fun _ ω => PsiTheta σ (X ω) z)
    (fun s _ => h₇ N (by omega) M σ X hD z hzD (hx z hz) s)
  have P7 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.univ : Finset (Fin M)) hN1 hc3
    (ξ := fun i ω => xiInd σ (X ω) z * ‖giiErr σ (X ω) z i‖)
    (ζ := fun i ω => σ i * PsiTheta σ (X ω) z ^ 2)
    (fun i _ => h₈ N (by omega) M σ X hD z hzD (hx z hz) i)
  unfold DomAt
  refine em_union7 (by omega) P1 P2 P3 P4 P5 P6 P7 (fun ω hω => ?_)
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at n1 n2 n3 n4 n5 n6 n7 hω
  have hdet := em_step_det hc hN1 da hσ (X ω) hS hx hstab k ha hb hab
    (h₉ N (by omega) M σ S da hS.1) hz hτN hlog hsmall hv (h₁₃ N (by omega)) (h₁₄ N (by omega))
    (fun j hj => n1 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n2 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n3 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n4 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n5 j (Finset.mem_range.2 (by omega)))
    (fun s => n6 s (Finset.mem_univ _)) (fun i => n7 i (Finset.mem_univ _))
  linarith

/-- `Θ ≺ (Nη)⁻¹` on `S` (both parts of `Θ`). -/
theorem theta_averaged (τ c C₀ C₁ K₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S →
      ∀ z ∈ S, DomAt N ε D (fun ω => Theta σ (X ω) z) (fun _ => PhiN N z) := by
  set εi := min ε τ with hεi
  have hεi0 : 0 < εi := lt_min hε hτ
  have hεiε : εi ≤ ε := min_le_left ε τ
  have hεiτ : εi ≤ τ := min_le_right ε τ
  set K : ℕ := ⌈3 / εi⌉₊ with hK
  set b := εi / (4 * (3 * (K : ℝ) + 1)) with hb
  have hb0 : 0 < b := by positivity
  have haK : (3 * (K : ℝ) + 1) * b = εi / 4 := by
    rw [hb]
    field_simp
  -- `Θ ≺ θ_k` at exponent `(3k+1) b`, for `k ≤ K`
  have key : ∀ k ≤ K, ∀ D' : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S →
      ∀ z ∈ S, DomAt N ((3 * (k : ℝ) + 1) * b) D' (fun ω => Theta σ (X ω) z)
        (fun _ => iterTheta k (PhiN N z)) := by
    intro k
    induction k with
    | zero =>
      intro _ D'
      obtain ⟨N₁, h₁⟩ := weak_law τ c C₀ C₁ K₀ C (b / 2) D' hτ hc (by positivity)
      obtain ⟨N₂, h₂⟩ := em_ev_rpow (p := b / 2) (by positivity) (ThetaConst τ)
      refine ⟨N₁ + N₂ + 1, fun N hN Ω _ _ M σ X S hD hS hx hstab z hz => ?_⟩
      have hNpos : 0 < N := by omega
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
      have h := h₁ N (by omega) M σ X S hD hS hx hstab z hz
      have hCT := h₂ N (by omega)
      have da := hD.densityAssumptions hτ
      have hq0 : 0 ≤ PhiN N z ^ (1 / 4 : ℝ) :=
        Real.rpow_nonneg (em_Phi hNpos (hS.1 hz)).1.le _
      have hsplit : (N : ℝ) ^ b = (N : ℝ) ^ (b / 2) * (N : ℝ) ^ (b / 2) := by
        rw [← Real.rpow_add hN0]
        ring_nf
      have hCT0 : 0 ≤ ThetaConst τ := by unfold ThetaConst; positivity
      unfold DomAt at h ⊢
      refine le_trans (measure_mono fun ω hω => ?_) h
      simp only [Set.mem_ofPred_eq, Nat.cast_zero, mul_zero, zero_add, one_mul] at hω ⊢
      by_contra hcon
      push Not at hcon
      have hT := Theta_le_Lambda da hD.pos (X ω) z hNpos
      have hle : Theta σ (X ω) z ≤ (N : ℝ) ^ b * iterTheta 0 (PhiN N z) := by
        change _ ≤ _ * PhiN N z ^ (1 / 4 : ℝ)
        calc Theta σ (X ω) z ≤ ThetaConst τ * Lambda σ (X ω) z := hT
          _ ≤ ThetaConst τ * ((N : ℝ) ^ (b / 2) * PhiN N z ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left hcon hCT0
          _ ≤ (N : ℝ) ^ (b / 2) * ((N : ℝ) ^ (b / 2) * PhiN N z ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_right hCT (by positivity)
          _ = (N : ℝ) ^ b * PhiN N z ^ (1 / 4 : ℝ) := by rw [hsplit]; ring
      linarith
    | succ k ih =>
      intro hk D'
      have hab : (3 * (k : ℝ) + 1) * b + 3 * b ≤ τ / 4 := by
        have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
        have e : (3 * (k : ℝ) + 1) * b + 3 * b = (3 * ((k + 1 : ℕ) : ℝ) + 1) * b := by
          push_cast
          ring
        rw [e]
        calc (3 * ((k + 1 : ℕ) : ℝ) + 1) * b ≤ (3 * (K : ℝ) + 1) * b := by gcongr
          _ = εi / 4 := haK
          _ ≤ τ / 4 := by linarith
      obtain ⟨D'', N₁, h₁⟩ := iterate_step τ c C₀ C₁ K₀ C k ((3 * (k : ℝ) + 1) * b) b D' hτ hc
        (by positivity) hb0 hab
      obtain ⟨N₂, h₂⟩ := ih (by omega) D''
      refine ⟨N₁ + N₂, fun N hN Ω _ _ M σ X S hD hS hx hstab z hz => ?_⟩
      have h := h₁ N (by omega) M σ X S hD hS hx hstab
        (h₂ N (by omega) M σ X S hD hS hx hstab) z hz
      have e : (3 * ((k + 1 : ℕ) : ℝ) + 1) * b = (3 * (k : ℝ) + 1) * b + 3 * b := by
        push_cast
        ring
      rw [e]
      exact h
  -- the end of the iteration
  obtain ⟨N₁, h₁⟩ := key K le_rfl D
  obtain ⟨N₂, h₂⟩ := em_ev_rpow (p := ε / 2) (by positivity) (3 * τ⁻¹)
  refine ⟨N₁ + N₂ + 1, fun N hN Ω _ _ M σ X S hD hS hx hstab z hz => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have da := hD.densityAssumptions hτ
  have hτ1 := em_tau_le_one da
  have h := h₁ N (by omega) M σ X S hD hS hx hstab z hz
  rw [haK] at h
  obtain ⟨hΦ0, hΦ, hΦl⟩ := em_Phi hN1 (hS.1 hz)
  have hΦ1 : PhiN N z ≤ 1 :=
    hΦ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hbd : (N : ℝ) ^ (εi / 4) * iterTheta K (PhiN N z) ≤ (N : ℝ) ^ ε * PhiN N z := by
    set Φ := PhiN N z with hΦdef
    set e : ℝ := 3 / 4 * ((1 : ℝ) / 2) ^ K with he_def
    have he0 : 0 ≤ e := by positivity
    have h2K : 3 / εi ≤ (2 : ℝ) ^ K :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
    have he : e ≤ εi / 4 := by
      rw [div_le_iff₀ hεi0] at h2K
      have h2 : (0 : ℝ) < 2 ^ K := by positivity
      have e1 : e = 3 / (4 * 2 ^ K) := by rw [he_def, div_pow, one_pow]; field_simp
      rw [e1, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hθ := iterTheta_le K hΦ0.le hΦ1
    have hτN : τ * (N : ℝ)⁻¹ ≤ 1 := by
      have : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1'
      nlinarith
    have hq0 : 0 < τ * (N : ℝ)⁻¹ := by positivity
    have h1 : (τ * (N : ℝ)⁻¹) ^ (εi / 4) ≤ Φ ^ e :=
      (Real.rpow_le_rpow_of_exponent_ge hq0 hτN he).trans (Real.rpow_le_rpow hq0.le hΦl he0)
    have h2 : τ * ((N : ℝ) ^ (εi / 4))⁻¹ ≤ (τ * (N : ℝ)⁻¹) ^ (εi / 4) := by
      rw [Real.mul_rpow hτ.le (by positivity), Real.inv_rpow hN0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc τ = τ ^ (1 : ℝ) := (Real.rpow_one τ).symm
        _ ≤ τ ^ (εi / 4) := Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)
    have hpos : 0 < Φ ^ e := Real.rpow_pos_of_pos hΦ0 _
    have hNe : 0 < (N : ℝ) ^ (εi / 4) := Real.rpow_pos_of_pos hN0 _
    have h3 : Φ ^ (1 - e) ≤ Φ * ((N : ℝ) ^ (εi / 4) * τ⁻¹) := by
      rw [Real.rpow_sub hΦ0, Real.rpow_one, div_le_iff₀ hpos]
      have h4 : 1 ≤ (N : ℝ) ^ (εi / 4) * τ⁻¹ * Φ ^ e := by
        calc (1 : ℝ) = (N : ℝ) ^ (εi / 4) * τ⁻¹ * (τ * ((N : ℝ) ^ (εi / 4))⁻¹) := by
              field_simp
          _ ≤ (N : ℝ) ^ (εi / 4) * τ⁻¹ * Φ ^ e :=
              mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)
      calc Φ = Φ * 1 := (mul_one Φ).symm
        _ ≤ Φ * ((N : ℝ) ^ (εi / 4) * τ⁻¹ * Φ ^ e) := mul_le_mul_of_nonneg_left h4 hΦ0.le
        _ = Φ * ((N : ℝ) ^ (εi / 4) * τ⁻¹) * Φ ^ e := by ring
    have hNe2 : (N : ℝ) ^ (εi / 4) * (N : ℝ) ^ (εi / 4) ≤ (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h3τ := h₂ N (by omega)
    have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hN0]
      ring_nf
    calc (N : ℝ) ^ (εi / 4) * iterTheta K Φ
        ≤ (N : ℝ) ^ (εi / 4) * (3 * (Φ * ((N : ℝ) ^ (εi / 4) * τ⁻¹))) :=
          mul_le_mul_of_nonneg_left (hθ.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))
            hNe.le
      _ = (3 * τ⁻¹) * ((N : ℝ) ^ (εi / 4) * (N : ℝ) ^ (εi / 4)) * Φ := by ring
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) * Φ := by gcongr
      _ = (N : ℝ) ^ ε * Φ := by rw [hsplit]
  unfold DomAt at h ⊢
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

/-! ## Theorem 3.22 -/

/-- `√(x + y) ≤ √x + √y`. -/
private theorem em_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  have h1 : x + y ≤ (√x + √y) ^ 2 := by
    have := Real.sq_sqrt hx
    have := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc √(x + y) ≤ √((√x + √y) ^ 2) := Real.sqrt_le_sqrt h1
    _ = √x + √y := Real.sqrt_sq (by positivity)

/-- `(G − Π)_{st} = G_{st} − δ_{st} m_s`. -/
private theorem em_PiDiag_apply (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) (s t : Fin M ⊕ Fin N) :
    PiDiag N σ w s t = if s = t then mS N σ w s else 0 := by
  cases s <;> cases t <;> simp [PiDiag, mS, mI, Matrix.diagonal_apply, Matrix.one_apply]

/-- The constant of the entrywise bound. -/
private def em_KE (c τ : ℝ) : ℝ := 2 * (mAsympUpper c τ + 1) / c + 2

/-- The weighted entry of `G − Π` at `(s, t)` on `Ξ`: `≤ K (Θ_N + n Ψ_Θ)` when the bounds of
Lemma 5.2, (Gii_2) and (Gmumu-m) at `s` hold with the factor `n`. -/
private theorem em_entry_le {τ c : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ}
    (hw : w ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm w ≤ (Real.log N)⁻¹) {n : ℝ}
    (hn : 0 ≤ n) (hp1 : PsiTheta σ Xm w ≤ 1) (s t : Fin M ⊕ Fin N)
    (hZ : ‖ZS σ Xm w s‖ + LambdaO σ Xm w ≤ n * PsiTheta σ Xm w)
    (hgii : ∀ i, s = Sum.inl i → ‖giiErr σ Xm w i‖ ≤ n * (σ i * PsiTheta σ Xm w ^ 2))
    (hmu : ∀ μ, s = Sum.inr μ →
      ‖G (diagonal σ) Xm w (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) Xm w‖ ≤
        n * PsiTheta σ Xm w) :
    ‖wEnt σ (G (diagonal σ) Xm w - PiDiag N σ w) s t‖ ≤
      em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w) := by
  have hψ0 : 0 ≤ PsiTheta σ Xm w := Real.sqrt_nonneg _
  have hθ0 : 0 ≤ ThetaN σ Xm w := norm_nonneg _
  have hLo0 := em_LambdaO_nonneg hσ Xm w
  have hCas := em_Cas_nonneg (τ := τ) hc
  have hq : 0 ≤ 2 * (mAsympUpper c τ + 1) / c := by positivity
  have hb0 : 0 ≤ ThetaN σ Xm w + n * PsiTheta σ Xm w := by positivity
  have hle1 : ThetaN σ Xm w + n * PsiTheta σ Xm w ≤
      em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w) := by
    unfold em_KE
    nlinarith
  have hst0 : 0 < sigS (N := N) σ s * sigS σ t := mul_pos (em_sigS_pos hσ s) (em_sigS_pos hσ t)
  have hnorm : ‖wEnt σ (G (diagonal σ) Xm w - PiDiag N σ w) s t‖ =
      ‖G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0)‖ /
        (sigS σ s * sigS σ t) := by
    unfold wEnt
    rw [Matrix.sub_apply, em_PiDiag_apply, norm_div, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (em_sigS_pos hσ s),
      abs_of_pos (em_sigS_pos hσ t)]
  rw [hnorm]
  by_cases hst : s = t
  · subst hst
    simp only [ite_true]
    cases s with
    | inl i =>
      have hσi := hσ i
      simp only [mS, sigS, Sum.elim_inl]
      have hg0 := G_diag_ne_zero (posDef_diagonal_iff.2 hσ) Xm hw.1 (Sum.inl i)
      have hx0 : 1 + (σ i : ℂ) * mFun N σ w ≠ 0 := norm_pos_iff.1 (hc.trans_le (hx i))
      have hG := (Gtt_bound hc da hσ Xm hw hx hlog hΞ ∅ (by simp) (Sum.inl i) (by simp)).2
      rw [Gm_empty] at hG
      simp only [sigS, Sum.elim_inl] at hG
      have e : G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) - mI N σ w i =
          -G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i) *
            ((σ i : ℂ) * (mN (diagonal σ) Xm w - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i
              + giiErr σ Xm w i) / (1 + (σ i : ℂ) * mFun N σ w) := by
        rw [mI, giiErr]
        field_simp
        ring
      have hZi : ‖Zi σ Xm w i‖ ≤ n * PsiTheta σ Xm w := by
        simp only [ZS, Sum.elim_inl] at hZ
        linarith
      have hE := hgii i rfl
      have hnum : ‖(σ i : ℂ) * (mN (diagonal σ) Xm w - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i
          + giiErr σ Xm w i‖ ≤ σ i * (ThetaN σ Xm w + 2 * (n * PsiTheta σ Xm w)) := by
        refine norm_add₃_le.trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσi]
        have h1 : σ i * ‖mN (diagonal σ) Xm w - mFun N σ w‖ = σ i * ThetaN σ Xm w := rfl
        have h2 := mul_le_mul_of_nonneg_left hZi hσi.le
        have h3 : n * (σ i * PsiTheta σ Xm w ^ 2) ≤ σ i * (n * PsiTheta σ Xm w) := by
          have : PsiTheta σ Xm w ^ 2 ≤ PsiTheta σ Xm w := by nlinarith
          calc n * (σ i * PsiTheta σ Xm w ^ 2) = σ i * n * PsiTheta σ Xm w ^ 2 := by ring
            _ ≤ σ i * n * PsiTheta σ Xm w := mul_le_mul_of_nonneg_left this (by positivity)
            _ = σ i * (n * PsiTheta σ Xm w) := by ring
        nlinarith
      rw [e, norm_div, norm_mul, norm_neg, div_le_iff₀ (by positivity)]
      have hw0 : 0 < ‖1 + (σ i : ℂ) * mFun N σ w‖ := hc.trans_le (hx i)
      rw [div_le_iff₀ hw0]
      calc ‖G (diagonal σ) Xm w (Sum.inl i) (Sum.inl i)‖ *
            ‖(σ i : ℂ) * (mN (diagonal σ) Xm w - mFun N σ w) + (σ i : ℂ) * Zi σ Xm w i +
              giiErr σ Xm w i‖
          ≤ ((mAsympUpper c τ + 1) * σ i) * (σ i * (ThetaN σ Xm w + 2 * (n * PsiTheta σ Xm w))) :=
            mul_le_mul hG hnum (norm_nonneg _) (by positivity)
        _ = σ i * σ i * ((mAsympUpper c τ + 1) / c * (ThetaN σ Xm w + 2 * (n * PsiTheta σ Xm w)))
              * c := by field_simp
        _ ≤ σ i * σ i * (em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w)) * c := by
            have hin : (mAsympUpper c τ + 1) / c * (ThetaN σ Xm w + 2 * (n * PsiTheta σ Xm w)) ≤
                em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w) := by
              unfold em_KE
              have hq' : 0 ≤ (mAsympUpper c τ + 1) / c := by positivity
              have e2 : 2 * (mAsympUpper c τ + 1) / c = 2 * ((mAsympUpper c τ + 1) / c) := by
                ring
              rw [e2]
              have hnp : 0 ≤ n * PsiTheta σ Xm w := by positivity
              nlinarith [mul_nonneg hq' hθ0, mul_nonneg hq' hnp]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hin (by positivity)) hc.le
        _ ≤ em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w) * (σ i * σ i) *
              ‖1 + (σ i : ℂ) * mFun N σ w‖ := by
            have h0 : 0 ≤ em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w) := by
              have : 0 ≤ em_KE c τ := by unfold em_KE; positivity
              positivity
            have := mul_le_mul_of_nonneg_left (hx i) (by positivity :
              0 ≤ σ i * σ i * (em_KE c τ * (ThetaN σ Xm w + n * PsiTheta σ Xm w)))
            linarith
    | inr μ =>
      simp only [mS, sigS, Sum.elim_inr, mul_one, div_one]
      have e := norm_sub_le_norm_sub_add_norm_sub
        (G (diagonal σ) Xm w (Sum.inr μ) (Sum.inr μ)) (mN (diagonal σ) Xm w) (mFun N σ w)
      have h1 := hmu μ rfl
      have h2 : ‖mN (diagonal σ) Xm w - mFun N σ w‖ = ThetaN σ Xm w := rfl
      linarith
  · simp only [hst, ite_false, sub_zero]
    have h1 := em_offdiag_le (σ := σ) Xm w hst
    have h2 : LambdaO σ Xm w ≤ n * PsiTheta σ Xm w := by
      linarith [norm_nonneg (ZS σ Xm w s)]
    linarith

/-- Theorem 3.22 (`thm:diag_gen`). -/
theorem diag_gen (τ c C₀ C₁ K₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S →
      EntrywiseLawAt N ε D (diagonal σ) X S ∧ AveragedLawAt N ε D (diagonal σ) X S := by
  obtain ⟨N₁, h₁⟩ := theta_averaged τ c C₀ C₁ K₀ C ε D hτ hc hε
  obtain ⟨N₂, h₂⟩ := theta_averaged τ c C₀ C₁ K₀ C (ε / 4) (D + 1) hτ hc (by positivity)
  obtain ⟨N₃, h₃⟩ := weak_law τ c C₀ C₁ K₀ C (τ / 8) (D + 1) hτ hc (by positivity)
  obtain ⟨N₄, h₄⟩ := lambdaO_Z_bound τ c C (ε / 4) (D + 1) hτ hc (by positivity)
  obtain ⟨N₅, h₅⟩ := Gii_2 τ c C (ε / 4) (D + 1 + 0) hτ hc (by positivity)
  obtain ⟨N₆, h₆⟩ := Gmumu_m τ c C (ε / 4) (D + 1 + 0) hτ hc (by positivity)
  obtain ⟨N₇, h₇⟩ := em_ev_log (p := τ / 8) (by positivity) (em_xiThr_pos hτ hc)
  obtain ⟨N₈, h₈⟩ := em_ev_rpow (p := ε / 2) (by positivity) (2 * em_KE c τ)
  obtain ⟨N₉, h₉⟩ := em_ev_rpow hτ (mBoundConst τ + ThetaConst τ)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉ + 5,
    fun N hN Ω _ _ M σ X S hD hS hx hstab => ⟨?_, ?_⟩⟩
  · have hN1 : 1 ≤ N := by omega
    have hNpos : 0 < N := hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have da := hD.densityAssumptions hτ
    have hσ := hD.pos
    obtain ⟨hlog, hlog1, hsmall⟩ := h₇ N (by omega)
    rw [entrywiseLawAt_diagonal_iff hσ (fun z hz => (hS.1 hz).1)]
    intro z hz s t
    have hzD := hS.1 hz
    have P1 := h₃ N (by omega) M σ X S hD hS hx hstab z hz
    have P2 := h₂ N (by omega) M σ X S hD hS hx hstab z hz
    have P3 := h₄ N (by omega) M σ X hD z hzD (hx z hz) s
    have hcI : ((Finset.univ.filter (fun i : Fin M => s = Sum.inl i)).card : ℝ) ≤
        (N : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_zero]
      exact_mod_cast Finset.card_le_one.2 fun i hi j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        exact Sum.inl_injective (hi.symm.trans hj)
    have hcM : ((Finset.univ.filter (fun μ : Fin N => s = Sum.inr μ)).card : ℝ) ≤
        (N : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_zero]
      exact_mod_cast Finset.card_le_one.2 fun i hi j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        exact Sum.inr_injective (hi.symm.trans hj)
    have P4 := DomAt.measure_exists_lt (D := D + 1) (C := 0)
      (Finset.univ.filter (fun i : Fin M => s = Sum.inl i)) hN1 hcI
      (ξ := fun i ω => xiInd σ (X ω) z * ‖giiErr σ (X ω) z i‖)
      (ζ := fun i ω => σ i * PsiTheta σ (X ω) z ^ 2)
      (fun i _ => h₅ N (by omega) M σ X hD z hzD (hx z hz) i)
    have P5 := DomAt.measure_exists_lt (D := D + 1) (C := 0)
      (Finset.univ.filter (fun μ : Fin N => s = Sum.inr μ)) hN1 hcM
      (ξ := fun μ ω => xiInd σ (X ω) z *
        ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr μ) - mN (diagonal σ) (X ω) z‖)
      (ζ := fun μ ω => PsiTheta σ (X ω) z)
      (fun μ _ => h₆ N (by omega) M σ X hD z hzD (hx z hz) μ)
    unfold ODomAt DomAt
    unfold DomAt at P1 P2 P3
    refine em_union5 (by omega) P1 P2 P3 P4 P5 (fun ω hω => ?_)
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨n1, n2, n3, n4, n5⟩ := hcon
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt, Finset.mem_filter,
      Finset.mem_univ, true_and] at n1 n2 n3 n4 n5 hω
    set n := (N : ℝ) ^ (ε / 4) with hn
    have hn1 : 1 ≤ n := Real.one_le_rpow hN1' (by positivity)
    have hΞ := em_xi hNpos (X ω) hzD hsmall n1
    have hxi := em_xiInd hΞ
    rw [hxi, one_mul] at n3
    obtain ⟨hΦ0, hΦ, -⟩ := em_Phi hNpos hzD
    obtain ⟨him, himC, -⟩ := em_imm hNpos da hzD
    have hθ0 : 0 ≤ Theta σ (X ω) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    -- `Ψ_Θ ≤ 1`
    have hp1 : PsiTheta σ (X ω) z ≤ 1 := by
      have hT := Theta_le_Lambda da hσ (X ω) z hNpos
      have hCT0 : 0 ≤ ThetaConst τ := by unfold ThetaConst; positivity
      have hT1 : Theta σ (X ω) z ≤ ThetaConst τ :=
        hT.trans ((mul_le_mul_of_nonneg_left (hΞ.trans hlog1) hCT0).trans (mul_one _).le)
      have hNτ := h₉ N (by omega)
      have hNτ0 : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 _
      have hΦ' : PhiN N z ≤ ((N : ℝ) ^ τ)⁻¹ := by rw [← Real.rpow_neg hN0.le]; exact hΦ
      have h1 : ((mFun N σ z).im + Theta σ (X ω) z) * PhiN N z ≤ 1 := by
        calc ((mFun N σ z).im + Theta σ (X ω) z) * PhiN N z
            ≤ (mBoundConst τ + ThetaConst τ) * ((N : ℝ) ^ τ)⁻¹ :=
              mul_le_mul (add_le_add himC hT1) hΦ' hΦ0.le (by
                have := em_Cm_pos hτ
                positivity)
          _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hNτ0]; exact hNτ
      unfold PsiTheta
      exact Real.sqrt_le_one.mpr h1
    have hent := em_entry_le hc da hσ (X ω) hzD (hx z hz) hlog hΞ (by positivity) hp1 s t n3
      (fun i hi => by have := n4 i hi; rwa [hxi, one_mul] at this)
      (fun μ hμ => by have := n5 μ hμ; rwa [hxi, one_mul] at this)
    -- `Θ_N ≤ n Ψ` and `Ψ_Θ ≤ n Ψ`
    have hPsi : Psi N σ z = √((mFun N σ z).im * PhiN N z) + PhiN N z := by
      unfold Psi PhiN
      rw [div_eq_mul_inv, one_div]
    have hPsi0 : 0 ≤ √((mFun N σ z).im * PhiN N z) := Real.sqrt_nonneg _
    have hThN : ThetaN σ (X ω) z ≤ n * Psi N σ z := by
      have h1 : ThetaN σ (X ω) z ≤ Theta σ (X ω) z := le_add_of_nonneg_left (norm_nonneg _)
      rw [hPsi]
      nlinarith
    have hpsiPsi : PsiTheta σ (X ω) z ≤ n * Psi N σ z := by
      unfold PsiTheta
      have hx0 : 0 ≤ (mFun N σ z).im * PhiN N z := by positivity
      have hy0 : 0 ≤ Theta σ (X ω) z * PhiN N z := by positivity
      have h1 : √(((mFun N σ z).im + Theta σ (X ω) z) * PhiN N z) ≤
          √((mFun N σ z).im * PhiN N z) + √(Theta σ (X ω) z * PhiN N z) := by
        rw [add_mul]
        exact em_sqrt_add hx0 hy0
      have h2 : √(Theta σ (X ω) z * PhiN N z) ≤ n * PhiN N z := by
        have h3 : Theta σ (X ω) z * PhiN N z ≤ (n * PhiN N z) ^ 2 := by
          have : Theta σ (X ω) z * PhiN N z ≤ n * PhiN N z * PhiN N z :=
            mul_le_mul_of_nonneg_right n2 hΦ0.le
          nlinarith
        calc √(Theta σ (X ω) z * PhiN N z) ≤ √((n * PhiN N z) ^ 2) := Real.sqrt_le_sqrt h3
          _ = n * PhiN N z := Real.sqrt_sq (by positivity)
      rw [hPsi]
      nlinarith
    have hKE0 : 0 ≤ em_KE c τ := by have := em_Cas_nonneg (τ := τ) hc; unfold em_KE; positivity
    have hPsi00 : 0 ≤ Psi N σ z := by rw [hPsi]; positivity
    have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (n * n) := by
      rw [hn, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      ring_nf
    have hK := h₈ N (by omega)
    have hfin : em_KE c τ * (ThetaN σ (X ω) z + n * PsiTheta σ (X ω) z) ≤
        (N : ℝ) ^ ε * Psi N σ z := by
      calc em_KE c τ * (ThetaN σ (X ω) z + n * PsiTheta σ (X ω) z)
          ≤ em_KE c τ * (n * n * Psi N σ z + n * (n * Psi N σ z)) := by
            gcongr
            calc ThetaN σ (X ω) z ≤ n * Psi N σ z := hThN
              _ ≤ n * n * Psi N σ z := by
                have := mul_le_mul_of_nonneg_right hn1 (mul_nonneg (by positivity) hPsi00 :
                  0 ≤ n * Psi N σ z)
                nlinarith
        _ = 2 * em_KE c τ * (n * n) * Psi N σ z := by ring
        _ ≤ (N : ℝ) ^ (ε / 2) * (n * n) * Psi N σ z := by gcongr
        _ = (N : ℝ) ^ ε * Psi N σ z := by rw [hsplit]
    linarith
  · rw [averagedLawAt_diagonal_iff]
    intro z hz
    have hN1 : 1 ≤ N := by omega
    unfold ODomAt
    refine DomAt.mono hN1 (fun ω => le_add_of_nonneg_left (norm_nonneg _))
      (fun _ => (one_div _).ge) (fun _ => ?_) le_rfl le_rfl
      (h₁ N (by omega) M σ X S hD hS hx hstab z hz)
    have := (hS.1 hz).1
    positivity

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `S = {2i}` -/

section Checks

/-- Theorem 3.22 at `τ = 1/2`, `c = 1`, `C₀ = C₁ = 4`, `K₀ = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X → SpectralDomain (1 / 2) N S → OneXmOn 1 N σ S →
    StableOn 4 4 1 N σ S →
    EntrywiseLawAt N 1 1 (diagonal σ) X S ∧ AveragedLawAt N 1 1 (diagonal σ) X S :=
  diag_gen (1 / 2) 1 4 4 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- One step of the iteration as a conditional instance at `τ = 1/2`, `c = 1`,
`C₀ = C₁ = 4`, `K₀ = 1`, `C_p = 2`, `k = 0`, `a = 1/80`, `b = 1/80`, `D = 1`: the hypotheses
of the model and `Θ ≺ θ_0` are binders. -/
example : ∃ D' : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X → SpectralDomain (1 / 2) N S → OneXmOn 1 N σ S →
    StableOn 4 4 1 N σ S →
    (∀ z ∈ S, DomAt N (1 / 80) D' (fun ω => Theta σ (X ω) z)
      (fun _ => iterTheta 0 (PhiN N z))) →
    ∀ z ∈ S, DomAt N (1 / 80 + 3 * (1 / 80)) 1 (fun ω => Theta σ (X ω) z)
      (fun _ => iterTheta (0 + 1) (PhiN N z)) :=
  iterate_step (1 / 2) 1 4 4 1 (fun _ => 2) 0 (1 / 80) (1 / 80) 1 (by norm_num) one_pos
    (by norm_num) (by norm_num) (by norm_num)

/-- `Θ ≺ Φ` as a conditional instance at `τ = 1/2`, `c = 1`, `C₀ = C₁ = 4`, `K₀ = 1`,
`C_p = 2`, `ε = D = 1`: the hypotheses of the model are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X → SpectralDomain (1 / 2) N S → OneXmOn 1 N σ S →
    StableOn 4 4 1 N σ S →
    ∀ z ∈ S, DomAt N 1 1 (fun ω => Theta σ (X ω) z) (fun _ => PhiN N z) :=
  theta_averaged (1 / 2) 1 4 4 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

end Checks

end Anisotropic

end

#print axioms Anisotropic.iterate_step
#print axioms Anisotropic.theta_averaged
#print axioms Anisotropic.diag_gen
