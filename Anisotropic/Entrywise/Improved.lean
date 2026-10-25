import Anisotropic.Entrywise.Main

/-! # (improved_avg_G) for `Σ = diag(σ)`

Section 10.1, proof of Lemma 10.1: for `Σ = diag(σ)`, on a spectral domain `S` on which
(1+xm), the stability of Definition 5.4 and the strong stability of Definition A.2 hold,
`|m_N − m| ≺ (κ + η)^{−1/2} Ψ²` ((improved_avg_G)). The proof reruns the argument of Section 5
with the strong stability.

Write `Φ = (Nη)⁻¹`, `X = (Im m + Φ) Φ`, `s = min(ε, τ)/2` and `a = s/3`. By the averaged law
(`Θ ≺ Φ`, from the stability of Definition 5.4), `Ψ_Θ² ≤ N^a X` with high probability. At every
point `w` of the lattice `z_k = z + i k N⁻⁵` set `Υ = (N^a X + N⁻¹)^{1/2}`; then
`N^{−1/2} ≤ Υ ≤ N^{−τ/4}`, `Λ ≺ N^{−τ/4}` (Proposition 5.1) and `Λ_o ≺ Υ` (Lemma 5.2), so that
Lemma 5.6 and Lemma 5.3 give `|f(m_N) − w| ≤ δ(w) = N^s X(w)`. The strong stability along the
lattice gives `|m_N − m| ≤ max(C₀, C₁) δ/(√(κ + η) + √δ) ≤ max(C₀, C₁) N^s X (κ + η)^{−1/2}`,
and `X ≤ Ψ²`. -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Elementary facts on `𝐃(τ, N)` -/

/-- `C_m > 0`. -/
private theorem imp_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

/-- `0 < Φ ≤ N^{−τ}` on `𝐃(τ,N)`. -/
private theorem imp_Phi {τ : ℝ} {N : ℕ} (hN : 0 < N) {w : ℂ}
    (hw : w ∈ specDomain τ N) : 0 < PhiN N w ∧ PhiN N w ≤ (N : ℝ) ^ (-τ) := by
  obtain ⟨h0, -, -, hη, -⟩ := hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by unfold PhiN; positivity, ?_⟩
  have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [Real.rpow_add hN0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
  have hx : (N : ℝ) ^ τ ≤ (N : ℝ) * w.im := by
    rw [← e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  unfold PhiN
  rw [Real.rpow_neg hN0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hx

/-- `0 < Im m ≤ C_m` and `N⁻¹ ≤ C_m Im m Φ` on `𝐃(τ,N)`. -/
private theorem imp_imm {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (da : DensityAssumptions τ N σ) {w : ℂ} (hw : w ∈ specDomain τ N) :
    0 < (mFun N σ w).im ∧ (mFun N σ w).im ≤ mBoundConst τ ∧
      (N : ℝ)⁻¹ ≤ mBoundConst τ * ((mFun N σ w).im * PhiN N w) := by
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain da hw
  have hC := imp_Cm_pos da.pos
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

/-- `τ ≤ 1` under the density assumptions. -/
private theorem imp_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (da : DensityAssumptions τ N σ) :
    τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := da.phi_lower.trans da.phi_upper
  by_contra hc
  push Not at hc
  linarith [inv_lt_one_of_one_lt₀ hc]

/-- `Φ^{1/4} ≤ N^{−τ/4}` on `𝐃(τ,N)`. -/
private theorem imp_Phi_quarter {τ : ℝ} {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : w ∈ specDomain τ N) :
    PhiN N w ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (-(τ / 4)) := by
  obtain ⟨hΦ0, hΦ⟩ := imp_Phi hN hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc PhiN N w ^ (1 / 4 : ℝ) ≤ ((N : ℝ) ^ (-τ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hΦ0.le hΦ (by norm_num)
    _ = (N : ℝ) ^ (-(τ / 4)) := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring

/-- `1 + N⁻⁵ ≤ τ⁻¹` when `Im z < 1` on `𝐃(τ,N)`, given `N⁻⁵ ≤ τ⁻¹ − 1` for `τ < 1`. -/
private theorem imp_top {τ : ℝ} {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ specDomain τ N)
    (h : τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1) : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ := by
  intro him
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hτlt : τ < 1 := by
    by_contra hc
    push Not at hc
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) := Real.one_le_rpow hN1 (by linarith)
    linarith [hz.2.2.2.1]
  linarith [h hτlt]

/-! ## Size conditions -/

/-- `K ≤ N^p` for all large `N`. -/
private theorem imp_ev_rpow {p : ℝ} (hp : 0 < p) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K ≤ (N : ℝ) ^ p := by
  have := (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.1 (this.eventually_ge_atTop K)
  exact ⟨N₀, h⟩

/-- `N^{−p} ≤ (log N)⁻¹` for all large `N`. -/
private theorem imp_ev_log {p : ℝ} (hp : 0 < p) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (N : ℝ) ^ (-p) ≤ (Real.log N)⁻¹ := by
  have e1 : ∀ᶠ y : ℝ in atTop, ‖Real.log y‖ ≤ 1 * ‖y ^ p‖ :=
    (isLittleO_log_rpow_atTop hp).def one_pos
  have e2 : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have e3 : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ y := eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually ((e1.and e2).and e3))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN₀ N hN
  set y : ℝ := (N : ℝ)
  have hy0 : 0 < y := by linarith
  have hlg0 : 0 < Real.log y := by linarith
  have hp' : 0 < y ^ p := Real.rpow_pos_of_pos hy0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlg0, abs_of_pos hp', one_mul] at h1
  rw [Real.rpow_neg hy0.le]
  exact inv_anti₀ hlg0 h1

/-- `N⁻⁵ ≤ τ⁻¹ − 1` when `τ < 1`, for all large `N`. -/
private theorem imp_ev_tau {τ : ℝ} (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1 := by
  refine ⟨⌈(τ⁻¹ - 1)⁻¹⌉₊ + 1, fun N hN hτ1 => ?_⟩
  have hpos : 0 < τ⁻¹ - 1 := by linarith [(one_lt_inv₀ hτ).2 hτ1]
  have hx : (τ⁻¹ - 1)⁻¹ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(τ⁻¹ - 1)⁻¹⌉₊ ≤ N))
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  calc ((N : ℝ) ^ 5)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ (by positivity) (le_self_pow₀ hx1 (by norm_num))
    _ ≤ ((τ⁻¹ - 1)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hpos) hx
    _ = τ⁻¹ - 1 := inv_inv _

/-- `N⁵ + 2 ≤ N⁹` for `N ≥ 2`. -/
private theorem imp_card {N : ℕ} (h2 : 2 ≤ N) : (N : ℝ) ^ 5 + 2 ≤ (N : ℝ) ^ (9 : ℝ) := by
  have e : (N : ℝ) ^ (9 : ℝ) = (N : ℝ) ^ (9 : ℕ) := by exact_mod_cast Real.rpow_natCast (N : ℝ) 9
  rw [e]
  have hx2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
  set x : ℝ := (N : ℝ)
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h4 : (2 : ℝ) ≤ x ^ 4 := by nlinarith [pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 4)]
  have h5 : x ^ 5 * 2 ≤ x ^ 5 * x ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h1 : (1 : ℝ) ≤ x ^ 5 := one_le_pow₀ hx1
  have : x ^ 9 = x ^ 5 * x ^ 4 := by ring
  nlinarith

/-! ## Unions of events -/

/-- `n` events of probability at most `N^{−(D+1)}` each, `n ≤ N`: their union has probability at
most `N^{−D}`. -/
private theorem imp_union {Ω : Type} [MeasureSpace Ω] {N n : ℕ} {D : ℝ} (hN : 1 ≤ N)
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

/-- Three events of probability at most `N^{−(D+1)}`, `N ≥ 3`. -/
private theorem imp_union3 {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : 3 ≤ N)
    {A B₁ B₂ B₃ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hA : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃) : ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  refine imp_union (n := 3) (by omega) hN ![B₁, B₂, B₃]
    (fun j => by fin_cases j; exacts [h₁, h₂, h₃]) fun ω hω => ?_
  rcases hA ω hω with h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

/-- Five events of probability at most `N^{−(D+1)}`, `N ≥ 5`. -/
private theorem imp_union5 {Ω : Type} [MeasureSpace Ω] {N : ℕ} {D : ℝ} (hN : 5 ≤ N)
    {A B₁ B₂ B₃ B₄ B₅ : Set Ω} (h₁ : ℙ B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₂ : ℙ B₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₄ : ℙ B₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (h₅ : ℙ B₅ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hA : ∀ ω ∈ A, ω ∈ B₁ ∨ ω ∈ B₂ ∨ ω ∈ B₃ ∨ ω ∈ B₄ ∨ ω ∈ B₅) :
    ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  refine imp_union (n := 5) (by omega) hN ![B₁, B₂, B₃, B₄, B₅]
    (fun j => by fin_cases j; exacts [h₁, h₂, h₃, h₄, h₅]) fun ω hω => ?_
  rcases hA ω hω with h | h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]

/-! ## The bound at one lattice point -/

/-- `Λ ≤ N^{τ/8} Φ^{1/4}` gives `Ξ` once `N^{−τ/8} ≤ (log N)⁻¹`. -/
private theorem imp_xi {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : w ∈ specDomain τ N)
    (hsmall : (N : ℝ) ^ (-(τ / 8)) ≤ (Real.log N)⁻¹)
    (hL : Lambda σ Xm w ≤ (N : ℝ) ^ (τ / 8) * PhiN N w ^ (1 / 4 : ℝ)) :
    xiInd σ Xm w = 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (N : ℝ) ^ (τ / 8) * (N : ℝ) ^ (-(τ / 4)) = (N : ℝ) ^ (-(τ / 8)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have h : Lambda σ Xm w ≤ (Real.log N)⁻¹ :=
    calc Lambda σ Xm w ≤ (N : ℝ) ^ (τ / 8) * PhiN N w ^ (1 / 4 : ℝ) := hL
      _ ≤ (N : ℝ) ^ (τ / 8) * (N : ℝ) ^ (-(τ / 4)) :=
          mul_le_mul_of_nonneg_left (imp_Phi_quarter hN hw) (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (-(τ / 8)) := h2
      _ ≤ (Real.log N)⁻¹ := hsmall
  simp [xiInd, h]

/-- `‖[Z]_M‖ ≤ τ⁻¹ ‖M⁻¹ Σ_i σ_i² (1 + m_N σ_i)⁻² Z_i‖`. -/
private theorem imp_ZM_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
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

/-- `Υ = (N^a (Im m + Φ) Φ + N⁻¹)^{1/2}`, the control parameter of Lemma 5.6. -/
private def imp_Ups (N : ℕ) (σ : Fin M → ℝ) (a : ℝ) (w : ℂ) : ℝ :=
  √((N : ℝ) ^ a * (((mFun N σ w).im + PhiN N w) * PhiN N w) + (N : ℝ)⁻¹)

/-- `Υ² = N^a X + N⁻¹` and `N^{−1/2} ≤ Υ ≤ N^{−τ/4}` on `𝐃(τ,N)`, `X = (Im m + Φ) Φ`, once
`C_m + 4 ≤ N^{τ/4}`. -/
private theorem imp_Ups_facts {τ a : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 1 ≤ N)
    (da : DensityAssumptions τ N σ) {w : ℂ} (hw : w ∈ specDomain τ N)
    (haτ : a ≤ τ / 4) (hv : mBoundConst τ + 4 ≤ (N : ℝ) ^ (τ / 4)) :
    imp_Ups N σ a w ^ 2 =
        (N : ℝ) ^ a * (((mFun N σ w).im + PhiN N w) * PhiN N w) + (N : ℝ)⁻¹ ∧
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ imp_Ups N σ a w ∧ imp_Ups N σ a w ≤ (N : ℝ) ^ (-(τ / 4)) := by
  have hτ := da.pos
  have hτ1 := imp_tau_le_one da
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hΦ0, hΦ⟩ := imp_Phi (by omega) hw
  obtain ⟨him, himC, -⟩ := imp_imm (by omega) da hw
  have hC := imp_Cm_pos hτ
  have hΦ1 : PhiN N w ≤ 1 :=
    hΦ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
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
  set X := ((mFun N σ w).im + PhiN N w) * PhiN N w with hXdef
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
  have hsq : imp_Ups N σ a w ^ 2 = (N : ℝ) ^ a * X + (N : ℝ)⁻¹ := Real.sq_sqrt hsum0
  refine ⟨hsq, ?_, ?_⟩
  · have e : (N : ℝ) ^ (-(1 / 2 : ℝ)) = √((N : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
    rw [e]
    exact Real.sqrt_le_sqrt (by have := mul_nonneg hNa0 hX0; linarith)
  · rw [hv2]
    calc imp_Ups N σ a w ≤ √((v ^ 2)⁻¹) := Real.sqrt_le_sqrt hsum
      _ = v⁻¹ := by rw [Real.sqrt_inv, Real.sqrt_sq hv0.le]

/-- `Ψ_Θ ≤ Υ` when `Θ ≤ N^a Φ`, `a ≥ 0`. -/
private theorem imp_psi_le_ups {a : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 1 ≤ N)
    (hσ : ∀ i, 0 ≤ σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ} (hw : 0 < w.im) (ha : 0 ≤ a)
    (hT : Theta σ Xm w ≤ (N : ℝ) ^ a * PhiN N w) :
    PsiTheta σ Xm w ≤ imp_Ups N σ a w := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha
  have him : 0 < (mFun N σ w).im := (mFun_spec N σ hσ hw).1
  have hΦ0 : 0 ≤ PhiN N w := by unfold PhiN; positivity
  have h1 : (mFun N σ w).im + Theta σ Xm w ≤ (N : ℝ) ^ a * ((mFun N σ w).im + PhiN N w) := by
    nlinarith
  have h : ((mFun N σ w).im + Theta σ Xm w) * PhiN N w ≤
      (N : ℝ) ^ a * (((mFun N σ w).im + PhiN N w) * PhiN N w) := by
    calc ((mFun N σ w).im + Theta σ Xm w) * PhiN N w
        ≤ (N : ℝ) ^ a * ((mFun N σ w).im + PhiN N w) * PhiN N w :=
          mul_le_mul_of_nonneg_right h1 hΦ0
      _ = (N : ℝ) ^ a * (((mFun N σ w).im + PhiN N w) * PhiN N w) := by ring
  unfold PsiTheta imp_Ups
  refine Real.sqrt_le_sqrt (h.trans ?_)
  have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  linarith

/-- The self-consistent bound at a lattice point: on `Ξ`, with Lemma 5.3, Lemma 5.6 and
`Θ ≤ N^a Φ`, `|f(m_N) − w| ≤ N^{3a} (Im m + Φ) Φ`. -/
private theorem imp_close {τ a : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hN : 0 < N)
    (da : DensityAssumptions τ N σ) (Xm : Matrix (Fin M) (Fin N) ℝ) {w : ℂ}
    (hw : w ∈ specDomain τ N) (ha : 0 ≤ a)
    (hK : 1 + (1 + τ⁻¹) * (1 + mBoundConst τ) ≤ (N : ℝ) ^ a)
    (hxi : xiInd σ Xm w = 1)
    (hD : xiInd σ Xm w * ‖calDErr σ Xm w‖ ≤ (N : ℝ) ^ a * PsiTheta σ Xm w ^ 2)
    (hZN : ‖ZN σ Xm w‖ ≤ (N : ℝ) ^ a * imp_Ups N σ a w ^ 2)
    (hZM : ‖ZMavg σ Xm w‖ ≤ (N : ℝ) ^ a * imp_Ups N σ a w ^ 2)
    (hY : imp_Ups N σ a w ^ 2 =
      (N : ℝ) ^ a * (((mFun N σ w).im + PhiN N w) * PhiN N w) + (N : ℝ)⁻¹)
    (hT : Theta σ Xm w ≤ (N : ℝ) ^ a * PhiN N w) :
    ‖fC N σ (mN (diagonal σ) Xm w) - w‖ ≤ iterDelta N σ (3 * a) (fun Φ => Φ) w := by
  have hτ := da.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hΦ0, -⟩ := imp_Phi hN hw
  obtain ⟨him, -, hinv⟩ := imp_imm hN da hw
  have hC := imp_Cm_pos hτ
  have hP1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha
  have hPQ : (N : ℝ) ^ (3 * a) = (N : ℝ) ^ a * (N : ℝ) ^ a * (N : ℝ) ^ a := by
    rw [show 3 * a = a + a + a by ring, Real.rpow_add hN0, Real.rpow_add hN0]
  have eδ : iterDelta N σ (3 * a) (fun Φ => Φ) w =
      (N : ℝ) ^ (3 * a) * (((mFun N σ w).im + PhiN N w) * PhiN N w) := by
    unfold iterDelta
    ring
  set P := (N : ℝ) ^ a with hPdef
  set X := ((mFun N σ w).im + PhiN N w) * PhiN N w with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hθ0 : 0 ≤ Theta σ Xm w := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpsi : PsiTheta σ Xm w ^ 2 ≤ P * X := by
    unfold PsiTheta
    rw [Real.sq_sqrt (by positivity)]
    have h1 : (mFun N σ w).im + Theta σ Xm w ≤ P * ((mFun N σ w).im + PhiN N w) := by nlinarith
    calc ((mFun N σ w).im + Theta σ Xm w) * PhiN N w
        ≤ P * ((mFun N σ w).im + PhiN N w) * PhiN N w := mul_le_mul_of_nonneg_right h1 hΦ0.le
      _ = P * X := by rw [hXdef]; ring
  have hImX : (mFun N σ w).im * PhiN N w ≤ X := by
    have : 0 ≤ PhiN N w * PhiN N w := by positivity
    rw [hXdef]
    nlinarith
  have hPX : X ≤ P * X := le_mul_of_one_le_left hX0 hP1
  have hY2 : imp_Ups N σ a w ^ 2 ≤ (1 + mBoundConst τ) * (P * X) := by
    rw [hY]
    have h1 : (N : ℝ)⁻¹ ≤ mBoundConst τ * X :=
      hinv.trans (mul_le_mul_of_nonneg_left hImX hC.le)
    have h2 : mBoundConst τ * X ≤ mBoundConst τ * (P * X) := mul_le_mul_of_nonneg_left hPX hC.le
    nlinarith
  have e : fC N σ (mN (diagonal σ) Xm w) - w = calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w := by
    unfold calDErr
    ring
  rw [hxi, one_mul] at hD
  have hZM' := imp_ZM_le hN da Xm w
  have hQ0 : 0 ≤ P := by linarith
  have b1 : ‖calDErr σ Xm w‖ ≤ P * (P * X) := hD.trans (mul_le_mul_of_nonneg_left hpsi hQ0)
  have b2 : ‖ZN σ Xm w‖ ≤ P * ((1 + mBoundConst τ) * (P * X)) :=
    hZN.trans (mul_le_mul_of_nonneg_left hY2 hQ0)
  have b3 : ‖ZM σ Xm w‖ ≤ τ⁻¹ * (P * ((1 + mBoundConst τ) * (P * X))) :=
    hZM'.trans (mul_le_mul_of_nonneg_left (hZM.trans (mul_le_mul_of_nonneg_left hY2 hQ0))
      (inv_pos.2 hτ).le)
  rw [e, eδ, hPQ]
  calc ‖calDErr σ Xm w + ZN σ Xm w + ZM σ Xm w‖
      ≤ ‖calDErr σ Xm w‖ + ‖ZN σ Xm w‖ + ‖ZM σ Xm w‖ := norm_add₃_le
    _ ≤ P * (P * X) + P * ((1 + mBoundConst τ) * (P * X)) +
          τ⁻¹ * (P * ((1 + mBoundConst τ) * (P * X))) := add_le_add (add_le_add b1 b2) b3
    _ = (1 + (1 + τ⁻¹) * (1 + mBoundConst τ)) * (P * P * X) := by ring
    _ ≤ P * (P * P * X) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = P * P * P * X := by ring

/-- `Ψ² ≥ (Im m + Φ) Φ`. -/
private theorem imp_X_le_Psi_sq {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {z : ℂ}
    (hz : 0 < z.im) : ((mFun N σ z).im + PhiN N z) * PhiN N z ≤ Psi N σ z ^ 2 := by
  have hPsi : Psi N σ z = √((mFun N σ z).im * PhiN N z) + PhiN N z := by
    unfold Psi PhiN
    rw [div_eq_mul_inv, one_div]
  have him : 0 < (mFun N σ z).im := (mFun_spec N σ hσ hz).1
  have hΦ0 : 0 ≤ PhiN N z := by unfold PhiN; positivity
  have hs := Real.sq_sqrt (mul_nonneg him.le hΦ0)
  have hs0 := Real.sqrt_nonneg ((mFun N σ z).im * PhiN N z)
  rw [hPsi]
  nlinarith [mul_nonneg hs0 hΦ0]

/-- The rerun at one `ω`: the bounds of Proposition 5.1, Lemma 5.3, Lemma 5.6 and `Θ ≤ N^a Φ`
along the lattice, and the strong stability, give
`|m_N − m| ≤ max(C₀, C₁, 0) N^{3a} (κ + η)^{−1/2} Ψ²` at `z`. -/
private theorem imp_det {τ C₀ C₁ K₀ a : ℝ} {N : ℕ} (hN : 1 ≤ N)
    {σ : Fin M → ℝ} (da : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {S : Set ℂ} (hS : SpectralDomain τ N S)
    (hstab : StronglyStableOn C₀ C₁ K₀ N σ S) (ha : 0 ≤ a) (haτ : a ≤ τ / 4)
    (hδ : AdmissibleDelta N S (iterDelta N σ (3 * a) fun Φ => Φ))
    {z : ℂ} (hz : z ∈ S) (hτN : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹)
    (hsmall : (N : ℝ) ^ (-(τ / 8)) ≤ (Real.log N)⁻¹)
    (hv : mBoundConst τ + 4 ≤ (N : ℝ) ^ (τ / 4))
    (hK : 1 + (1 + τ⁻¹) * (1 + mBoundConst τ) ≤ (N : ℝ) ^ a)
    (hL : ∀ j ≤ latticeTop N z, Lambda σ Xm (latticePt N z j) ≤
      (N : ℝ) ^ (τ / 8) * PhiN N (latticePt N z j) ^ (1 / 4 : ℝ))
    (hD : ∀ j ≤ latticeTop N z, xiInd σ Xm (latticePt N z j) *
      ‖calDErr σ Xm (latticePt N z j)‖ ≤ (N : ℝ) ^ a * PsiTheta σ Xm (latticePt N z j) ^ 2)
    (hZN : ∀ j ≤ latticeTop N z, ‖ZN σ Xm (latticePt N z j)‖ ≤
      (N : ℝ) ^ a * imp_Ups N σ a (latticePt N z j) ^ 2)
    (hZM : ∀ j ≤ latticeTop N z, ‖ZMavg σ Xm (latticePt N z j)‖ ≤
      (N : ℝ) ^ a * imp_Ups N σ a (latticePt N z j) ^ 2)
    (hT : ∀ j ≤ latticeTop N z, Theta σ Xm (latticePt N z j) ≤
      (N : ℝ) ^ a * PhiN N (latticePt N z j)) :
    ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ max (max C₀ C₁) 0 * (N : ℝ) ^ (3 * a) *
      ((kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2) := by
  have hNpos : 0 < N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmem : ∀ j ≤ latticeTop N z, latticePt N z j ∈ S :=
    fun j hj => latticePt_mem hS hz hτN hj
  have hmemD : ∀ j ≤ latticeTop N z, latticePt N z j ∈ specDomain τ N :=
    fun j hj => hS.1 (hmem j hj)
  have hz0 : latticePt N z 0 = z := by simp [latticePt]
  have hzD : z ∈ specDomain τ N := hS.1 hz
  have hP : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have : IsProbabilityMeasure (empMeasure (specOf (Xmᵀ * diagonal σ * Xm))) :=
    isProbabilityMeasure_empMeasure _ hNpos
  -- the self-consistent bound along the lattice
  have hclose : ∀ j ≤ latticeTop N z, True →
      ‖fC N σ (resolventTransform (empMeasure (specOf (Xmᵀ * diagonal σ * Xm)))
          (latticePt N z j)) - latticePt N z j‖ ≤
        iterDelta N σ (3 * a) (fun Φ => Φ) (latticePt N z j) := by
    intro j hj _
    have hw := hmemD j hj
    rw [← mN_eq_resolventTransform hP Xm hw.1]
    exact imp_close hNpos da Xm hw ha hK (imp_xi hNpos Xm hw hsmall (hL j hj)) (hD j hj)
      (hZN j hj) (hZM j hj) (imp_Ups_facts hN da hw haτ hv).1 (hT j hj)
  -- the strong stability along the lattice
  have hdesc := stable_descent (B := strongBound C₀ C₁ K₀ N σ) hstab hδ
    (empMeasure (specOf (Xmᵀ * diagonal σ * Xm))) z (latticeTop N z) hmem
    (one_le_im_latticeTop hNpos z) (fun _ => True) (fun _ => True) trivial
    (fun _ _ _ => trivial) hclose (fun _ _ _ _ => trivial)
  have hstz := (hdesc 0 (Nat.zero_le _)).2
  rw [hz0, ← mN_eq_resolventTransform hP Xm hzD.1] at hstz
  -- the bound at `z`
  obtain ⟨hΦ0, -⟩ := imp_Phi hNpos hzD
  obtain ⟨him, -, -⟩ := imp_imm hNpos da hzD
  have hκ := kappa_nonneg N σ z.re
  have hη := hzD.1
  have hκη : 0 < kappa N σ z.re + z.im := by linarith
  have hsq : 0 < √(kappa N σ z.re + z.im) := Real.sqrt_pos.2 hκη
  have hδ0 : 0 ≤ iterDelta N σ (3 * a) (fun Φ => Φ) z := by
    unfold iterDelta
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (add_nonneg him.le hΦ0.le)) hΦ0.le
  have h1 := twoRegime_le_max (C₀ := C₀) (C₁ := C₁) (K₀ := K₀) (κ := kappa N σ z.re)
    (η := z.im) hδ0 hsq.le
  have hq : iterDelta N σ (3 * a) (fun Φ => Φ) z /
      (√(kappa N σ z.re + z.im) + √(iterDelta N σ (3 * a) (fun Φ => Φ) z)) ≤
      iterDelta N σ (3 * a) (fun Φ => Φ) z * (√(kappa N σ z.re + z.im))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hδ0 hsq (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hq0 : 0 ≤ iterDelta N σ (3 * a) (fun Φ => Φ) z /
      (√(kappa N σ z.re + z.im) + √(iterDelta N σ (3 * a) (fun Φ => Φ) z)) :=
    div_nonneg hδ0 (add_nonneg hsq.le (Real.sqrt_nonneg _))
  have hδΨ : iterDelta N σ (3 * a) (fun Φ => Φ) z ≤ (N : ℝ) ^ (3 * a) * Psi N σ z ^ 2 := by
    have e : iterDelta N σ (3 * a) (fun Φ => Φ) z =
        (N : ℝ) ^ (3 * a) * (((mFun N σ z).im + PhiN N z) * PhiN N z) := by
      unfold iterDelta
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (imp_X_le_Psi_sq (fun i => (hσ i).le) hη)
      (Real.rpow_nonneg hN0.le _)
  have hrp : (kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) = (√(kappa N σ z.re + z.im))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hκη.le]
  have hBp0 : 0 ≤ max (max C₀ C₁) 0 := le_max_right _ _
  calc ‖mN (diagonal σ) Xm z - mFun N σ z‖
      ≤ strongBound C₀ C₁ K₀ N σ (iterDelta N σ (3 * a) fun Φ => Φ) z := hstz
    _ ≤ max C₀ C₁ * (iterDelta N σ (3 * a) (fun Φ => Φ) z /
          (√(kappa N σ z.re + z.im) + √(iterDelta N σ (3 * a) (fun Φ => Φ) z))) := h1
    _ ≤ max (max C₀ C₁) 0 * (iterDelta N σ (3 * a) (fun Φ => Φ) z *
          (√(kappa N σ z.re + z.im))⁻¹) := mul_le_mul (le_max_left _ _) hq hq0 hBp0
    _ ≤ max (max C₀ C₁) 0 * ((N : ℝ) ^ (3 * a) * Psi N σ z ^ 2 *
          (√(kappa N σ z.re + z.im))⁻¹) := by gcongr
    _ = max (max C₀ C₁) 0 * (N : ℝ) ^ (3 * a) *
          ((kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2) := by rw [hrp]; ring

/-! ## (improved_avg_G) -/

/-- (improved_avg_G) for `Σ = diag(σ)` (Section 10.1, proof of Lemma 10.1): on a spectral domain
`S` on which (1+xm), the stability of Definition 5.4 and the strong stability of Definition A.2
hold, `|m_N − m| ≺ (κ + η)^{−1/2} Ψ²` at every `z ∈ S`. -/
theorem improved_avg_diag (τ c C₀ C₁ K₀ C₀' C₁' K₀' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      DiagModel τ C M N σ X → SpectralDomain τ N S → OneXmOn c N σ S →
      StableOn C₀ C₁ K₀ N σ S → StronglyStableOn C₀' C₁' K₀' N σ S →
      ∀ z ∈ S, ODomAt N ε D (fun ω => mN (diagonal σ) (X ω) z - mFun N σ z)
        (fun _ => (kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2) := by
  set a := min ε τ / 6 with ha_def
  have hmin := lt_min hε hτ
  have ha : 0 < a := by positivity
  have haτ : a ≤ τ / 4 := by have := min_le_right ε τ; linarith
  have h3a : 3 * a ≤ τ / 2 := by have := min_le_right ε τ; linarith
  have h3aε : 3 * a ≤ ε / 2 := by have := min_le_left ε τ; linarith
  have hc₀ : (0 : ℝ) < τ / 4 := by positivity
  obtain ⟨ε₁, hε₁, D₁, N₁, h₁⟩ := fluct_avg τ c (τ / 4) C a (D + 1 + 9) hτ hc hc₀ ha
  obtain ⟨N₂, h₂⟩ := weak_law τ c C₀ C₁ K₀ C (τ / 8) (D + 1 + 9) hτ hc (by positivity)
  obtain ⟨N₃, h₃⟩ := weak_law τ c C₀ C₁ K₀ C ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := weak_law τ c C₀ C₁ K₀ C (τ / 8) (D₁ + 1) hτ hc (by positivity)
  obtain ⟨N₅, h₅⟩ := lambdaO_Z_bound τ c C (ε₁ / 2) (D₁ + 1) hτ hc (by positivity)
  obtain ⟨N₆, h₆⟩ := calD_bound τ c C a (D + 1 + 9) hτ hc ha
  obtain ⟨N₇, h₇⟩ := theta_averaged τ c C₀ C₁ K₀ C a (D₁ + 1) hτ hc ha
  obtain ⟨N₈, h₈⟩ := theta_averaged τ c C₀ C₁ K₀ C a (D + 1 + 9) hτ hc ha
  obtain ⟨N₉, h₉⟩ := admissible_strongDelta hτ (s := 3 * a) (by positivity) h3a
  obtain ⟨N₁₀, h₁₀⟩ := imp_ev_log (p := τ / 8) (by positivity)
  obtain ⟨N₁₁, h₁₁⟩ := imp_ev_tau hτ
  obtain ⟨N₁₂, h₁₂⟩ := imp_ev_rpow hc₀ (mBoundConst τ + 4)
  obtain ⟨N₁₃, h₁₃⟩ := imp_ev_rpow ha (1 + (1 + τ⁻¹) * (1 + mBoundConst τ))
  obtain ⟨N₁₄, h₁₄⟩ := imp_ev_rpow (p := ε / 2) (by positivity) (max (max C₀' C₁') 0)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉ + N₁₀ + N₁₁ + N₁₂ + N₁₃ + N₁₄ + 5,
    fun N hN Ω _ _ M σ X S hD hS hx hstab hstab' z hz => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have da := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hsmall := h₁₀ N (by omega)
  have hzD := hS.1 hz
  have hτN := imp_top hN1 hzD (h₁₁ N (by omega))
  have hv := h₁₂ N (by omega)
  have hmem : ∀ j ≤ latticeTop N z, latticePt N z j ∈ S :=
    fun j hj => latticePt_mem hS hz hτN hj
  have hmemD : ∀ j ≤ latticeTop N z, latticePt N z j ∈ specDomain τ N :=
    fun j hj => hS.1 (hmem j hj)
  -- the inputs of Lemma 5.6 at every point of `S`
  have hΛ : ∀ w ∈ S, DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) w)
      (fun _ => (N : ℝ) ^ (-(τ / 4))) := fun w hw =>
    DomAt.mono hN1 (fun _ => le_rfl) (fun _ => imp_Phi_quarter hNpos (hS.1 hw))
      (fun _ => (Real.rpow_pos_of_pos hN0 _).le) le_rfl le_rfl
      (h₃ N (by omega) M σ X S hD hS hx hstab w hw)
  have hLo : ∀ w ∈ S, DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) w)
      (fun _ => imp_Ups N σ a w) := by
    intro w hw
    have hwD := hS.1 hw
    have E1 := h₄ N (by omega) M σ X S hD hS hx hstab w hw
    have E2 := h₅ N (by omega) M σ X hD w hwD (hx w hw) (Sum.inr ⟨0, hNpos⟩)
    have E3 := h₇ N (by omega) M σ X S hD hS hx hstab w hw
    unfold DomAt at E1 E2 E3 ⊢
    refine imp_union3 (by omega) E1 E2 E3 (fun ω hω => ?_)
    by_contra hcon
    simp only [not_or, Set.mem_ofPred_eq, not_lt] at hcon hω
    obtain ⟨n1, n2, n3⟩ := hcon
    have hxi := imp_xi hNpos (X ω) hwD hsmall n1
    rw [hxi, one_mul] at n2
    have hps := imp_psi_le_ups hN1 (fun i => (hσ i).le) (X ω) hwD.1 ha.le n3
    have hlo : LambdaO σ (X ω) w ≤ (N : ℝ) ^ (ε₁ / 2) * PsiTheta σ (X ω) w := by
      linarith [norm_nonneg (ZS σ (X ω) w (Sum.inr ⟨0, hNpos⟩))]
    have hU0 : 0 ≤ imp_Ups N σ a w := Real.sqrt_nonneg _
    have h1 : (N : ℝ) ^ (ε₁ / 2) ≤ (N : ℝ) ^ ε₁ :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h3 : (N : ℝ) ^ (ε₁ / 2) * PsiTheta σ (X ω) w ≤ (N : ℝ) ^ ε₁ * imp_Ups N σ a w :=
      (mul_le_mul_of_nonneg_left hps (Real.rpow_nonneg hN0.le _)).trans
        (mul_le_mul_of_nonneg_right h1 hU0)
    linarith
  -- the five families of events along the lattice
  have hKN : ((latticeTop N z : ℕ) : ℝ) + 1 ≤ (N : ℝ) ^ 5 + 2 := latticeTop_add_one_le hNpos hzD.1
  have hc1 : ((Finset.range (latticeTop N z + 1)).card : ℝ) ≤ (N : ℝ) ^ (9 : ℝ) := by
    rw [Finset.card_range]
    push_cast
    linarith [imp_card (N := N) (by omega)]
  have hk_of : ∀ j ∈ Finset.range (latticeTop N z + 1), j ≤ latticeTop N z :=
    fun j hj => Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hfa : ∀ j ≤ latticeTop N z,
      DomAt N a (D + 1 + 9) (fun ω => ‖ZN σ (X ω) (latticePt N z j)‖)
        (fun _ => imp_Ups N σ a (latticePt N z j) ^ 2) ∧
      DomAt N a (D + 1 + 9) (fun ω => ‖ZMavg σ (X ω) (latticePt N z j)‖)
        (fun _ => imp_Ups N σ a (latticePt N z j) ^ 2) := fun j hj =>
    h₁ N (by omega) M σ X hD _ (hmemD j hj) (hx _ (hmem j hj)) (imp_Ups N σ a (latticePt N z j))
      (imp_Ups_facts hN1 da (hmemD j hj) haτ hv).2.1
      (imp_Ups_facts hN1 da (hmemD j hj) haτ hv).2.2 (hΛ _ (hmem j hj)) (hLo _ (hmem j hj))
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
    (ζ := fun j _ => imp_Ups N σ a (latticePt N z j) ^ 2)
    (fun j hj => (hfa j (hk_of j hj)).1)
  have P4 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => ‖ZMavg σ (X ω) (latticePt N z j)‖)
    (ζ := fun j _ => imp_Ups N σ a (latticePt N z j) ^ 2)
    (fun j hj => (hfa j (hk_of j hj)).2)
  have P5 := DomAt.measure_exists_lt (D := D + 1) (C := 9) (Finset.range (latticeTop N z + 1))
    hN1 hc1 (ξ := fun j ω => Theta σ (X ω) (latticePt N z j))
    (ζ := fun j _ => PhiN N (latticePt N z j))
    (fun j hj => h₈ N (by omega) M σ X S hD hS hx hstab _ (hmem j (hk_of j hj)))
  -- the constants
  have hBp := h₁₄ N (by omega)
  have hBp0 : 0 ≤ max (max C₀' C₁') 0 := le_max_right _ _
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have hNs : (N : ℝ) ^ (3 * a) ≤ (N : ℝ) ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1' h3aε
  have hconst : max (max C₀' C₁') 0 * (N : ℝ) ^ (3 * a) ≤ (N : ℝ) ^ ε := by
    rw [hsplit]
    exact mul_le_mul hBp hNs (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)
  have hζ0 : 0 ≤ (kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (add_nonneg (kappa_nonneg N σ z.re) hzD.1.le) _) (sq_nonneg _)
  unfold ODomAt DomAt
  refine imp_union5 (by omega) P1 P2 P3 P4 P5 (fun ω hω => ?_)
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨n1, n2, n3, n4, n5⟩ := hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at n1 n2 n3 n4 n5 hω
  have hdet := imp_det hN1 da hσ (X ω) hS hstab' ha.le haτ
    (h₉ N (by omega) M σ S da hS.1) hz hτN hsmall hv (h₁₃ N (by omega))
    (fun j hj => n1 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n2 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n3 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n4 j (Finset.mem_range.2 (by omega)))
    (fun j hj => n5 j (Finset.mem_range.2 (by omega)))
  have := mul_le_mul_of_nonneg_right hconst hζ0
  linarith

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `S = {2i}` -/

section Checks

/-- (improved_avg_G) for `Σ = diag(σ)` as a conditional instance at `τ = 1/2`, `c = 1`,
`C₀ = C₁ = 4`, `K₀ = 1`, `C₀' = C₁' = 11`, `K₀' = 1`, `C_p = 2`, `ε = D = 1`: the hypotheses of
the model are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X → SpectralDomain (1 / 2) N S → OneXmOn 1 N σ S →
    StableOn 4 4 1 N σ S → StronglyStableOn 11 11 1 N σ S →
    ∀ z ∈ S, ODomAt N 1 1 (fun ω => mN (diagonal σ) (X ω) z - mFun N σ z)
      (fun _ => (kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2) :=
  improved_avg_diag (1 / 2) 1 4 4 1 11 11 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

end Checks

end Anisotropic

end

#print axioms Anisotropic.improved_avg_diag
