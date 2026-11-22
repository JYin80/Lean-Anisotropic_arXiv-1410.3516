module

public import Anisotropic.Entrywise.Control
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.LinAlg.OpBound
public import Anisotropic.Density.Varrho

@[expose] public section

/-! # The continuity argument of Proposition 5.1

The lattice `z_k = z + i k N⁻⁵` in a spectral domain, the downward descent along it that
combines the stability of Definition 5.4 with a self-consistent bound at each lattice point
(Section 5.1), the control function `δ = N^a (Nη)^{-1/2}` and its admissibility, the
Lipschitz bound for `Λ` along vertical segments, and the bound `B ≤ max(C₀, C₁) δ/(D + √δ)`
for the two-regime bound of (u-m_stability). -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The lattice, the descent, `weakDelta`, the Lipschitz bound for `Λ` -/

/-- The lattice `z_k = z + i k N⁻⁵`. -/
def latticePt (N : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  z + (((k : ℝ) * ((N : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) * Complex.I

/-- The top index `K = ⌈(1 − η) N⁵⌉`; `Im z_K ≥ 1`. -/
def latticeTop (N : ℕ) (z : ℂ) : ℕ := ⌈(1 - z.im) * (N : ℝ) ^ 5⌉₊

/-- `Re z_k = Re z`. -/
private theorem latticePt_re (N : ℕ) (z : ℂ) (k : ℕ) : (latticePt N z k).re = z.re := by
  rw [latticePt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `Im z_k = Im z + k N⁻⁵`. -/
private theorem latticePt_im (N : ℕ) (z : ℂ) (k : ℕ) :
    (latticePt N z k).im = z.im + (k : ℝ) * ((N : ℝ) ^ 5)⁻¹ := by
  rw [latticePt, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem shiftUp_latticePt (N : ℕ) (z : ℂ) (k : ℕ) :
    shiftUp N (latticePt N z k) = latticePt N z (k + 1) := by
  unfold shiftUp latticePt
  push_cast
  ring

theorem one_le_im_latticeTop {N : ℕ} (hN : 0 < N) (z : ℂ) :
    1 ≤ (latticePt N z (latticeTop N z)).im := by
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have h : (1 - z.im) * (N : ℝ) ^ 5 ≤ (latticeTop N z : ℝ) := Nat.le_ceil _
  have h' : 1 - z.im ≤ (latticeTop N z : ℝ) * ((N : ℝ) ^ 5)⁻¹ := by
    rw [le_mul_inv_iff₀ hN5]
    exact h
  rw [latticePt_im]
  linarith

theorem latticeTop_add_one_le {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : 0 < z.im) :
    ((latticeTop N z : ℕ) : ℝ) + 1 ≤ (N : ℝ) ^ 5 + 2 := by
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hzN : 0 < z.im * (N : ℝ) ^ 5 := mul_pos hz hN5
  have e : (1 - z.im) * (N : ℝ) ^ 5 = (N : ℝ) ^ 5 - z.im * (N : ℝ) ^ 5 := by ring
  rcases le_or_gt ((1 - z.im) * (N : ℝ) ^ 5) 0 with h | h
  · have h0 : latticeTop N z = 0 := Nat.ceil_eq_zero.2 h
    rw [h0]
    push_cast
    linarith
  · have hc : (latticeTop N z : ℝ) < (1 - z.im) * (N : ℝ) ^ 5 + 1 := Nat.ceil_lt_add_one h.le
    linarith

theorem latticePt_mem {τ : ℝ} {N : ℕ} {S : Set ℂ} (hS : SpectralDomain τ N S) {z : ℂ}
    (hz : z ∈ S) (hτN : z.im < 1 → 1 + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹) {k : ℕ}
    (hk : k ≤ latticeTop N z) : latticePt N z k ∈ S := by
  obtain ⟨h0, hn, hre, hη, him⟩ := hS.1 hz
  have hre' := latticePt_re N z k
  have him' := latticePt_im N z k
  have hk0 : 0 ≤ (k : ℝ) * ((N : ℝ) ^ 5)⁻¹ := by positivity
  have hle : z.im ≤ (latticePt N z k).im := by rw [him']; linarith
  have hnorm : ‖z‖ ≤ ‖latticePt N z k‖ := by
    by_contra hc
    rw [not_le] at hc
    have hsq := pow_lt_pow_left₀ hc (norm_nonneg _) two_ne_zero
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      hre'] at hsq
    nlinarith
  have htop : (latticePt N z k).im ≤ τ⁻¹ := by
    rcases le_or_gt 1 z.im with h1 | h1
    · have hK : latticeTop N z = 0 :=
        Nat.ceil_eq_zero.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
      have hk' : k = 0 := by omega
      subst hk'
      rw [him']
      simpa using him
    · rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        rw [him']
        simpa using him
      · have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
        have hc : (latticeTop N z : ℝ) < (1 - z.im) * (N : ℝ) ^ 5 + 1 :=
          Nat.ceil_lt_add_one (mul_nonneg (by linarith) hN5.le)
        have hkK : (k : ℝ) ≤ latticeTop N z := by exact_mod_cast hk
        have e : ((1 - z.im) * (N : ℝ) ^ 5 + 1) * ((N : ℝ) ^ 5)⁻¹
            = (1 - z.im) + ((N : ℝ) ^ 5)⁻¹ := by
          field_simp
        have hb : (k : ℝ) * ((N : ℝ) ^ 5)⁻¹ ≤ (1 - z.im) + ((N : ℝ) ^ 5)⁻¹ := by
          calc (k : ℝ) * ((N : ℝ) ^ 5)⁻¹ ≤ (latticeTop N z : ℝ) * ((N : ℝ) ^ 5)⁻¹ :=
                mul_le_mul_of_nonneg_right hkK (by positivity)
            _ ≤ ((1 - z.im) * (N : ℝ) ^ 5 + 1) * ((N : ℝ) ^ 5)⁻¹ :=
                mul_le_mul_of_nonneg_right hc.le (by positivity)
            _ = (1 - z.im) + ((N : ℝ) ^ 5)⁻¹ := e
        have := hτN h1
        rw [him']
        linarith
  exact hS.2 z hz _ ⟨by linarith, hn.trans hnorm, by rw [hre']; exact hre, hη.trans hle, htop⟩
    hre' hle

/-- The bound `B ≤ max(C₀, C₁) δ/(D + √δ)`, in both regimes. -/
theorem twoRegime_le_max {C₀ C₁ K₀ κ η d D : ℝ} (hd : 0 ≤ d) (hD : 0 ≤ D) :
    twoRegime C₀ C₁ K₀ κ η d D ≤ max C₀ C₁ * (d / (D + √d)) := by
  have hq : 0 ≤ d / (D + √d) := div_nonneg hd (add_nonneg hD (Real.sqrt_nonneg d))
  unfold twoRegime
  split_ifs
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hq

/-- The descent along the lattice: stability at each `z_k`, its hypothesis at `z_{k+1}`
(`shiftUp`), interleaved with an event `xi k` that gives the self-consistent bound at `z_k`. -/
theorem stable_descent {B : (ℂ → ℝ) → ℂ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {S : Set ℂ}
    (hB : StableWith B N σ S) {δ : ℂ → ℝ} (hδ : AdmissibleDelta N S δ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (z : ℂ) (K : ℕ) (hmem : ∀ k ≤ K, latticePt N z k ∈ S)
    (htop : 1 ≤ (latticePt N z K).im) (xi good : ℕ → Prop) (hxiTop : xi K)
    (hxi : ∀ k < K, good (k + 1) → xi k)
    (hclose : ∀ k ≤ K, xi k →
      ‖fC N σ (resolventTransform μ (latticePt N z k)) - latticePt N z k‖ ≤ δ (latticePt N z k))
    (hgood : ∀ k ≤ K, xi k →
      ‖resolventTransform μ (latticePt N z k) - mFun N σ (latticePt N z k)‖ ≤
        B δ (latticePt N z k) → good k) :
    ∀ k ≤ K, good k ∧
      ‖resolventTransform μ (latticePt N z k) - mFun N σ (latticePt N z k)‖ ≤
        B δ (latticePt N z k) := by
  have step : ∀ k ≤ K, xi k →
      ((latticePt N z k).im < 1 →
        ‖resolventTransform μ (shiftUp N (latticePt N z k)) -
            mFun N σ (shiftUp N (latticePt N z k))‖ ≤ B δ (shiftUp N (latticePt N z k))) →
      good k ∧ ‖resolventTransform μ (latticePt N z k) - mFun N σ (latticePt N z k)‖ ≤
        B δ (latticePt N z k) := by
    intro k hk hx hup
    have hb := hB δ hδ μ inferInstance (latticePt N z k) (hmem k hk) (hclose k hk hx) hup
    exact ⟨hgood k hk hx hb, hb⟩
  intro k hk
  refine Nat.decreasingInduction (n := K)
    (motive := fun k _ => good k ∧ ‖resolventTransform μ (latticePt N z k) -
      mFun N σ (latticePt N z k)‖ ≤ B δ (latticePt N z k))
    (fun k hk ih => ?_) ?_ hk
  · exact step k hk.le (hxi k hk ih.1) (fun _ => by rw [shiftUp_latticePt]; exact ih.2)
  · exact step K le_rfl hxiTop (fun h => absurd htop (not_le.2 h))

/-- The control function `δ = N^a (Nη)^{-1/2}` of the continuity argument. -/
def weakDelta (N : ℕ) (a : ℝ) (z : ℂ) : ℝ := (N : ℝ) ^ a * PhiN N z ^ (1 / 2 : ℝ)

/-- `δ = N^a / √(Nη)`. -/
private theorem weakDelta_eq (N : ℕ) (a : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    weakDelta N a z = (N : ℝ) ^ a * (√((N : ℝ) * z.im))⁻¹ := by
  rw [weakDelta, PhiN, Real.inv_rpow (by positivity), ← Real.sqrt_eq_rpow]

theorem admissible_weakDelta {τ a : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a) (haτ : a ≤ τ / 8) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Set ℂ, S ⊆ specDomain τ N → AdmissibleDelta N S (weakDelta N a) :=
  by
  set ε : ℝ := 3 * τ / 16 with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨max 2 (max ⌈τ⁻¹⌉₊ ⌈(ε⁻¹) ^ (ε⁻¹)⌉₊), fun N hN S hS => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := le_trans (le_max_left _ _) hN
    exact_mod_cast this
  have hτN : τ⁻¹ ≤ N := by
    have : ⌈τ⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hTN : (ε⁻¹) ^ (ε⁻¹) ≤ (N : ℝ) := by
    have : ⌈(ε⁻¹) ^ (ε⁻¹)⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  -- `x = Nη ≥ N^τ ≥ 1` on `𝐃(τ,N)`
  have hx : ∀ z ∈ S, (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
    intro z hz
    obtain ⟨-, -, -, hη, -⟩ := hS hz
    have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
    rw [← e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hNa1 : (1 : ℝ) ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha
  have hNaτ : (N : ℝ) ^ a ≤ (N : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have him : ∀ z ∈ S, 0 < z.im := fun z hz => (hS hz).1
  have hsq : ∀ z ∈ S, 1 ≤ √((N : ℝ) * z.im) := fun z hz =>
    Real.one_le_sqrt.2 (hNτ.trans (hx z hz))
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz w hw => ?_, fun z hz w hw _ hzw => ?_⟩
  · -- lower: `N⁻² ≤ δ`
    rw [weakDelta_eq N a (him z hz).le]
    obtain ⟨-, -, -, -, hητ⟩ := hS hz
    have hs0 : 0 < √((N : ℝ) * z.im) := lt_of_lt_of_le one_pos (hsq z hz)
    have hsN : √((N : ℝ) * z.im) ≤ (N : ℝ) ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have h1 : z.im ≤ N := hητ.trans hτN
      have h2 : (N : ℝ) * z.im ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left h1 hN0.le
      have h3 : (1 : ℝ) ≤ N * N := by nlinarith
      have h4 : (N : ℝ) * N ≤ ((N : ℝ) ^ 2) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ N * N)
        nlinarith
      linarith
    calc ((N : ℝ) ^ 2)⁻¹ ≤ (√((N : ℝ) * z.im))⁻¹ := inv_anti₀ hs0 hsN
      _ ≤ (N : ℝ) ^ a * (√((N : ℝ) * z.im))⁻¹ :=
          le_mul_of_one_le_left (inv_nonneg.2 hs0.le) hNa1
  · -- upper: `δ ≤ (log N)⁻¹`
    rw [weakDelta_eq N a (him z hz).le]
    have hs0 : 0 < √((N : ℝ) * z.im) := lt_of_lt_of_le one_pos (hsq z hz)
    have hlog0 : 0 < Real.log N := Real.log_pos (by linarith)
    have hlog : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0.le hε0
    have hεN : ε⁻¹ ≤ (N : ℝ) ^ ε := by
      have h1 : ((ε⁻¹) ^ (ε⁻¹)) ^ ε ≤ (N : ℝ) ^ ε :=
        Real.rpow_le_rpow (by positivity) hTN hε0.le
      rwa [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hε0.ne', Real.rpow_one] at h1
    have hlog' : Real.log N ≤ (N : ℝ) ^ ε * (N : ℝ) ^ ε := by
      rw [div_eq_mul_inv] at hlog
      exact hlog.trans (mul_le_mul_of_nonneg_left hεN (by positivity))
    have hexp : (N : ℝ) ^ a * ((N : ℝ) ^ ε * (N : ℝ) ^ ε) ≤ (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hε]; linarith)
    have hhalf : (N : ℝ) ^ (τ / 2) ≤ √((N : ℝ) * z.im) := by
      have e : (N : ℝ) ^ (τ / 2) = √((N : ℝ) ^ τ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
        ring_nf
      rw [e]
      exact Real.sqrt_le_sqrt (hx z hz)
    have hkey : (N : ℝ) ^ a * Real.log N ≤ √((N : ℝ) * z.im) :=
      (mul_le_mul_of_nonneg_left hlog' (by positivity)).trans (hexp.trans hhalf)
    rw [mul_inv_le_iff₀ hs0, le_inv_mul_iff₀ hlog0, mul_comm]
    exact hkey
  · -- Lipschitz: `|δ(z) − δ(w)| ≤ N² ‖z − w‖`
    rw [weakDelta_eq N a (him z hz).le, weakDelta_eq N a (him w hw).le]
    set s := √((N : ℝ) * z.im) with hs
    set t := √((N : ℝ) * w.im) with ht
    have hs1 : 1 ≤ s := hsq z hz
    have ht1 : 1 ≤ t := hsq w hw
    have hs2 : s ^ 2 = (N : ℝ) * z.im := Real.sq_sqrt (by have := him z hz; positivity)
    have ht2 : t ^ 2 = (N : ℝ) * w.im := Real.sq_sqrt (by have := him w hw; positivity)
    -- `N^a ≤ min(s², t²) ≤ s t`
    have hP : (N : ℝ) ^ a ≤ s * t := by
      have h1 : (N : ℝ) ^ a ≤ s ^ 2 := hNaτ.trans (hs2 ▸ hx z hz)
      have h2 : (N : ℝ) ^ a ≤ t ^ 2 := hNaτ.trans (ht2 ▸ hx w hw)
      rcases le_total s t with h | h
      · nlinarith
      · nlinarith
    have e : (N : ℝ) ^ a * s⁻¹ - (N : ℝ) ^ a * t⁻¹ = (N : ℝ) ^ a * (t - s) / (s * t) := by
      field_simp
    have hst : 0 < s * t := by positivity
    have h1 : |(N : ℝ) ^ a * s⁻¹ - (N : ℝ) ^ a * t⁻¹| ≤ |t - s| := by
      rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ a),
        abs_of_pos hst, div_le_iff₀ hst]
      calc (N : ℝ) ^ a * |t - s| ≤ s * t * |t - s| :=
            mul_le_mul_of_nonneg_right hP (abs_nonneg _)
        _ = |t - s| * (s * t) := by ring
    have h2 : |t - s| ≤ |t ^ 2 - s ^ 2| := by
      have : t ^ 2 - s ^ 2 = (t - s) * (t + s) := by ring
      rw [this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t + s)]
      exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    have h3 : |t ^ 2 - s ^ 2| ≤ (N : ℝ) * ‖z - w‖ := by
      rw [hs2, ht2, ← mul_sub, abs_mul, abs_of_pos hN0]
      refine mul_le_mul_of_nonneg_left ?_ hN0.le
      have := Complex.abs_im_le_norm (z - w)
      rw [Complex.sub_im, abs_sub_comm] at this
      exact this
    have h4 : (N : ℝ) * ‖z - w‖ ≤ (N : ℝ) ^ 2 * ‖z - w‖ :=
      mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    linarith
  · -- antitone in `η`
    rw [weakDelta_eq N a (him z hz).le, weakDelta_eq N a (him w hw).le]
    have hs0 : 0 < √((N : ℝ) * z.im) := lt_of_lt_of_le one_pos (hsq z hz)
    refine mul_le_mul_of_nonneg_left (inv_anti₀ hs0 (Real.sqrt_le_sqrt ?_)) (by positivity)
    exact mul_le_mul_of_nonneg_left hzw hN0.le

/-! ### The Lipschitz bound for `Λ` -/

/-- `σ̲_s > 0` for `σ > 0`. -/
private theorem lattice_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Σ̲⁻¹ = diag(σ̲)⁻¹` for `Σ = diag(σ)`. -/
private theorem lattice_cplx_SigU_inv {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) :
    cplx (SigU (n := Fin N) (diagonal σ))⁻¹ =
      diagonal fun s : Fin M ⊕ Fin N => (((sigS σ s)⁻¹ : ℝ) : ℂ) := by
  have h1 : SigU (n := Fin N) (diagonal σ) = diagonal (sigS (N := N) σ) := by
    rw [SigU, ← diagonal_one, fromBlocks_diagonal]
    rfl
  have h2 : (SigU (n := Fin N) (diagonal σ))⁻¹ =
      diagonal fun s : Fin M ⊕ Fin N => (sigS σ s)⁻¹ := by
    apply inv_eq_left_inv
    rw [h1, diagonal_mul_diagonal]
    convert diagonal_one (n := Fin M ⊕ Fin N) (α := ℝ) using 2
    funext s
    exact inv_mul_cancel₀ (lattice_sigS_pos hσ s).ne'
  rw [h2, cplx, diagonal_map (by simp)]
  rfl

/-- `|(G P_N G)_{st}| ≤ σ̲_s σ̲_t (1 + ‖XᵀX‖)/η²` (Lemma 4.9). -/
private theorem lattice_dG_entry {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) (s t : Fin M ⊕ Fin N) :
    ‖(G (diagonal σ) Xm ζ * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
        G (diagonal σ) Xm ζ) s t‖ ≤
      (1 + ‖Xmᵀ * Xm‖) / ζ.im ^ 2 * (sigS σ s * sigS σ t) := by
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have h := opnorm_dG hSig Xm hζ (eI s) (eI t)
  have he : ∀ r : Fin M ⊕ Fin N, (eI r : Fin M ⊕ Fin N → ℝ) ⬝ᵥ eI r = 1 := by
    intro r
    simp [eI, dotProduct, Pi.single_apply]
  rw [he, he, Real.sqrt_one, mul_one, mul_one, ent_eI_eI, lattice_cplx_SigU_inv hσ,
    mul_diagonal, diagonal_mul] at h
  have hs := lattice_sigS_pos (N := N) hσ s
  have ht := lattice_sigS_pos (N := N) hσ t
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), abs_of_pos (inv_pos.2 ht)] at h
  have e : ∀ x : ℝ, (sigS σ s)⁻¹ * x * (sigS σ t)⁻¹ = x / (sigS σ s * sigS σ t) := fun x => by
    field_simp
  rw [e, div_le_iff₀ (mul_pos hs ht)] at h
  exact h

/-- `|G_{st}(z) − G_{st}(w)| ≤ σ̲_s σ̲_t (1 + ‖XᵀX‖) ‖z − w‖ / min(Im z, Im w)²`. -/
private theorem lattice_G_lip {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (s t : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z s t - G (diagonal σ) Xm w s t‖ ≤
      (1 + ‖Xmᵀ * Xm‖) / min z.im w.im ^ 2 * (sigS σ s * sigS σ t) * ‖z - w‖ := by
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  set ρ := min z.im w.im with hρ
  have hρ0 : 0 < ρ := lt_min hz hw
  have hst : 0 ≤ sigS (N := N) σ s * sigS σ t :=
    (mul_pos (lattice_sigS_pos hσ s) (lattice_sigS_pos hσ t)).le
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun ζ => G (diagonal σ) Xm ζ s t)
    (f' := fun ζ => (G (diagonal σ) Xm ζ * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
      G (diagonal σ) Xm ζ) s t)
    (s := {ζ : ℂ | ρ ≤ ζ.im}) (fun ζ hζ => ?_) (fun ζ hζ => ?_) (convex_halfSpace_im_ge ρ)
    (show ρ ≤ w.im from min_le_right _ _) (show ρ ≤ z.im from min_le_left _ _)
  · exact (hasDerivAt_G hSig Xm (lt_of_lt_of_le hρ0 hζ) s t).hasDerivWithinAt
  · have hζ0 : 0 < ζ.im := lt_of_lt_of_le hρ0 hζ
    refine (lattice_dG_entry hσ Xm hζ0 s t).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hst
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hρ0.le hζ 2)

/-- `|m(z) − m(w)| ≤ ‖z − w‖ / min(Im z, Im w)²`, from the Stieltjes representation of `m`. -/
private theorem lattice_m_lip {N : ℕ} (hN : 0 < N) {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖mFun N σ z - mFun N σ w‖ ≤ ‖z - w‖ / min z.im w.im ^ 2 := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have h := norm_resolventTransform_sub_le (varrho N σ) hz hw
  rw [resolventTransform_varrho N σ hσ hN hz, resolventTransform_varrho N σ hσ hN hw] at h
  refine h.trans (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) ?_)
  rw [sq]
  exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (lt_min hz hw).le hz.le

/-- `|m_s(z) − m_s(w)| ≤ σ̲_s² (1 + c⁻²) ‖z − w‖ / min(Im z, Im w)²` under (1+xm) at `z, w`. -/
private theorem lattice_mS_lip {N : ℕ} (hN : 0 < N) {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {c : ℝ} (hc : 0 < c) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hcw : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖) (s : Fin M ⊕ Fin N) :
    ‖mS N σ z s - mS N σ w s‖ ≤
      (1 + c⁻¹ ^ 2) * (‖z - w‖ / min z.im w.im ^ 2) * (sigS σ s * sigS σ s) := by
  have hm := lattice_m_lip hN (fun i => (hσ i).le) hz hw
  have hq : 0 ≤ ‖z - w‖ / min z.im w.im ^ 2 := by
    have := lt_min hz hw
    positivity
  cases s with
  | inr μ =>
    simp only [mS, Sum.elim_inr, sigS, mul_one]
    nlinarith [sq_nonneg c⁻¹]
  | inl i =>
    simp only [mS, Sum.elim_inl, sigS, mI]
    set a := mFun N σ z
    set b := mFun N σ w
    have hcz' := hcz i
    have hcw' := hcw i
    have ha : 1 + (σ i : ℂ) * a ≠ 0 := fun h => by
      rw [h, norm_zero] at hcz'; linarith
    have hb : 1 + (σ i : ℂ) * b ≠ 0 := fun h => by
      rw [h, norm_zero] at hcw'; linarith
    have e : -(σ i : ℂ) / (1 + σ i * a) - -(σ i : ℂ) / (1 + σ i * b) =
        (σ i : ℂ) ^ 2 * (a - b) / ((1 + σ i * a) * (1 + σ i * b)) := by
      field_simp
      ring
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hσ i)]
    have hden : c * c ≤ ‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖ :=
      mul_le_mul hcz' hcw' hc.le (norm_nonneg _)
    have hcc : 0 < c * c := mul_pos hc hc
    rw [div_le_iff₀ (lt_of_lt_of_le hcc hden)]
    have hσ2 : 0 ≤ σ i ^ 2 := sq_nonneg _
    have hci : c⁻¹ ^ 2 * (c * c) = 1 := by field_simp
    calc σ i ^ 2 * ‖a - b‖ ≤ σ i ^ 2 * (‖z - w‖ / min z.im w.im ^ 2) :=
          mul_le_mul_of_nonneg_left hm hσ2
      _ = σ i ^ 2 * (‖z - w‖ / min z.im w.im ^ 2) * (c⁻¹ ^ 2 * (c * c)) := by rw [hci, mul_one]
      _ ≤ (1 + c⁻¹ ^ 2) * (‖z - w‖ / min z.im w.im ^ 2) * (σ i * σ i) *
            (‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖) := by
          have h1 : σ i ^ 2 * (‖z - w‖ / min z.im w.im ^ 2) * (c⁻¹ ^ 2 * (c * c)) ≤
              σ i ^ 2 * (‖z - w‖ / min z.im w.im ^ 2) * (c⁻¹ ^ 2 *
                (‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden (sq_nonneg _))
              (mul_nonneg hσ2 hq)
          have hD : 0 ≤ ‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖ := by positivity
          have h2 : σ i ^ 2 * (‖z - w‖ / min z.im w.im ^ 2) * (c⁻¹ ^ 2 *
                (‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖)) ≤
              (1 + c⁻¹ ^ 2) * (‖z - w‖ / min z.im w.im ^ 2) * (σ i * σ i) *
                (‖1 + (σ i : ℂ) * a‖ * ‖1 + (σ i : ℂ) * b‖) := by
            nlinarith [mul_nonneg (mul_nonneg hσ2 hq) hD]
          exact h1.trans h2

/-- `Λ(z) ≤ Λ(w) + L` when every weighted entry of `D(z) − D(w)` is at most `L`. -/
private theorem lattice_Lambda_le {N : ℕ} (hN : 0 < N) {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z w : ℂ) (L : ℝ)
    (h : ∀ s t, ‖(G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)) -
        (G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0))‖ /
          (sigS σ s * sigS σ t) ≤ L) :
    Lambda σ Xm z ≤ Lambda σ Xm w + L := by
  have : Nonempty (Fin M ⊕ Fin N) := ⟨Sum.inr ⟨0, hN⟩⟩
  refine ciSup_le fun s => ciSup_le fun t => ?_
  have hp : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (lattice_sigS_pos hσ s) (lattice_sigS_pos hσ t)
  have hw : ‖G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0)‖ /
      (sigS σ s * sigS σ t) ≤ Lambda σ Xm w := by
    unfold Lambda
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove s)
    exact le_ciSup (f := fun t => ‖G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0)‖
      / (sigS σ s * sigS σ t)) (Set.finite_range _).bddAbove t
  have htri := norm_sub_norm_le
    (G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0))
    (G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0))
  have h1 : ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖ /
      (sigS σ s * sigS σ t) ≤
      ‖G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0)‖ / (sigS σ s * sigS σ t) +
      ‖(G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)) -
        (G (diagonal σ) Xm w s t - (if s = t then mS N σ w s else 0))‖ /
          (sigS σ s * sigS σ t) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  linarith [h s t]

/-- `Λ` is Lipschitz along vertical segments: `opnorm_dG` for `G`, (1+xm) and the Stieltjes
representation of `m` for `Π`. -/
theorem Lambda_lipschitz {N : ℕ} (hN : 0 < N) {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {c : ℝ} (hc : 0 < c) {z w : ℂ} (hre : z.re = w.re)
    (hz : 0 < z.im) (hw : 0 < w.im) (hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hcw : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖) :
    |Lambda σ Xm z - Lambda σ Xm w| ≤
      (2 + ‖Xmᵀ * Xm‖ + c⁻¹ ^ 2) * ‖z - w‖ / min z.im w.im ^ 2 := by
  -- the entrywise bound, for `(z, w)` in either order
  have key : ∀ z' w' : ℂ, 0 < z'.im → 0 < w'.im →
      (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z'‖) → (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ w'‖) →
      ∀ s t, ‖(G (diagonal σ) Xm z' s t - (if s = t then mS N σ z' s else 0)) -
        (G (diagonal σ) Xm w' s t - (if s = t then mS N σ w' s else 0))‖ /
          (sigS σ s * sigS σ t) ≤
        (2 + ‖Xmᵀ * Xm‖ + c⁻¹ ^ 2) * ‖z' - w'‖ / min z'.im w'.im ^ 2 := by
    intro z' w' hz' hw' hcz' hcw' s t
    have hp : 0 < sigS (N := N) σ s * sigS σ t :=
      mul_pos (lattice_sigS_pos hσ s) (lattice_sigS_pos hσ t)
    have hq : 0 ≤ ‖z' - w'‖ / min z'.im w'.im ^ 2 := by
      have := lt_min hz' hw'
      positivity
    have hG := lattice_G_lip hσ Xm hz' hw' s t
    have hX : 0 ≤ ‖Xmᵀ * Xm‖ := norm_nonneg _
    have hc2 : 0 ≤ c⁻¹ ^ 2 := sq_nonneg _
    have e1 : (1 + ‖Xmᵀ * Xm‖) / min z'.im w'.im ^ 2 * (sigS σ s * sigS σ t) * ‖z' - w'‖ =
        (1 + ‖Xmᵀ * Xm‖) * (‖z' - w'‖ / min z'.im w'.im ^ 2) * (sigS σ s * sigS σ t) := by
      ring
    rw [e1] at hG
    rw [div_le_iff₀ hp, mul_div_assoc]
    split_ifs with hst
    · subst hst
      have hm := lattice_mS_lip hN hσ hc hz' hw' hcz' hcw' s
      have e2 : G (diagonal σ) Xm z' s s - mS N σ z' s - (G (diagonal σ) Xm w' s s - mS N σ w' s)
          = (G (diagonal σ) Xm z' s s - G (diagonal σ) Xm w' s s) - (mS N σ z' s - mS N σ w' s) :=
        by ring
      rw [e2]
      refine (norm_sub_le _ _).trans ?_
      nlinarith
    · simp only [sub_zero]
      refine hG.trans ?_
      nlinarith [mul_nonneg (mul_nonneg hq hp.le) (add_nonneg zero_le_one hc2)]
  have h1 := lattice_Lambda_le hN hσ Xm z w _ (key z w hz hw hcz hcw)
  have h2 := lattice_Lambda_le hN hσ Xm w z _ (key w z hw hz hcw hcz)
  rw [norm_sub_rev w z, min_comm w.im z.im] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` -/

section Checks

example : latticeTop 2 (2 * Complex.I) = 0 := by
  simp [latticeTop]
  norm_num

example (z : ℂ) (k : ℕ) : shiftUp 2 (latticePt 2 z k) = latticePt 2 z (k + 1) :=
  shiftUp_latticePt 2 z k

/-- `z = 1/2 + 3i/4`, `N = 2`: `K = ⌈8⌉ = 8`, and `Im z_8 = 1`. -/
example : latticeTop 2 (⟨1 / 2, 3 / 4⟩ : ℂ) = 8 := by
  simp only [latticeTop]
  norm_num

example : 1 ≤ (latticePt 2 (⟨1 / 2, 3 / 4⟩ : ℂ) (latticeTop 2 ⟨1 / 2, 3 / 4⟩)).im :=
  one_le_im_latticeTop (by norm_num) _

example : ((latticeTop 2 (⟨1 / 2, 3 / 4⟩ : ℂ) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ 5 + 2 :=
  latticeTop_add_one_le (by norm_num) (by norm_num)

/-- The thick regime `κ = 1/10`, `η = 10⁻⁴`, `δ = 10⁻³`, `K₀ = 36`. -/
example : twoRegime 10 50 36 (1 / 10) (1 / 10000) (1 / 1000) √(1 / 10 + 1 / 10000) ≤
    max 10 50 * ((1 / 1000) / (√(1 / 10 + 1 / 10000) + √(1 / 1000))) :=
  twoRegime_le_max (by norm_num) (Real.sqrt_nonneg _)

/-- `admissible_weakDelta` at `τ = 1/2`, `a = 0`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Set ℂ, S ⊆ specDomain (1 / 2) N →
    AdmissibleDelta N S (weakDelta N 0) :=
  admissible_weakDelta (by norm_num) le_rfl (by norm_num)

end Checks

end Anisotropic

#print axioms Anisotropic.latticePt
#print axioms Anisotropic.latticeTop
#print axioms Anisotropic.shiftUp_latticePt
#print axioms Anisotropic.one_le_im_latticeTop
#print axioms Anisotropic.latticeTop_add_one_le
#print axioms Anisotropic.latticePt_mem
#print axioms Anisotropic.twoRegime_le_max
#print axioms Anisotropic.stable_descent
#print axioms Anisotropic.weakDelta
#print axioms Anisotropic.admissible_weakDelta
#print axioms Anisotropic.Lambda_lipschitz
