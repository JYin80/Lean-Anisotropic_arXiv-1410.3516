import Anisotropic.Density.Stability.EdgeTaylor

/-!
# (m_sq_root), (mz_reg) and (1+xm) on `𝐃^e_k` (Lemma A.4)

Lemma A.4 (`lem:stab_edge1`) with explicit constants depending only on `τ`, on the edge domain
`𝐃^e_k(τ, τ'')` with `τ'' ≤ τ' = τ'₀/4`. Write `z = E + iη`, `κ = κ(E)`, `b = κ + η`.

* `m_sq_root_edge`: (m_sq_root), `Im m(z) ≍ √b` for `E ∈ supp ϱ` and `Im m(z) ≍ η/√b` otherwise.
* `mz_reg_edge`: (mz_reg), `|m(z) + s⁻¹| ≥ c` for every positive value `s` of `σ`.
* `one_add_mul_mFun_edge`: (1+xm), `|1 + σ_i m(z)| ≥ c`.

Proofs. Write `a = a_k`, `x_k` for the critical point, and `ε = (-1)^{k+1}`, so that the band
side of `a` is `ε(x - a) ≤ 0`. On `𝐃^e_k`, `κ = |E - a|` (§3.3).
* `η ≥ τ'`: Lemma 4.10 gives `C_m⁻¹η ≤ Im m ≤ |m| ≤ C_m`, and `τ' ≤ b ≤ 2/τ`.
* `η < τ'`: `Im m(z) = ∫ η((x - E)² + η²)⁻¹ ϱ(dx)` (Lemma 2.2), and on `|x - a| ≤ τ'₀` the density
  is `≍ √|x - a|` on the band side and `0` on the gap side (proof of Lemma A.4).
  * Lower bounds: restrict the integral to `ε(a - x) ∈ [κ + η/2, κ + η]` (band) or
    `ε(a - x) ∈ [b, 2b]` (gap).
  * Band upper bound: `Im m ≤ |m - x_k|` and (z-a_taylor), `(c₂/4)|m - x_k|² ≤ |z - a| ≤ b`.
  * Gap upper bound: on the band side of `a`, the kernel at `z` is at most `2η/b` times the kernel
    at `a + ib`; the gap side of `a` near `a` is `ϱ`-null, and farther away the kernel is
    `≤ η/τ'²`. The band upper bound at `a + ib` then gives `Im m(z) ≤ (4/√c₂) η/√b + η/τ'²`.
  * Support: near `a`, `E ∈ supp ϱ` iff `ε(E - a) ≤ 0`, from the same density bounds.
* (mz_reg): for `η ≥ τ'`, `|m + s⁻¹| ≥ Im m ≥ τ'/C_m`; for `η < τ'`, (z-a_taylor) gives
  `|m - x_k| < ρ₁ ≤ τ/2`, and (reg: edge) gives `|x_k + s⁻¹| ≥ τ`.
* (1+xm) follows from (mz_reg) and `|m| ≤ C_m`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-- Lower constant of (m_sq_root) on `𝐃^e_k`. -/
def sqLower (τ : ℝ) : ℝ :=
  min (min ((√(edgeC2 τ))⁻¹ / (4 * √2 * Real.pi)) (edgeTau' τ * √(τ / 2) / mBoundConst τ))
    (min ((√(edgeC2 τ))⁻¹ / (10 * Real.pi)) (√(edgeTau' τ) / mBoundConst τ))

/-- Upper constant of (m_sq_root) on `𝐃^e_k`. -/
def sqUpper (τ : ℝ) : ℝ :=
  max (max (6 * √2 / √(edgec2 τ) + (√τ)⁻¹ / edgeTau' τ ^ 2) (mBoundConst τ / √(edgeTau' τ)))
    (max (4 / √(edgec2 τ) + √(2 / τ) / edgeTau' τ ^ 2) (mBoundConst τ * √(2 / τ) / edgeTau' τ))

/-- Constant of (mz_reg) on `𝐃^e_k`. -/
def edgeMz (τ : ℝ) : ℝ := min (τ / 2) (edgeTau' τ / mBoundConst τ)

/-! ## Elementary consequences of the assumptions -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `τ ≤ 1` and some positive `σ i`. -/
private lemma esr_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ τ ≤ 1 ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))
  refine ⟨hN, hτ1, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
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

/-- The constants of Lemma A.3: positivity, `ρ₁ ≤ τ/2`, `τ'₀ < τ`, and `0 < C_m`. -/
private lemma esr_consts {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgec2 τ ∧ 0 < edgeC2 τ ∧ 0 < edgeRho1 τ ∧ edgeRho1 τ ≤ τ / 2 ∧ 0 < edgeTau0 τ ∧
      edgeTau0 τ < τ ∧ 0 < mBoundConst τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC2 : 0 < edgeC2 τ := by unfold edgeC2; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hρτ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have ht0 : 0 < edgeTau0 τ := by unfold edgeTau0; positivity
  have htτ : edgeTau0 τ < τ := by
    unfold edgeTau0
    have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le hρτ 2
    have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
      mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
    have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
    nlinarith
  have hCm : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
  exact ⟨h2, hC2, h1, hρτ, ht0, htτ, hCm⟩

/-- `y² = (εy)²` for `ε² = 1`. -/
private lemma esr_sq_eq {ε : ℝ} (hε2 : ε * ε = 1) (y : ℝ) : y ^ 2 = (ε * y) ^ 2 := by
  rw [mul_pow, sq ε, hε2, one_mul]

/-- `|y| = εy` for `ε = ±1` and `εy ≥ 0`. -/
private lemma esr_abs_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {y : ℝ} (hy : 0 ≤ ε * y) : |y| = ε * y := by
  have hεa : |ε| = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← abs_of_nonneg hy, abs_mul, hεa, one_mul]

/-! ## The Stieltjes integral of `ϱ` -/

/-- The Poisson kernel `Im (x - z)⁻¹ = η / ((x - E)² + η²)`. -/
private def esrKer (z : ℂ) (x : ℝ) : ℝ := z.im / ((x - z.re) ^ 2 + z.im ^ 2)

private lemma esrKer_nonneg {z : ℂ} (hz : 0 < z.im) (x : ℝ) : 0 ≤ esrKer z x := by
  unfold esrKer; positivity

private lemma esrKer_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) : esrKer z x ≤ z.im⁻¹ := by
  unfold esrKer
  rw [div_le_iff₀ (by positivity)]
  have e : z.im⁻¹ * z.im ^ 2 = z.im := by field_simp
  nlinarith [mul_nonneg (inv_nonneg.2 hz.le) (sq_nonneg (x - z.re))]

private lemma esrKer_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    Integrable (esrKer z) μ := by
  refine Integrable.of_bound ?_ z.im⁻¹ (ae_of_all _ fun x => ?_)
  · have hc : Continuous (esrKer z) := by
      unfold esrKer
      exact continuous_const.div (((continuous_id.sub continuous_const).pow 2).add
        continuous_const) fun x => by positivity
    exact hc.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (esrKer_nonneg hz x)]
    exact esrKer_le hz x

/-- `Im m(z) = ∫ η / ((x - E)² + η²) ϱ(dx)` (Lemma 2.2). -/
private lemma esr_im_mFun {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : (mFun N σ z).im = ∫ x, esrKer z x ∂(varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) (varrho N σ) := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
    · rw [norm_inv]
      refine inv_anti₀ hz ?_
      have h := Complex.abs_im_le_norm ((x : ℂ) - z)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
      exact le_trans (le_abs_self _) h
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  have hres : ∀ x : ℝ, resolvent z x = ((x : ℂ) - z)⁻¹ := fun x => by
    simp [resolvent, Ring.inverse_eq_inv']
  simp_rw [hres]
  have him : (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(varrho N σ)).im =
      ∫ x : ℝ, (((x : ℂ) - z)⁻¹).im ∂(varrho N σ) := by
    have := integral_im (𝕜 := ℂ) hint
    simpa using this.symm
  rw [him]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [esrKer]
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.sub_re, Complex.ofReal_re]
  ring

/-- `L · vol(S) ≤ ϱ(S)` when `S ⊆ (0, ∞)` and `ρ ≥ L` on `S`. -/
private lemma esr_varrho_ge {N : ℕ} {σ : Fin M → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Set.Ioi 0) {L : ℝ} (hL : ∀ x ∈ S, L ≤ rhoDens N σ x) :
    ENNReal.ofReal L * volume S ≤ varrho N σ S := by
  rw [varrho, Measure.add_apply, withDensity_apply _ hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.2 hS0]
  refine le_add_left ?_
  rw [← setLIntegral_const]
  exact setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (hL x hx)

/-- `ϱ(G) = 0` when `G ⊆ (0, ∞)` and `ρ = 0` on `G`. -/
private lemma esr_varrho_null {N : ℕ} {σ : Fin M → ℝ} {G : Set ℝ} (hG : MeasurableSet G)
    (hG0 : G ⊆ Set.Ioi 0) (h0 : ∀ x ∈ G, rhoDens N σ x = 0) : varrho N σ G = 0 := by
  have h0G : (0 : ℝ) ∉ G := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.1 (hG0 h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hG,
    Set.indicator_of_notMem h0G, smul_zero, zero_add, withDensity_apply _ hG,
    Measure.restrict_restrict hG]
  refine setLIntegral_eq_zero (hG.inter measurableSet_Ioi) fun x hx => ?_
  simp [h0 x hx.1]

/-- `c μ(S) ≤ ∫ f dμ` for `f ≥ 0` with `f ≥ c` on `S`. -/
private lemma esr_integral_ge (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) {S : Set ℝ} (hS : MeasurableSet S) {c : ℝ}
    (hc : ∀ x ∈ S, c ≤ f x) : c * μ.real S ≤ ∫ x, f x ∂μ := by
  have h1 : ∫ x, S.indicator (fun _ => c) x ∂μ = μ.real S • c := integral_indicator_const c hS
  rw [mul_comm, ← smul_eq_mul, ← h1]
  refine integral_mono ((integrable_const c).indicator hS) hf fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact hc x hx
  · rw [Set.indicator_of_notMem hx]; exact hf0 x

/-- The set `{x | ε(c - x) ∈ [p, q]}`, `ε = ±1`, is an interval of length `q - p`. -/
private lemma esr_set {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (c p q : ℝ) :
    MeasurableSet {x : ℝ | ε * (c - x) ∈ Set.Icc p q} ∧
      volume {x : ℝ | ε * (c - x) ∈ Set.Icc p q} = ENNReal.ofReal (q - p) := by
  have key : ∃ l, {x : ℝ | ε * (c - x) ∈ Set.Icc p q} = Set.Icc l (l + (q - p)) := by
    rcases hε with rfl | rfl
    · refine ⟨c - q, ?_⟩
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    · refine ⟨c + p, ?_⟩
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  obtain ⟨l, hl⟩ := key
  rw [hl, Real.volume_Icc]
  exact ⟨measurableSet_Icc, by ring_nf⟩

/-- `L (q - p) ≤ ϱ(S)` for `S = {x | ε(c - x) ∈ [p, q]} ⊆ (0, ∞)` with `ρ ≥ L` on `S`. -/
private lemma esr_real_ge {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {c p q L : ℝ} (hpq : p ≤ q) (hL0 : 0 ≤ L)
    (hS0 : ∀ x, ε * (c - x) ∈ Set.Icc p q → 0 < x)
    (hL : ∀ x, ε * (c - x) ∈ Set.Icc p q → L ≤ rhoDens N σ x) :
    L * (q - p) ≤ (varrho N σ).real {x : ℝ | ε * (c - x) ∈ Set.Icc p q} := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  obtain ⟨hS, hvol⟩ := esr_set hε c p q
  have h := esr_varrho_ge (N := N) (σ := σ) hS (fun x hx => hS0 x hx) (fun x hx => hL x hx)
  rw [hvol] at h
  have := ENNReal.toReal_mono (measure_ne_top _ _) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0, ENNReal.toReal_ofReal (by linarith)]
    at this

/-! ## The density on the band side and the support near `a_k` -/

/-- On the band side of `a_k` within `τ'₀`: `x > 0` and `√(|x - a_k|/C₂) ≤ π ρ(x)`. -/
private lemma esr_band_point {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {x : ℝ}
    (hx0 : 0 ≤ (-1 : ℝ) ^ (k + 1) * (edgeVal N σ k - x))
    (hxt : (-1 : ℝ) ^ (k + 1) * (edgeVal N σ k - x) ≤ edgeTau0 τ) :
    0 < x ∧ √((-1 : ℝ) ^ (k + 1) * (edgeVal N σ k - x) / edgeC2 τ) ≤
      Real.pi * rhoDens N σ x := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨-, -, -, -, -, htτ, -⟩ := esr_consts h.pos hτ1
  have hε : (-1 : ℝ) ^ (k + 1) = 1 ∨ (-1 : ℝ) ^ (k + 1) = -1 := neg_one_pow_eq_or ℝ (k + 1)
  have habs : |x - edgeVal N σ k| = (-1 : ℝ) ^ (k + 1) * (edgeVal N σ k - x) := by
    rw [← esr_abs_eq hε hx0, abs_sub_comm]
  have hxa : |x - edgeVal N σ k| ≤ edgeTau0 τ := by rw [habs]; exact hxt
  have ha := hk.2.2.1
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp hxa).1
    linarith
  · have hb : (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k) ≤ 0 := by
      have e : (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k) =
          -((-1 : ℝ) ^ (k + 1) * (edgeVal N σ k - x)) := by ring
      rw [e]; linarith
    have := ((rhoDens_edge h hk hxa).1 hb).1
    rwa [habs] at this

/-- The gap side of `a_k` within `τ'₀` is `ϱ`-null. -/
private lemma esr_gap_null {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) :
    MeasurableSet {x : ℝ | |x - edgeVal N σ k| ≤ edgeTau0 τ ∧
        0 < (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)} ∧
      varrho N σ {x : ℝ | |x - edgeVal N σ k| ≤ edgeTau0 τ ∧
        0 < (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)} = 0 := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨-, -, -, -, -, htτ, -⟩ := esr_consts h.pos hτ1
  have ha := hk.2.2.1
  have hG : MeasurableSet {x : ℝ | |x - edgeVal N σ k| ≤ edgeTau0 τ ∧
      0 < (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)} :=
    (measurableSet_le (f := fun x : ℝ => |x - edgeVal N σ k|) (g := fun _ => edgeTau0 τ)
      (by fun_prop) measurable_const).inter
      (measurableSet_lt (f := fun _ : ℝ => (0 : ℝ))
        (g := fun x : ℝ => (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)) measurable_const
        (by fun_prop))
  refine ⟨hG, esr_varrho_null hG (fun x hx => ?_) (fun x hx => (rhoDens_edge h hk hx.1).2 hx.2)⟩
  have := (abs_le.mp hx.1).1
  change 0 < x
  linarith

/-- Near `a_k`, the gap side is outside `supp ϱ`. -/
private lemma esr_not_mem_support {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {E : ℝ}
    (hE : |E - edgeVal N σ k| < edgeTau0 τ)
    (hgap : 0 < (-1 : ℝ) ^ (k + 1) * (E - edgeVal N σ k)) : E ∉ (varrho N σ).support := by
  obtain ⟨-, hnull⟩ := esr_gap_null h hk
  rw [Measure.notMem_support_iff_exists]
  refine ⟨{x : ℝ | |x - edgeVal N σ k| < edgeTau0 τ ∧
      0 < (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ⟨hE, hgap⟩
    exact (isOpen_lt (f := fun x : ℝ => |x - edgeVal N σ k|) (g := fun _ => edgeTau0 τ)
      (by fun_prop) continuous_const).inter
      (isOpen_lt (f := fun _ : ℝ => (0 : ℝ))
        (g := fun x : ℝ => (-1 : ℝ) ^ (k + 1) * (x - edgeVal N σ k)) continuous_const
        (by fun_prop))
  · refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨hx.1.le, hx.2⟩

/-- Near `a_k`, the band side is in `supp ϱ`. -/
private lemma esr_mem_support {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {E : ℝ}
    (hE : |E - edgeVal N σ k| < edgeTau0 τ)
    (hband : (-1 : ℝ) ^ (k + 1) * (E - edgeVal N σ k) < 0) : E ∈ (varrho N σ).support := by
  obtain ⟨hN, hτ1, -⟩ := esr_facts h
  obtain ⟨-, hC2, -, -, -, -, -⟩ := esr_consts h.pos hτ1
  have hσ := h.nonneg
  set ε : ℝ := (-1) ^ (k + 1) with hεdef
  have hε : ε = 1 ∨ ε = -1 := neg_one_pow_eq_or ℝ (k + 1)
  set a := edgeVal N σ k with hadef
  have hκ : |E - a| = ε * (a - E) := by
    rw [abs_sub_comm]
    exact esr_abs_eq hε (by nlinarith)
  have hκ0 : 0 < ε * (a - E) := by nlinarith
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  set d := min δ (edgeTau0 τ - |E - a|) / 2 with hd
  have hd0 : 0 < d := by
    have : 0 < min δ (edgeTau0 τ - |E - a|) := lt_min hδ (by linarith)
    positivity
  have hdδ : d < δ := by
    have := min_le_left δ (edgeTau0 τ - |E - a|)
    linarith
  have hdt : d ≤ (edgeTau0 τ - |E - a|) / 2 := by
    have := min_le_right δ (edgeTau0 τ - |E - a|)
    linarith
  set L := √(ε * (a - E) / edgeC2 τ) / Real.pi with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]
    exact div_pos (Real.sqrt_pos.2 (div_pos hκ0 hC2)) Real.pi_pos
  obtain ⟨hS, hvol⟩ := esr_set hε E (d / 2) d
  have hpt : ∀ x, ε * (E - x) ∈ Set.Icc (d / 2) d →
      0 < x ∧ L ≤ rhoDens N σ x ∧ x ∈ U := by
    intro x hx
    have ht : ε * (a - x) = ε * (a - E) + ε * (E - x) := by ring
    have hb := esr_band_point h hk (x := x) (by rw [← hεdef, ← hadef, ht]; linarith [hx.1])
      (by rw [← hεdef, ← hadef, ht]; linarith [hx.2])
    rw [← hεdef, ← hadef] at hb
    refine ⟨hb.1, ?_, hball ?_⟩
    · rw [hLdef, div_le_iff₀' Real.pi_pos]
      refine le_trans (Real.sqrt_le_sqrt ?_) hb.2
      exact div_le_div_of_nonneg_right (by rw [ht]; linarith [hx.1]) hC2.le
    · rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, esr_abs_eq hε (by linarith [hx.1])]
      linarith [hx.2]
  have hge := esr_varrho_ge (N := N) (σ := σ) hS (fun x hx => (hpt x hx).1)
    (fun x hx => (hpt x hx).2.1)
  rw [hvol] at hge
  have hpos : 0 < ENNReal.ofReal L * ENNReal.ofReal (d - d / 2) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hL0).ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
  exact lt_of_lt_of_le hpos (hge.trans (measure_mono fun x hx => (hpt x hx).2.2))

/-! ## (m_sq_root) for `η < τ'` -/

/-- `Im m(w) ≤ (2/√c₂) √B` for `|w - a_k| ≤ B ≤ τ'₀`, from (z-a_taylor). -/
private lemma esr_im_le_sqrt {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {w : ℂ} (hw : 0 < w.im) {B : ℝ}
    (hwB : ‖w - edgeVal N σ k‖ ≤ B) (hB : B ≤ edgeTau0 τ) :
    (mFun N σ w).im ≤ 2 / √(edgec2 τ) * √B := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨hc2, -, -, -, -, -, -⟩ := esr_consts h.pos hτ1
  obtain ⟨-, -, l1, -, -⟩ := z_a_taylor h hk hw.le (hwB.trans hB)
  have hm : mExt N σ w = mFun N σ w := by simp [mExt, hw]
  rw [hm] at l1
  set v := mFun N σ w - xCrit N σ k with hv
  have him : (mFun N σ w).im = v.im := by simp [hv]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hwB
  have hsc := Real.sqrt_pos.2 hc2
  have hr : v.im ≤ ‖v‖ := (le_abs_self _).trans (Complex.abs_im_le_norm v)
  rw [him]
  refine hr.trans ?_
  have hsq : ‖v‖ ^ 2 ≤ (2 / √(edgec2 τ) * √B) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hc2.le, Real.sq_sqrt hB0]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- Band side, `η < τ'`: `C₂^{-1/2}/(4√2π) · √(κ + η) ≤ Im m`. -/
private lemma esr_band_lower {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {z : ℂ} (hη : 0 < z.im)
    (hηs : z.im < edgeTau' τ) (hE : |z.re - edgeVal N σ k| ≤ edgeTau' τ)
    (hband : (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k) ≤ 0) :
    (√(edgeC2 τ))⁻¹ / (4 * √2 * Real.pi) * √(|z.re - edgeVal N σ k| + z.im) ≤
      (mFun N σ z).im := by
  obtain ⟨hN, hτ1, -⟩ := esr_facts h
  obtain ⟨-, hC2, -, -, ht0, -, -⟩ := esr_consts h.pos hτ1
  have hσ := h.nonneg
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  set ε : ℝ := (-1) ^ (k + 1) with hεdef
  have hε : ε = 1 ∨ ε = -1 := neg_one_pow_eq_or ℝ (k + 1)
  have hε2 : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  set a := edgeVal N σ k with hadef
  set E := z.re with hEdef
  set η := z.im with hηdef
  set κ := |E - a| with hκdef
  have hκε : κ = ε * (a - E) := by
    rw [hκdef, abs_sub_comm]
    exact esr_abs_eq hε (by nlinarith)
  have hκ0 : 0 ≤ κ := abs_nonneg _
  set q := κ + η with hq
  set L := √(q / 2 / edgeC2 τ) / Real.pi with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hpt : ∀ x, ε * (a - x) ∈ Set.Icc (κ + η / 2) q →
      0 < x ∧ L ≤ rhoDens N σ x ∧ 1 / (2 * η) ≤ esrKer z x := by
    intro x hx
    have hb := esr_band_point h hk (x := x) (by rw [← hεdef, ← hadef]; linarith [hx.1])
      (by rw [← hεdef, ← hadef]; linarith [hx.2])
    rw [← hεdef, ← hadef] at hb
    refine ⟨hb.1, ?_, ?_⟩
    · rw [hLdef, div_le_iff₀' Real.pi_pos]
      refine le_trans (Real.sqrt_le_sqrt ?_) hb.2
      exact div_le_div_of_nonneg_right (by linarith [hx.1]) hC2.le
    · have e1 : ε * (x - E) = κ - ε * (a - x) := by rw [hκε]; ring
      have e2 : (x - E) ^ 2 = (ε * (a - x) - κ) ^ 2 := by
        rw [esr_sq_eq hε2 (x - E), e1]; ring
      have h3 : (ε * (a - x) - κ) ^ 2 ≤ η ^ 2 := by
        have h4 : 0 ≤ ε * (a - x) - κ := by linarith [hx.1]
        nlinarith [hx.2]
      unfold esrKer
      rw [← hEdef, ← hηdef, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hreal := esr_real_ge hσ hN hε (c := a) (p := κ + η / 2) (q := q) (L := L)
    (by linarith) hL0 (fun x hx => (hpt x hx).1) (fun x hx => (hpt x hx).2.1)
  obtain ⟨hS, -⟩ := esr_set hε a (κ + η / 2) q
  have hint := esr_integral_ge (varrho N σ) (esrKer_integrable _ hη) (esrKer_nonneg hη) hS
    (c := 1 / (2 * η)) (fun x hx => (hpt x hx).2.2)
  rw [← esr_im_mFun hσ hN hη] at hint
  refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left hreal (by positivity)) hint)
  have hs2 : √(q / 2 / edgeC2 τ) = √q / (√2 * √(edgeC2 τ)) := by
    rw [div_div, Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num)]
  have hsC := Real.sqrt_pos.2 hC2
  rw [hLdef, hs2]
  apply le_of_eq
  field_simp
  ring

/-- Gap side, `η < τ'`: `C₂^{-1/2}/(10π) · η/√(κ + η) ≤ Im m`. -/
private lemma esr_gap_lower {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {z : ℂ} (hη : 0 < z.im)
    (hηs : z.im < edgeTau' τ) (hE : |z.re - edgeVal N σ k| ≤ edgeTau' τ)
    (hgap : 0 ≤ (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k)) :
    (√(edgeC2 τ))⁻¹ / (10 * Real.pi) * (z.im / √(|z.re - edgeVal N σ k| + z.im)) ≤
      (mFun N σ z).im := by
  obtain ⟨hN, hτ1, -⟩ := esr_facts h
  obtain ⟨-, hC2, -, -, ht0, -, -⟩ := esr_consts h.pos hτ1
  have hσ := h.nonneg
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  set ε : ℝ := (-1) ^ (k + 1) with hεdef
  have hε : ε = 1 ∨ ε = -1 := neg_one_pow_eq_or ℝ (k + 1)
  have hε2 : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  set a := edgeVal N σ k with hadef
  set E := z.re with hEdef
  set η := z.im with hηdef
  set κ := |E - a| with hκdef
  have hκε : κ = ε * (E - a) := esr_abs_eq hε hgap
  have hκ0 : 0 ≤ κ := abs_nonneg _
  set b := κ + η with hbdef
  have hb0 : 0 < b := by linarith
  set L := √(b / edgeC2 τ) / Real.pi with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hpt : ∀ x, ε * (a - x) ∈ Set.Icc b (2 * b) →
      0 < x ∧ L ≤ rhoDens N σ x ∧ η / (10 * b ^ 2) ≤ esrKer z x := by
    intro x hx
    have hb := esr_band_point h hk (x := x) (by rw [← hεdef, ← hadef]; linarith [hx.1])
      (by rw [← hεdef, ← hadef]; linarith [hx.2])
    rw [← hεdef, ← hadef] at hb
    refine ⟨hb.1, ?_, ?_⟩
    · rw [hLdef, div_le_iff₀' Real.pi_pos]
      refine le_trans (Real.sqrt_le_sqrt ?_) hb.2
      exact div_le_div_of_nonneg_right hx.1 hC2.le
    · have e1 : ε * (x - E) = -(ε * (a - x)) - κ := by rw [hκε]; ring
      have e2 : (x - E) ^ 2 = (ε * (a - x) + κ) ^ 2 := by
        rw [esr_sq_eq hε2 (x - E), e1]; ring
      have h3 : (ε * (a - x) + κ) ^ 2 ≤ (3 * b) ^ 2 := by
        have h4 : 0 ≤ ε * (a - x) + κ := by linarith [hx.1]
        nlinarith [hx.2]
      have h5 : (ε * (a - x) + κ) ^ 2 + η ^ 2 ≤ 10 * b ^ 2 := by nlinarith
      unfold esrKer
      rw [← hEdef, ← hηdef, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left h5 hη.le
  have hreal := esr_real_ge hσ hN hε (c := a) (p := b) (q := 2 * b) (L := L)
    (by linarith) hL0 (fun x hx => (hpt x hx).1) (fun x hx => (hpt x hx).2.1)
  obtain ⟨hS, -⟩ := esr_set hε a b (2 * b)
  have hint := esr_integral_ge (varrho N σ) (esrKer_integrable _ hη) (esrKer_nonneg hη) hS
    (c := η / (10 * b ^ 2)) (fun x hx => (hpt x hx).2.2)
  rw [← esr_im_mFun hσ hN hη] at hint
  refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left hreal (by positivity)) hint)
  have hsb := Real.sqrt_pos.2 hb0
  have hsbb : √b * √b = b := Real.mul_self_sqrt hb0.le
  have hsC := Real.sqrt_pos.2 hC2
  rw [hLdef, Real.sqrt_div' _ hC2.le]
  have hb' : b = √b ^ 2 := (Real.sq_sqrt hb0.le).symm
  generalize √b = s at hb' hsb ⊢
  rw [hb']
  apply le_of_eq
  field_simp
  ring

/-- Gap side, `η < τ'`: `Im m ≤ (4/√c₂ + √(2/τ)/τ'²) · η/√(κ + η)`. -/
private lemma esr_gap_upper {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {z : ℂ} (hη : 0 < z.im)
    (hηs : z.im < edgeTau' τ) (hE : |z.re - edgeVal N σ k| ≤ edgeTau' τ)
    (hgap : 0 ≤ (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k)) :
    (mFun N σ z).im ≤ (4 / √(edgec2 τ) + √(2 / τ) / edgeTau' τ ^ 2) *
      (z.im / √(|z.re - edgeVal N σ k| + z.im)) := by
  obtain ⟨hN, hτ1, -⟩ := esr_facts h
  obtain ⟨hc2, -, -, -, ht0, htτ, -⟩ := esr_consts h.pos hτ1
  have hσ := h.nonneg
  have hτ := h.pos
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  have ht'0 : 0 < edgeTau' τ := by rw [hτ']; positivity
  set ε : ℝ := (-1) ^ (k + 1) with hεdef
  have hε : ε = 1 ∨ ε = -1 := neg_one_pow_eq_or ℝ (k + 1)
  have hε2 : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  set a := edgeVal N σ k with hadef
  set E := z.re with hEdef
  set η := z.im with hηdef
  set κ := |E - a| with hκdef
  have hκε : κ = ε * (E - a) := esr_abs_eq hε hgap
  have hκ0 : 0 ≤ κ := abs_nonneg _
  set b := κ + η with hbdef
  have hb0 : 0 < b := by linarith
  set τ' := edgeTau' τ with hτ'def
  -- the comparison point `a + ib`
  set z' : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hz'
  have hz're : z'.re = a := by simp [hz']
  have hz'im : z'.im = b := by simp [hz']
  have hz'0 : 0 < z'.im := by rw [hz'im]; exact hb0
  have hm' : (mFun N σ z').im ≤ 2 / √(edgec2 τ) * √b := by
    refine esr_im_le_sqrt h hk hz'0 (le_of_eq ?_) (by linarith)
    rw [hz', add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hb0]
  -- pointwise bound off the `ϱ`-null gap side
  obtain ⟨hG, hnull⟩ := esr_gap_null h hk
  have hae := measure_eq_zero_iff_ae_notMem.1 hnull
  have hpt : ∀ x : ℝ, x ∉ {x : ℝ | |x - a| ≤ edgeTau0 τ ∧ 0 < ε * (x - a)} →
      esrKer z x ≤ 2 * η / b * esrKer z' x + η / τ' ^ 2 := by
    intro x hx
    simp only [Set.mem_ofPred_eq, not_and_or, not_le, not_lt] at hx
    have hk0 : 0 ≤ esrKer z' x := esrKer_nonneg hz'0 x
    by_cases hside : ε * (x - a) ≤ 0
    · set t := ε * (a - x) with ht
      have ht0 : 0 ≤ t := by rw [ht]; nlinarith
      have e1 : ε * (x - E) = -t - κ := by rw [hκε, ht]; ring
      have e2 : (x - E) ^ 2 = (t + κ) ^ 2 := by rw [esr_sq_eq hε2 (x - E), e1]; ring
      have e3 : (x - a) ^ 2 = t ^ 2 := by
        rw [esr_sq_eq hε2 (x - a), ht]; ring
      have hle : esrKer z x ≤ 2 * η / b * esrKer z' x := by
        unfold esrKer
        rw [← hEdef, ← hηdef, hz're, hz'im, e2, e3]
        rw [show 2 * η / b * (b / (t ^ 2 + b ^ 2)) = 2 * η / (t ^ 2 + b ^ 2) by
          field_simp]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hκ0 ht0, mul_nonneg hκ0 hη.le, sq_nonneg (κ - η)]
      have : 0 ≤ η / τ' ^ 2 := by positivity
      linarith
    · have hfar : edgeTau0 τ < |x - a| := by
        rcases hx with hx | hx
        · exact hx
        · exact absurd hx hside
      have hxE : τ' ≤ |x - E| := by
        have h1 : |x - a| ≤ |x - E| + |E - a| := abs_sub_le x E a
        rw [← hκdef] at h1
        linarith
      have hsq : τ' ^ 2 ≤ (x - E) ^ 2 := by
        rw [← sq_abs (x - E)]
        exact pow_le_pow_left₀ ht'0.le hxE 2
      have hle : esrKer z x ≤ η / τ' ^ 2 := by
        unfold esrKer
        rw [← hEdef, ← hηdef]
        exact div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)
      have : 0 ≤ 2 * η / b * esrKer z' x := by positivity
      linarith
  have hint : ∫ x, esrKer z x ∂(varrho N σ) ≤
      ∫ x, (2 * η / b * esrKer z' x + η / τ' ^ 2) ∂(varrho N σ) :=
    integral_mono_ae (esrKer_integrable _ hη)
      (((esrKer_integrable _ hz'0).const_mul _).add (integrable_const _))
      (hae.mono fun x hx => hpt x hx)
  rw [integral_add ((esrKer_integrable _ hz'0).const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul, ← esr_im_mFun hσ hN hz'0,
    ← esr_im_mFun hσ hN hη] at hint
  refine hint.trans ?_
  have hsb := Real.sqrt_pos.2 hb0
  have hsbb : √b * √b = b := Real.mul_self_sqrt hb0.le
  have hsc := Real.sqrt_pos.2 hc2
  have hb2 : √b ≤ √(2 / τ) := by
    refine Real.sqrt_le_sqrt ?_
    have h1 : 1 ≤ 2 / τ := by rw [le_div_iff₀ hτ]; linarith
    linarith
  have h1 : 2 * η / b * (mFun N σ z').im ≤ 4 / √(edgec2 τ) * (η / √b) := by
    calc 2 * η / b * (mFun N σ z').im ≤ 2 * η / b * (2 / √(edgec2 τ) * √b) :=
          mul_le_mul_of_nonneg_left hm' (by positivity)
      _ = 4 / √(edgec2 τ) * (η / √b) := by
          have hb' : b = √b ^ 2 := (Real.sq_sqrt hb0.le).symm
          generalize √b = s at hb' hsb ⊢
          rw [hb']
          field_simp
          ring
  have h2 : η / τ' ^ 2 ≤ √(2 / τ) / τ' ^ 2 * (η / √b) := by
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    have : η / τ' ^ 2 * (τ' ^ 2 * √b) = η * √b := by field_simp
    rw [this, mul_comm (√(2 / τ)) η]
    exact mul_le_mul_of_nonneg_left hb2 hη.le
  linarith

/-! ## (m_sq_root) for `η ≥ τ'` -/

/-- `η ≥ τ'`: the four bounds from `C_m⁻¹η ≤ Im m ≤ C_m` and `τ' ≤ κ + η ≤ 2/τ`. -/
private lemma esr_large {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {z : ℂ}
    (hz : z ∈ specDomain τ N) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ edgeTau' τ)
    (hηl : edgeTau' τ ≤ z.im) :
    edgeTau' τ * √(τ / 2) / mBoundConst τ * √(κ + z.im) ≤ (mFun N σ z).im ∧
      (mFun N σ z).im ≤ mBoundConst τ / √(edgeTau' τ) * √(κ + z.im) ∧
      √(edgeTau' τ) / mBoundConst τ * (z.im / √(κ + z.im)) ≤ (mFun N σ z).im ∧
      (mFun N σ z).im ≤ mBoundConst τ * √(2 / τ) / edgeTau' τ * (z.im / √(κ + z.im)) := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨-, -, -, -, ht0, htτ, hCm⟩ := esr_consts h.pos hτ1
  have hτ := h.pos
  obtain ⟨-, hmC, hmlow⟩ := gen_prop_m_specDomain h hz
  have hηu : z.im ≤ τ⁻¹ := hz.2.2.2.2
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  set τ' := edgeTau' τ with hτ'def
  set η := z.im with hηdef
  set C := mBoundConst τ with hCdef
  have ht'0 : 0 < τ' := by rw [hτ']; positivity
  have hη0 : 0 < η := lt_of_lt_of_le ht'0 hηl
  set b := κ + η with hbdef
  have hb0 : 0 < b := by linarith
  have hbl : τ' ≤ b := by linarith
  have hτi : 1 ≤ τ⁻¹ := one_le_inv₀ hτ |>.2 hτ1
  have hbu : b ≤ 2 / τ := by
    have : 2 / τ = 2 * τ⁻¹ := by ring
    rw [this]
    linarith
  have hsb := Real.sqrt_pos.2 hb0
  have hst := Real.sqrt_pos.2 ht'0
  have him_le : (mFun N σ z).im ≤ C := (Complex.im_le_norm _).trans hmC
  have him_ge : η / C ≤ (mFun N σ z).im := by rw [div_eq_inv_mul]; exact hmlow
  have hsbl : √τ' ≤ √b := Real.sqrt_le_sqrt hbl
  have hsbu : √b ≤ √(2 / τ) := Real.sqrt_le_sqrt hbu
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hprod : √(τ / 2) * √b ≤ 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_one.mpr ?_
      have : τ / 2 * b ≤ τ / 2 * (2 / τ) := mul_le_mul_of_nonneg_left hbu (by positivity)
      rw [show τ / 2 * (2 / τ) = 1 by field_simp] at this
      exact this
    calc τ' * √(τ / 2) / C * √b = τ' / C * (√(τ / 2) * √b) := by ring
      _ ≤ τ' / C * 1 := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ η / C := by rw [mul_one]; exact div_le_div_of_nonneg_right hηl hCm.le
      _ ≤ _ := him_ge
  · refine him_le.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hst]
    exact mul_le_mul_of_nonneg_left hsbl hCm.le
  · refine le_trans ?_ him_ge
    have hr : √τ' / √b ≤ 1 := (div_le_one hsb).2 hsbl
    calc √τ' / C * (η / √b) = η / C * (√τ' / √b) := by ring
      _ ≤ η / C * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = η / C := mul_one _
  · refine him_le.trans ?_
    have h1 : τ' * √b ≤ √(2 / τ) * η := by
      calc τ' * √b ≤ η * √(2 / τ) := mul_le_mul hηl hsbu hsb.le hη0.le
        _ = √(2 / τ) * η := mul_comm _ _
    have hr : 1 ≤ √(2 / τ) * η / (τ' * √b) := (one_le_div (by positivity)).2 h1
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (√(2 / τ) * η / (τ' * √b)) := mul_le_mul_of_nonneg_left hr hCm.le
      _ = C * √(2 / τ) / τ' * (η / √b) := by ring

/-! ## Lemma A.4 -/

/-- Lemma A.4, (m_sq_root) on `𝐃^e_k(τ, τ'')`, `τ'' ≤ τ'(τ)`. -/
theorem m_sq_root_edge {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hz : z ∈ edgeDomain τ τ'' N σ k) :
    (z.re ∈ (varrho N σ).support →
      sqLower τ * √(kappa N σ z.re + z.im) ≤ (mFun N σ z).im ∧
        (mFun N σ z).im ≤ sqUpper τ * √(kappa N σ z.re + z.im)) ∧
    (z.re ∉ (varrho N σ).support →
      sqLower τ * (z.im / √(kappa N σ z.re + z.im)) ≤ (mFun N σ z).im ∧
        (mFun N σ z).im ≤ sqUpper τ * (z.im / √(kappa N σ z.re + z.im))) := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨hc2, hC2, -, -, ht0, htτ, hCm⟩ := esr_consts h.pos hτ1
  have hτ := h.pos
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  have ht'0 : 0 < edgeTau' τ := by rw [hτ']; positivity
  have hη : 0 < z.im := hz.1.1
  have hE : |z.re - edgeVal N σ k| ≤ edgeTau' τ := by
    obtain ⟨-, h1, h2⟩ := hz
    rw [abs_le]; constructor <;> linarith
  have hEt : |z.re - edgeVal N σ k| < edgeTau0 τ := by linarith
  rw [kappa_edgeDomain h hk (by linarith) hz]
  set κ := |z.re - edgeVal N σ k| with hκdef
  have hκ0 : 0 ≤ κ := abs_nonneg _
  have hsq0 : 0 ≤ √(κ + z.im) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ z.im / √(κ + z.im) := by positivity
  -- the entries of `sqLower` and `sqUpper`
  have hL1 : sqLower τ ≤ (√(edgeC2 τ))⁻¹ / (4 * √2 * Real.pi) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hL2 : sqLower τ ≤ edgeTau' τ * √(τ / 2) / mBoundConst τ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hL3 : sqLower τ ≤ (√(edgeC2 τ))⁻¹ / (10 * Real.pi) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hL4 : sqLower τ ≤ √(edgeTau' τ) / mBoundConst τ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hU1 : 6 * √2 / √(edgec2 τ) + (√τ)⁻¹ / edgeTau' τ ^ 2 ≤ sqUpper τ :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hU2 : mBoundConst τ / √(edgeTau' τ) ≤ sqUpper τ :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hU3 : 4 / √(edgec2 τ) + √(2 / τ) / edgeTau' τ ^ 2 ≤ sqUpper τ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hU4 : mBoundConst τ * √(2 / τ) / edgeTau' τ ≤ sqUpper τ :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases hηs : z.im < edgeTau' τ
  · -- `η < τ'`
    have hup : (mFun N σ z).im ≤ 2 / √(edgec2 τ) * √(κ + z.im) := by
      refine esr_im_le_sqrt h hk hη ?_ (by linarith)
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - edgeVal N σ k)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero, abs_of_pos hη] at h1
      exact h1
    have hsc := Real.sqrt_pos.2 hc2
    have h2le : 2 / √(edgec2 τ) ≤ 6 * √2 / √(edgec2 τ) + (√τ)⁻¹ / edgeTau' τ ^ 2 := by
      have h1 : 2 / √(edgec2 τ) ≤ 6 * √2 / √(edgec2 τ) := by
        refine div_le_div_of_nonneg_right ?_ hsc.le
        have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
        linarith
      have : 0 ≤ (√τ)⁻¹ / edgeTau' τ ^ 2 := by positivity
      linarith
    refine ⟨fun hsupp => ⟨?_, ?_⟩, fun hsupp => ⟨?_, ?_⟩⟩
    · have hband : (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k) ≤ 0 := by
        by_contra hc
        exact esr_not_mem_support h hk hEt (lt_of_not_ge hc) hsupp
      exact (mul_le_mul_of_nonneg_right hL1 hsq0).trans (esr_band_lower h hk hη hηs hE hband)
    · exact hup.trans (mul_le_mul_of_nonneg_right (h2le.trans hU1) hsq0)
    · have hgap : 0 ≤ (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k) := by
        by_contra hc
        exact hsupp (esr_mem_support h hk hEt (lt_of_not_ge hc))
      exact (mul_le_mul_of_nonneg_right hL3 hq0).trans (esr_gap_lower h hk hη hηs hE hgap)
    · have hgap : 0 ≤ (-1 : ℝ) ^ (k + 1) * (z.re - edgeVal N σ k) := by
        by_contra hc
        exact hsupp (esr_mem_support h hk hEt (lt_of_not_ge hc))
      exact (esr_gap_upper h hk hη hηs hE hgap).trans (mul_le_mul_of_nonneg_right hU3 hq0)
  · -- `η ≥ τ'`
    obtain ⟨l1, u1, l2, u2⟩ := esr_large h hz.1 hκ0 hE (not_lt.mp hηs)
    exact ⟨fun _ => ⟨(mul_le_mul_of_nonneg_right hL2 hsq0).trans l1,
        u1.trans (mul_le_mul_of_nonneg_right hU2 hsq0)⟩,
      fun _ => ⟨(mul_le_mul_of_nonneg_right hL4 hq0).trans l2,
        u2.trans (mul_le_mul_of_nonneg_right hU4 hq0)⟩⟩

/-- Lemma A.4, (mz_reg) on `𝐃^e_k(τ, τ'')`. -/
theorem mz_reg_edge {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hz : z ∈ edgeDomain τ τ'' N σ k) :
    ∀ s ∈ posVals σ, edgeMz τ ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨-, -, -, hρτ, ht0, htτ, hCm⟩ := esr_consts h.pos hτ1
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  have hη : 0 < z.im := hz.1.1
  intro s hs
  by_cases hηs : z.im < edgeTau' τ
  · have hE : |z.re - edgeVal N σ k| ≤ edgeTau' τ := by
      obtain ⟨-, h1, h2⟩ := hz
      rw [abs_le]; constructor <;> linarith
    have hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - edgeVal N σ k)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero, abs_of_pos hη] at h1
      linarith
    obtain ⟨hloc, -⟩ := z_a_taylor h hk hη.le hza
    have hm : mExt N σ z = mFun N σ z := by simp [mExt, hη]
    rw [hm] at hloc
    have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
      rintro ⟨hk', hy⟩
      have : edgeVal N σ k = 0 := by
        unfold edgeVal
        simp only [hk', ↓reduceIte, hy]
        simp [FChart]
      linarith [hk.2.2.1, h.pos]
    have hreg := hk.2.2.2.2 hfin s hs
    have htri : ‖((xCrit N σ k + s⁻¹ : ℝ) : ℂ)‖ ≤
        ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ + ‖mFun N σ z - xCrit N σ k‖ := by
      have e : ((xCrit N σ k + s⁻¹ : ℝ) : ℂ) =
          (mFun N σ z + ((s⁻¹ : ℝ) : ℂ)) - (mFun N σ z - xCrit N σ k) := by
        push_cast; ring
      rw [e]
      exact norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at htri
    have : edgeMz τ ≤ τ / 2 := min_le_left _ _
    linarith
  · have hηl : edgeTau' τ ≤ z.im := not_lt.mp hηs
    obtain ⟨-, -, hmlow⟩ := gen_prop_m_specDomain h hz.1
    have h1 : (mFun N σ z).im ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
      have := Complex.im_le_norm (mFun N σ z + ((s⁻¹ : ℝ) : ℂ))
      simpa using this
    have h2 : edgeMz τ ≤ edgeTau' τ / mBoundConst τ := min_le_right _ _
    have h3 : edgeTau' τ / mBoundConst τ ≤ (mBoundConst τ)⁻¹ * z.im := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hηl (inv_nonneg.2 hCm.le)
    linarith

/-- (1+xm) on `𝐃^e_k(τ, τ'')`. -/
theorem one_add_mul_mFun_edge {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hz : z ∈ edgeDomain τ τ'' N σ k) :
    ∀ i, oneXmConst (edgeMz τ) (mBoundConst τ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖ := by
  obtain ⟨-, hτ1, -⟩ := esr_facts h
  obtain ⟨-, -, -, -, ht0, -, hCm⟩ := esr_consts h.pos hτ1
  have hτ' : edgeTau' τ = edgeTau0 τ / 4 := rfl
  have hc : 0 < edgeMz τ := by
    have : 0 < edgeTau' τ := by rw [hτ']; positivity
    unfold edgeMz
    exact lt_min (half_pos h.pos) (div_pos this hCm)
  exact one_add_mul_ge_of_mz_reg h.nonneg hc hCm (gen_prop_m_specDomain h hz.1).2.1
    (mz_reg_edge h hk hτ'' hz)

/-! ## Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `τ = 1/20` (`φ = 1/2`, `p = 1`, `x_1 = √2 - 2`,
`a_1 = 3/2 + √2`), at the edge `k = 1`, `τ'' = τ'(1/20)`, at `z = a_1 + i ∈ 𝐃^e_1`
(the regime `η ≥ τ'`). -/

local notation "σMP" => (fun _ : Fin 1 => (1 : ℝ))
local notation "xMP" => xCrit 2 σMP 1
local notation "aMP" => edgeVal 2 σMP 1

/-- The constants at `τ = 1/20` are positive. -/
example : 0 < sqLower (1 / 20) ∧ 0 < edgeMz (1 / 20) := by
  obtain ⟨-, hC2, -, -, ht0, -, hCm⟩ := esr_consts (τ := 1 / 20) (by norm_num) (by norm_num)
  have ht : 0 < edgeTau' (1 / 20) := by change 0 < edgeTau0 (1 / 20) / 4; positivity
  refine ⟨?_, ?_⟩
  · unfold sqLower
    refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity
  · unfold edgeMz
    exact lt_min (by norm_num) (by positivity)

end Anisotropic
