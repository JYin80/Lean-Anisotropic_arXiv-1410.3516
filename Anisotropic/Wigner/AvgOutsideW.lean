module

public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.AvgMain
public import Anisotropic.Wigner.AvgOutside
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.EdgeDefs
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.SelfConsistent

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The strong averaged bound for `W + A` outside the spectrum -/

/-- Cauchy estimate and mean value: if `|g| ≤ B` on `B(E, r)`, then `g` is `4B/r`-Lipschitz on
`B(E, 3r/4)`. -/
private theorem aux_lip {g : ℂ → ℂ} {E r B : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball (E : ℂ) r))
    (hB : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖g ζ‖ ≤ B) {w₁ w₂ : ℂ}
    (h₁ : w₁ ∈ Metric.ball (E : ℂ) (3 * r / 4)) (h₂ : w₂ ∈ Metric.ball (E : ℂ) (3 * r / 4)) :
    ‖g w₂ - g w₁‖ ≤ 4 * B / r * ‖w₂ - w₁‖ := by
  have hsub : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4),
      Metric.closedBall x (r / 4) ⊆ Metric.ball (E : ℂ) r := by
    intro x hx y hy
    rw [mem_ball_iff_norm] at hx ⊢
    rw [mem_closedBall_iff_norm] at hy
    calc ‖y - E‖ = ‖(y - x) + (x - E)‖ := by ring_nf
      _ ≤ ‖y - x‖ + ‖x - E‖ := norm_add_le _ _
      _ < r := by linarith
  have hd : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4), DifferentiableAt ℂ g x := fun x hx =>
    hg.differentiableAt (Metric.isOpen_ball.mem_nhds
      (hsub x hx (Metric.mem_closedBall_self (by positivity))))
  have hder : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4), ‖deriv g x‖ ≤ 4 * B / r := by
    intro x hx
    have hR : (0 : ℝ) < r / 4 := by positivity
    have hcont : DiffContOnCl ℂ g (Metric.ball x (r / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hR.ne']
      exact hg.mono (hsub x hx)
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hcont
      (fun y hy => hB y (hsub x hx (Metric.sphere_subset_closedBall hy)))
    calc ‖deriv g x‖ ≤ B / (r / 4) := this
      _ = 4 * B / r := by field_simp
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hder (convex_ball _ _) h₁ h₂


/-- The standing bound is invariant under the reflection `a ↦ −a` (through `m^W_{−a}(−z̄) =
−conj m^W_a(z)`). -/
private theorem aux_sb_neg {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} {a : Fin N → ℝ}
    (h : StandingBoundW τ a (domW τ N)) : StandingBoundW τ (-a) (domW τ N) := by
  intro z hz i
  set w := -(starRingEnd ℂ) z with hwdef
  have hw : w ∈ domW τ N := by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨by simpa [w] using h1, by simpa [w] using h2, by simpa [w] using h3,
      by simpa [w] using h4⟩
  have hz' : -(starRingEnd ℂ) w = z := by simp [w]
  have hm : mW (-a) z = -(starRingEnd ℂ) (mW a w) := by rw [← hz']; exact mW_neg hN a hw.1
  have e : -(mW (-a) z) + (((-a) i : ℝ) : ℂ) - z = -(starRingEnd ℂ) (-(mW a w) + a i - w) := by
    rw [hm, ← hz']
    simp only [map_sub, map_add, map_neg, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg,
]
    ring
  rw [e, norm_neg, Complex.norm_conj]
  exact h w hw i

/-- `X ≤ N^p` for all large `N`, when `p > 0`. -/
private theorem aux_ev_rpow {p : ℝ} (hp : 0 < p) (X : ℝ) :
    ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)

/-- `S(maxᵢ aᵢ + 1) ≤ 1`. -/
private theorem aux_sW_le_one {N : ℕ} (a : Fin N → ℝ) : sW a ((⨆ i, a i) + 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp [sW]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
  unfold sW
  have h : ∀ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ 1 := by
    intro i
    have := le_ciSup (Set.finite_range a).bddAbove i
    apply inv_le_one_of_one_le₀
    nlinarith
  calc (N : ℝ)⁻¹ * ∑ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = 1 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]; field_simp

/-- `S` is continuous at every point to the right of the spectrum. -/
private theorem aux_sW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : ∀ i, a i < x) :
    ContinuousAt (sW a) x := by
  unfold sW
  refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
  have hne : (a i - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hx i).ne)
  exact ((continuousAt_const.sub continuousAt_id).pow 2).inv₀ hne

/-- If `maxᵢ aᵢ + τ/4 ≤ x₊`: `x₊ ≤ maxᵢ aᵢ + 1` and `S(x₊) = 1`. -/
private theorem aux_xp_facts {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {a : Fin N → ℝ}
    (hgap : (⨆ i, a i) + τ / 4 ≤ xpW a) : xpW a ≤ (⨆ i, a i) + 1 ∧ sW a (xpW a) = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  set T := {x | α < x ∧ sW a x ≤ 1} with hT
  have hbdd : BddBelow T := ⟨α, fun x hx => hx.1.le⟩
  have hmem : α + 1 ∈ T := ⟨by linarith, aux_sW_le_one a⟩
  have hxp : xpW a = sInf T := rfl
  have hup : xpW a ≤ α + 1 := hxp ▸ csInf_le hbdd hmem
  refine ⟨hup, ?_⟩
  have hgt : ∀ i, a i < xpW a := fun i => by linarith [hle i]
  have hc := aux_sW_continuousAt a hgt
  apply le_antisymm
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), 1 < sW a y := hc.eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨y, hyT, hy⟩ := exists_lt_of_csInf_lt ⟨α + 1, hmem⟩
      (show sInf T < xpW a + δ by rw [← hxp]; linarith)
    have hy1 : xpW a ≤ y := hxp ▸ csInf_le hbdd hyT
    have : dist y (xpW a) < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball this, hyT.2]
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), sW a y < 1 := hc.eventually (gt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set y := xpW a - min (δ / 2) (τ / 8) with hy
    have hm1 : 0 < min (δ / 2) (τ / 8) := lt_min (by linarith) (by linarith)
    have hm2 : min (δ / 2) (τ / 8) ≤ δ / 2 := min_le_left _ _
    have hm3 : min (δ / 2) (τ / 8) ≤ τ / 8 := min_le_right _ _
    have hyd : dist y (xpW a) < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hyT : y ∈ T := ⟨by linarith, (hball hyd).le⟩
    have := hxp ▸ csInf_le hbdd hyT
    linarith

/-- `−B ≤ L₊ ≤ B + 2` when `|aᵢ| ≤ B` (`L₊ = x₊ + N⁻¹ ∑ᵢ (x₊ − aᵢ)⁻¹`, `x₊ ≤ maxᵢ aᵢ + 1`,
and `N⁻¹ ∑ᵢ (x₊ − aᵢ)⁻¹ ≤ S(x₊)^{1/2} = 1`). -/
private theorem aux_LpW_bounds {τ : ℝ} (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ τ⁻¹ - 2) →
      StandingBoundW τ a (domW τ N) → ∀ B : ℝ, (∀ i, |a i| ≤ B) → -B ≤ LpW a ∧ LpW a ≤ B + 2 := by
  obtain ⟨N₁, hN₁⟩ := xpW_sub_ge hτ
  refine ⟨max N₁ 1, fun N hN a ha hSB B hB => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have : Nonempty (Fin N) := ⟨⟨0, hN1⟩⟩
  have hgap := (hN₁ N (le_of_max_le_left hN) a ha hSB).1
  obtain ⟨hup, hS⟩ := aux_xp_facts hN1 hτ hgap
  set x := xpW a with hx
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  have hpos : ∀ i, 0 < x - a i := fun i => by linarith [hle i]
  set u : Fin N → ℝ := fun i => (x - a i)⁻¹ with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => (inv_pos.2 (hpos i)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : LpW a = x + (N : ℝ)⁻¹ * ∑ i, u i := by
    rw [show LpW a = gW a x from rfl]
    unfold gW
    have : ∀ i, (a i - x)⁻¹ = -u i := fun i => by simp only [hu]; rw [← inv_neg, neg_sub]
    simp only [this, Finset.sum_neg_distrib]
    ring
  have hsq : ∑ i, u i ^ 2 = N := by
    have h1 : sW a x = (N : ℝ)⁻¹ * ∑ i, u i ^ 2 := by
      unfold sW
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hu, inv_pow]
      congr 1
      ring
    rw [hS] at h1
    field_simp at h1
    linarith
  have hsum : ∑ i, u i ≤ N := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := u)
    rw [hsq, Finset.card_univ, Fintype.card_fin] at hcs
    have h0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu0 i
    nlinarith
  have hmean0 : 0 ≤ (N : ℝ)⁻¹ * ∑ i, u i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hu0 i)
  have hmean1 : (N : ℝ)⁻¹ * ∑ i, u i ≤ 1 := by
    rw [inv_mul_le_iff₀ hNpos]; linarith
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  have hα1 := abs_le.1 (hB i₀)
  rw [hi₀] at hα1
  constructor
  · rw [hL]; linarith [hle ⟨0, hN1⟩, abs_le.1 (hB ⟨0, hN1⟩)]
  · rw [hL]; linarith

/-- `|E| ≤ B + 2 + X` when `0 < κ(E) ≤ X`, `−B ≤ L₊ ≤ B + 2` and `−(B + 2) ≤ L₋ ≤ B`. -/
private theorem aux_E_bound {N : ℕ} {a : Fin N → ℝ} {E B X : ℝ} (hκ : 0 < kappaW a E)
    (hκX : kappaW a E ≤ X) (hp : -B ≤ LpW a ∧ LpW a ≤ B + 2) (hm : -(B + 2) ≤ LmW a ∧ LmW a ≤ B) :
    |E| ≤ B + 2 + X := by
  unfold kappaW at hκ hκX
  rcases max_choice (max (E - LpW a) (LmW a - E)) 0 with h0 | h0
  swap
  · rw [h0] at hκ; exact absurd hκ (lt_irrefl 0)
  rw [h0] at hκ hκX
  rw [abs_le]
  rcases max_choice (E - LpW a) (LmW a - E) with h1 | h1
  · rw [h1] at hκ hκX
    constructor <;> linarith [hp.1, hp.2]
  · rw [h1] at hκ hκX
    constructor <;> linarith [hm.1, hm.2]

/-- `Im m^W_{−a}(−x + iy) = Im m^W_a(x + iy)` for `y > 0`. -/
private lemma aux_im_neg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {x y : ℝ} (hy : 0 < y) :
    (mW (-a) ⟨-x, y⟩).im = (mW a ⟨x, y⟩).im := by
  have e : (⟨-x, y⟩ : ℂ) = -(starRingEnd ℂ) ⟨x, y⟩ := Complex.ext (by simp) (by simp)
  rw [e, mW_neg hN a (by simpa using hy)]
  simp

/-- To the right of `L₊`: `Im m^W(z) · min(√(E − L₊), 1) ≤ K η`, from the square-root bound near
`L₊` and the continuation of `m^W` across `(L₊, ∞)` away from it. -/
private theorem aux_im_right {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) →
      ∀ z : ℂ, 0 < z.im → LpW a < z.re →
        (mW a z).im * min √(z.re - LpW a) 1 ≤ K * z.im := by
  obtain ⟨cs, Ks, hcs, hKs, Ns, hsq⟩ := im_mW_sqrt_edge hτ
  obtain ⟨c, Kc, hc, hc4, hKc, Nc, hcont⟩ := mW_continuation_right hτ
  set m₀ := min (cs / 2) 1 with hm₀
  have hm₀pos : 0 < m₀ := lt_min (by linarith) one_pos
  have hK1 : 0 ≤ 2 / cs := by positivity
  have hK2 : 0 ≤ (4 * Kc + 2) / (c * m₀) := by positivity
  refine ⟨Ks + 2 / cs + (4 * Kc + 2) / (c * m₀), by positivity, max (max Ns Nc) 1,
    fun N hN a ha hSB z hz hE => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNs : N ≥ Ns := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hNc : N ≥ Nc := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  set κ := z.re - LpW a with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨hmpos, -⟩ := mW_spec hN1 a hz
  have hm1 : (mW a z).im < 1 :=
    lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN1 a hz)
  have hmin1 : min √κ 1 ≤ 1 := min_le_right _ _
  have hle_im : (mW a z).im * min √κ 1 ≤ (mW a z).im := mul_le_of_le_one_right hmpos.le hmin1
  have hη := hz.le
  by_cases hnear : ‖z - (LpW a : ℂ)‖ ≤ cs
  · have h := ((hsq N hNs a ha hSB z hz hnear).2 hE.le).2
    have hpos : 0 < √(κ + z.im) := Real.sqrt_pos.2 (by linarith)
    have h1 : min √κ 1 ≤ √(κ + z.im) :=
      (min_le_left _ _).trans (Real.sqrt_le_sqrt (by linarith))
    have h2 : (mW a z).im * √(κ + z.im) ≤ Ks * z.im := by
      have := mul_le_mul_of_nonneg_right h hpos.le
      rwa [mul_assoc, div_mul_cancel₀ _ hpos.ne'] at this
    calc (mW a z).im * min √κ 1 ≤ (mW a z).im * √(κ + z.im) :=
          mul_le_mul_of_nonneg_left h1 hmpos.le
      _ ≤ Ks * z.im := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hη
  · push Not at hnear
    have hsum : cs < κ + z.im := by
      have := Complex.norm_le_abs_re_add_abs_im (z - (LpW a : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero] at this
      rw [abs_of_pos (by linarith : 0 < z.re - LpW a), abs_of_pos hz] at this
      linarith
    by_cases hκc : cs / 2 ≤ κ
    · obtain ⟨f, hf, hfm, hfc, hfb⟩ := hcont N hNc a ha hSB z.re hE
      set r := c * min (z.re - LpW a) 1 with hr
      have hr0 : c * m₀ ≤ r := mul_le_mul_of_nonneg_left (min_le_min hκc le_rfl) hc.le
      have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr0
      have hzE : ‖z - (z.re : ℂ)‖ = z.im := by
        have e : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hz]
      have hbound : (mW a z).im ≤ (4 * Kc + 2) / (c * m₀) * z.im := by
        by_cases hsmall : z.im < 3 * r / 4
        · have hEb : (z.re : ℂ) ∈ Metric.ball (z.re : ℂ) (3 * r / 4) :=
            Metric.mem_ball_self (by positivity)
          have hzb : z ∈ Metric.ball (z.re : ℂ) (3 * r / 4) := by
            rw [mem_ball_iff_norm, hzE]; exact hsmall
          have hlip := aux_lip hrpos hf hfb hEb hzb
          have hzr : z ∈ Metric.ball (z.re : ℂ) r := by
            rw [mem_ball_iff_norm, hzE]; linarith
          have hEr : (z.re : ℂ) ∈ Metric.ball (z.re : ℂ) r := Metric.mem_ball_self hrpos
          have hfz : f z = mW a z := hfm z hzr hz
          have hfE : (f (z.re : ℂ)).im = 0 := by
            have h := hfc _ hEr
            rw [Complex.conj_ofReal] at h
            have := congrArg Complex.im h
            simp only [Complex.conj_im] at this
            linarith
          rw [hzE] at hlip
          have him : (mW a z).im ≤ ‖f z - f (z.re : ℂ)‖ := by
            have := Complex.im_le_norm (f z - f (z.re : ℂ))
            rw [Complex.sub_im, hfE, sub_zero] at this
            rw [← hfz]
            exact this
          have h4 : 4 * Kc / r * z.im ≤ 4 * Kc / (c * m₀) * z.im := by
            gcongr
          have h5 : 4 * Kc / (c * m₀) * z.im ≤ (4 * Kc + 2) / (c * m₀) * z.im := by
            gcongr; linarith
          linarith
        · push Not at hsmall
          have h1 : 1 ≤ 2 / (c * m₀) * z.im := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
            linarith
          have h5 : 2 / (c * m₀) * z.im ≤ (4 * Kc + 2) / (c * m₀) * z.im := by
            gcongr; linarith
          linarith
      calc (mW a z).im * min √κ 1 ≤ (mW a z).im := hle_im
        _ ≤ (4 * Kc + 2) / (c * m₀) * z.im := hbound
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hη
    · push Not at hκc
      have h1 : 1 ≤ 2 / cs * z.im := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcs]
        linarith
      calc (mW a z).im * min √κ 1 ≤ (mW a z).im := hle_im
        _ ≤ 2 / cs * z.im := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hη

/-- Outside `[L₋, L₊]`: `Im m^W(z) · min(√κ(E), 1) ≤ K η` (the left side by reflection). -/
private theorem aux_im_out {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) →
      ∀ z : ℂ, 0 < z.im → 0 < kappaW a z.re →
        (mW a z).im * min √(kappaW a z.re) 1 ≤ K * z.im := by
  obtain ⟨K, hK, N₀, h⟩ := aux_im_right hτ
  refine ⟨K, hK, max N₀ 1, fun N hN a ha hSB z hz hκ => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N ≥ N₀ := le_of_max_le_left hN
  unfold kappaW at hκ ⊢
  rcases max_choice (max (z.re - LpW a) (LmW a - z.re)) 0 with h0 | h0
  swap
  · rw [h0] at hκ; exact absurd hκ (lt_irrefl 0)
  rw [h0] at hκ ⊢
  rcases max_choice (z.re - LpW a) (LmW a - z.re) with h1 | h1
  · rw [h1] at hκ ⊢
    exact h N hN0 a ha hSB z hz (by linarith)
  · rw [h1] at hκ ⊢
    have ha' : ∀ i, |(-a) i| ≤ τ⁻¹ - 2 := fun i => by simpa using ha i
    have hL : LmW a - z.re = (⟨-z.re, z.im⟩ : ℂ).re - LpW (-a) := by
      rw [LmW_neg]; simp only; ring
    have := h N hN0 (-a) ha' (aux_sb_neg hN1 hSB) ⟨-z.re, z.im⟩ hz
      (by rw [hL] at hκ; linarith)
    rw [← hL, aux_im_neg hN1 a hz] at this
    simpa only [Complex.eta] using this

/-- `κ ≤ T min(√κ, 1)` for `0 ≤ κ ≤ T` and `1 ≤ T`. -/
private theorem aux_kappa_min {κ T : ℝ} (hκ : 0 ≤ κ) (hκT : κ ≤ T) (hT : 1 ≤ T) :
    κ ≤ T * min √κ 1 := by
  rcases le_total κ 1 with h | h
  · have hs1 : √κ ≤ 1 := Real.sqrt_le_one.mpr h
    rw [min_eq_left hs1]
    have hss : √κ * √κ = κ := Real.mul_self_sqrt hκ
    have hs0 := Real.sqrt_nonneg κ
    nlinarith
  · have hs1 : 1 ≤ √κ := Real.one_le_sqrt.mpr h
    rw [min_eq_right hs1, mul_one]
    exact hκT

/-- `ξ ≺ ζ'` at `(ε₁, D)` and `N^{ε₁} ζ' ≤ N^ε ζ` give `ξ ≺ ζ` at `(ε, D)`. -/
private theorem aux_dom_scale {Ω : Type} [MeasureSpace Ω] {N : ℕ} {ε₁ ε D : ℝ} {ξ ζ' ζ : Ω → ℝ}
    (h : DomAt N ε₁ D ξ ζ') (hle : ∀ ω, (N : ℝ) ^ ε₁ * ζ' ω ≤ (N : ℝ) ^ ε * ζ ω) :
    DomAt N ε D ξ ζ := by
  unfold DomAt at *
  refine le_trans (measure_mono ?_) h
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith [hle ω]

/-- `Ψ^W ≥ 0` for `Im z > 0`. -/
private theorem aux_psi_nonneg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ PsiW a z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold PsiW
  exact add_nonneg (Real.sqrt_nonneg _) (by positivity)

/-- `Ψ^W ≤ N^{−7/24}` at `z` when `N = q²⁴`, `η, κ(E) ≥ N^{−2/3}`, `Im m^W · min(√κ, 1) ≤ K η` and
`√K + 1 ≤ q`. -/
private theorem aux_psi_bound {N : ℕ} (hN1 : 1 ≤ N) {a : Fin N → ℝ} {K q : ℝ} (hq1 : 1 ≤ q)
    (hNq : (N : ℝ) = q ^ 24) (hqK : √K + 1 ≤ q) {z : ℂ} (hη : (q ^ 16)⁻¹ ≤ z.im)
    (hκ : (q ^ 16)⁻¹ ≤ kappaW a z.re)
    (hI : (mW a z).im * min √(kappaW a z.re) 1 ≤ K * z.im) : PsiW a z ≤ (q ^ 7)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hq0 : 0 < q := by linarith
  have hq16 : 0 < (q ^ 16)⁻¹ := by positivity
  have hη0 : 0 < z.im := lt_of_lt_of_le hq16 hη
  obtain ⟨hmpos, -⟩ := mW_spec hN1 a hη0
  have hsq8 : (q ^ 8)⁻¹ ≤ min √(kappaW a z.re) 1 := by
    refine le_min ?_ (inv_le_one_of_one_le₀ (one_le_pow₀ hq1))
    have : √((q ^ 16)⁻¹) = (q ^ 8)⁻¹ := by
      rw [show (q ^ 16)⁻¹ = ((q ^ 8)⁻¹) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [← this]; exact Real.sqrt_le_sqrt hκ
  have hq8 : 0 < q ^ 8 := by positivity
  have hIm8 : (mW a z).im ≤ K * z.im * q ^ 8 := by
    have h1 : (mW a z).im * (q ^ 8)⁻¹ ≤ K * z.im :=
      (mul_le_mul_of_nonneg_left hsq8 hmpos.le).trans hI
    rw [mul_inv_le_iff₀ hq8] at h1
    linarith
  have hNη : q ^ 8 ≤ N * z.im := by
    have := mul_le_mul_of_nonneg_left hη hNpos.le
    rw [hNq] at this ⊢
    calc q ^ 8 = q ^ 24 * (q ^ 16)⁻¹ := by field_simp
      _ ≤ _ := this
  have hNη0 : 0 < (N : ℝ) * z.im := by positivity
  have hx : (mW a z).im / (N * z.im) ≤ K / q ^ 16 := by
    rw [div_le_div_iff₀ hNη0 (by positivity)]
    have : (mW a z).im * q ^ 16 ≤ K * z.im * q ^ 8 * q ^ 16 :=
      mul_le_mul_of_nonneg_right hIm8 (by positivity)
    calc (mW a z).im * q ^ 16 ≤ K * z.im * q ^ 8 * q ^ 16 := this
      _ = K * (q ^ 24 * z.im) := by ring
      _ = K * (N * z.im) := by rw [hNq]
  have hsx : √((mW a z).im / (N * z.im)) ≤ √K / q ^ 8 := by
    calc √((mW a z).im / (N * z.im)) ≤ √(K / q ^ 16) := Real.sqrt_le_sqrt hx
      _ = √K / q ^ 8 := by
        rw [Real.sqrt_div' K (by positivity : (0 : ℝ) ≤ q ^ 16),
          show q ^ 16 = (q ^ 8) ^ 2 by ring, Real.sqrt_sq hq8.le]
  have hy : 1 / (N * z.im) ≤ 1 / q ^ 8 := one_div_le_one_div_of_le hq8 hNη
  unfold PsiW
  calc √((mW a z).im / (N * z.im)) + 1 / (N * z.im) ≤ √K / q ^ 8 + 1 / q ^ 8 :=
        add_le_add hsx hy
    _ = (√K + 1) / q ^ 8 := by ring
    _ ≤ q / q ^ 8 := by gcongr
    _ = (q ^ 7)⁻¹ := by field_simp

/-- On `𝐒_τ`: `s (Nη)⁻¹ + Ψ^W(z)² + c (Nη)⁻¹ ≤ (4 + 2KT) s (Nη)⁻¹` when `N = q²⁴`,
`N^{−1/3} ≤ s`, `c ≤ s`, `η ≥ N^{−2/3}`, `0 < κ(E) ≤ T`, `η ≤ s κ(E)` and
`Im m^W · min(√κ, 1) ≤ K η`. -/
private theorem aux_out_bound {N : ℕ} (hN1 : 1 ≤ N) {a : Fin N → ℝ} {K q s T c : ℝ}
    (hK : 0 ≤ K) (hq1 : 1 ≤ q) (hNq : (N : ℝ) = q ^ 24) (hs8 : (q ^ 8)⁻¹ ≤ s) (hcs : c ≤ s)
    (hT : 1 ≤ T) {z : ℂ} (hη : (q ^ 16)⁻¹ ≤ z.im) (hκ0 : 0 < kappaW a z.re)
    (hκT : kappaW a z.re ≤ T) (hηκ : z.im ≤ s * kappaW a z.re)
    (hI : (mW a z).im * min √(kappaW a z.re) 1 ≤ K * z.im) :
    s / (N * z.im) + PsiW a z ^ 2 + c / (N * z.im) ≤ (4 + 2 * K * T) * (s / (N * z.im)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hq0 : 0 < q := by linarith
  have hq16 : 0 < (q ^ 16)⁻¹ := by positivity
  have hη0 : 0 < z.im := lt_of_lt_of_le hq16 hη
  have hNη0 : 0 < (N : ℝ) * z.im := by positivity
  set Y : ℝ := 1 / (N * z.im) with hY
  have hY0 : 0 < Y := by positivity
  have hsY : ∀ t : ℝ, t / (N * z.im) = t * Y := fun t => by rw [hY]; ring
  have hNη : q ^ 8 ≤ N * z.im := by
    have := mul_le_mul_of_nonneg_left hη hNpos.le
    rw [hNq] at this ⊢
    calc q ^ 8 = q ^ 24 * (q ^ 16)⁻¹ := by field_simp
      _ ≤ _ := this
  have hYs : Y ≤ s := by
    calc Y ≤ 1 / q ^ 8 := one_div_le_one_div_of_le (by positivity) hNη
      _ = (q ^ 8)⁻¹ := one_div _
      _ ≤ s := hs8
  obtain ⟨hmpos, -⟩ := mW_spec hN1 a hη0
  have hmin0 : 0 < min √(kappaW a z.re) 1 := lt_min (Real.sqrt_pos.2 hκ0) one_pos
  have hkm := aux_kappa_min hκ0.le hκT hT
  have hs0 : 0 ≤ s := le_trans (by positivity) hs8
  have hImS : (mW a z).im ≤ K * T * s := by
    have h1 : (mW a z).im * min √(kappaW a z.re) 1 ≤ (K * T * s) * min √(kappaW a z.re) 1 := by
      calc (mW a z).im * min √(kappaW a z.re) 1 ≤ K * z.im := hI
        _ ≤ K * (s * kappaW a z.re) := mul_le_mul_of_nonneg_left hηκ hK
        _ ≤ K * (s * (T * min √(kappaW a z.re) 1)) := by gcongr
        _ = (K * T * s) * min √(kappaW a z.re) 1 := by ring
    exact le_of_mul_le_mul_right h1 hmin0
  have hx0 : 0 ≤ (mW a z).im / (N * z.im) := div_nonneg hmpos.le hNη0.le
  have hx : (mW a z).im / (N * z.im) ≤ K * T * s * Y := by
    rw [hsY]; exact mul_le_mul_of_nonneg_right hImS hY0.le
  have hYY : Y * Y ≤ s * Y := mul_le_mul_of_nonneg_right hYs hY0.le
  have hPsi2 : PsiW a z ^ 2 ≤ 2 * (K * T * s * Y) + 2 * (s * Y) := by
    have hP : PsiW a z = √((mW a z).im / (N * z.im)) + Y := rfl
    rw [hP]
    have hsq : √((mW a z).im / (N * z.im)) ^ 2 = (mW a z).im / (N * z.im) := Real.sq_sqrt hx0
    have h1 : (√((mW a z).im / (N * z.im)) + Y) ^ 2 ≤
        2 * √((mW a z).im / (N * z.im)) ^ 2 + 2 * (Y * Y) := by
      nlinarith [sq_nonneg (√((mW a z).im / (N * z.im)) - Y)]
    rw [hsq] at h1
    linarith
  have hc : c * Y ≤ s * Y := mul_le_mul_of_nonneg_right hcs hY0.le
  rw [hsY s, hsY c]
  linarith

/-- The strong averaged bound on `𝐒_τ` (§12.4): from the entrywise and averaged laws for
`(W^Gauss, D, 𝐃^W(τ, N))` and the rigid extremes of `W^Gauss + D`,
`N⁻¹ tr G − m^W = O_≺(N^{−τ_S/2}(Nη)⁻¹)` on `𝐒_τ`, for every `W` of the class. -/
theorem wig_avg_outside (τ τS : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hττS : τ ≤ τS / 4)
    (hτS1 : τS ≤ 1 / 24) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τS⁻¹ → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      AveragedPhiLawWAt N ε D A W (outDomW τS (specOf A))
        (fun z => (N : ℝ) ^ (-τS / 2) / (N * z.im)) := by
  have hτS : 0 < τS := by linarith
  have hτinv : 4 * τS⁻¹ ≤ τ⁻¹ := by
    have h := inv_anti₀ hτ hττS
    rw [inv_div] at h
    rw [div_eq_mul_inv] at h
    linarith
  have hτS24 : 24 ≤ τS⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτS]; linarith
  obtain ⟨ε₁', D₁', hε₁', N₁, hG⟩ :=
    general_wig_avg_phi τ (1 / 24) C (ε / 2) D hτ (by norm_num) (half_pos hε)
  obtain ⟨ε₁'', D₁'', hε₁'', N₂, hO⟩ :=
    avg_law_outside τ τS ε₁' D₁' hτ hττS (by linarith) hε₁'
  obtain ⟨K, hK, N₃, hIm⟩ := aux_im_out hτ
  obtain ⟨N₄, hLb⟩ := aux_LpW_bounds hτ
  have hev : ∀ᶠ N : ℕ in atTop, (N₁ ≤ N ∧ N₂ ≤ N ∧ N₃ ≤ N ∧ N₄ ≤ N ∧ 1 ≤ N) ∧
      √K + 1 ≤ (N : ℝ) ^ (1 / 24 : ℝ) ∧ 4 + 2 * K * τS⁻¹ ≤ (N : ℝ) ^ (ε / 2) := by
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₂, eventually_ge_atTop N₃,
      eventually_ge_atTop N₄, eventually_ge_atTop 1,
      aux_ev_rpow (by norm_num : (0 : ℝ) < 1 / 24) (√K + 1),
      aux_ev_rpow (half_pos hε) (4 + 2 * K * τS⁻¹)] with N h1 h2 h3 h4 h5 h6 h7
    exact ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨min ε₁' ε₁'', max D₁' D₁'', lt_min hε₁' hε₁'', N₀, ?_⟩
  intro N hN Ω _ _ A W hA hAn hW hSB hEnt hAvg hRig
  obtain ⟨⟨hN1', hN2', hN3', hN4', hN1⟩, hqK, hεN⟩ := hN₀ N hN
  set a := specOf A with ha_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- the spectrum and the edges
  have habs : ∀ i, |a i| ≤ τS⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hAn
  have ha2 : ∀ i, |a i| ≤ τ⁻¹ - 2 := fun i => by linarith [habs i]
  have ha2' : ∀ i, |(-a) i| ≤ τ⁻¹ - 2 := fun i => by simpa using ha2 i
  have hp := hLb N hN4' a ha2 hSB τS⁻¹ habs
  have hp' := hLb N hN4' (-a) ha2' (aux_sb_neg hN1 hSB) τS⁻¹ (fun i => by simpa using habs i)
  have hm : -(τS⁻¹ + 2) ≤ LmW a ∧ LmW a ≤ τS⁻¹ := by
    rw [LmW_neg]; constructor <;> linarith [hp'.1, hp'.2]
  -- powers of `N`
  set q : ℝ := (N : ℝ) ^ (1 / 24 : ℝ) with hq
  set s : ℝ := (N : ℝ) ^ (-τS / 2) with hs
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1R (by norm_num)
  have hq0 : 0 < q := by linarith
  have hpow : ∀ k : ℕ, (N : ℝ) ^ (1 / 24 * (k : ℝ)) = q ^ k := fun k =>
    Real.rpow_mul_natCast hNpos.le _ k
  have hNq : (N : ℝ) = q ^ 24 := by
    rw [← hpow 24]; norm_num
  have he : (N : ℝ) ^ (-2 / 3 : ℝ) = (q ^ 16)⁻¹ := by
    rw [← hpow 16, ← Real.rpow_neg hNpos.le]; norm_num
  have he3 : (N : ℝ) ^ (-1 / 3 : ℝ) = (q ^ 8)⁻¹ := by
    rw [← hpow 8, ← Real.rpow_neg hNpos.le]; norm_num
  have he7 : (N : ℝ) ^ (-1 / 4 - 1 / 24 : ℝ) = (q ^ 7)⁻¹ := by
    rw [← hpow 7, ← Real.rpow_neg hNpos.le]; norm_num
  have hs0 : 0 < s := Real.rpow_pos_of_pos hNpos _
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
  have hs2 : (N : ℝ) ^ (-2 / 3 + τS) * (N : ℝ) ^ (-τS) = (q ^ 16)⁻¹ := by
    rw [← Real.rpow_add hNpos, ← he]; ring_nf
  have hsS : (N : ℝ) ^ (-τS) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; ring_nf
  have hκe : (q ^ 16)⁻¹ ≤ (N : ℝ) ^ (-2 / 3 + τS) := by
    rw [← he]; exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  have hτe : (N : ℝ) ^ (-1 + τ) ≤ (q ^ 16)⁻¹ := by
    rw [← he]; exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  have hs8 : (q ^ 8)⁻¹ ≤ s := by
    rw [← he3]; exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  have hs48 : (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) ≤ s :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  have hNε : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hq8 : q ^ 8 * (q ^ 16)⁻¹ * (N : ℝ) = q ^ 16 := by
    rw [hNq]; field_simp
  -- the domain `𝐒_τ` and its upward hull `Ŝ`
  have hlowη : ∀ z ∈ outDomW τS a, (q ^ 16)⁻¹ ≤ z.im ∧ (q ^ 16)⁻¹ ≤ kappaW a z.re := by
    intro z hz
    obtain ⟨h1, -, h3, -⟩ := hz
    refine ⟨?_, hκe.trans h1⟩
    have hsS0 : 0 ≤ (N : ℝ) ^ (-τS) := Real.rpow_nonneg hNpos.le _
    calc (q ^ 16)⁻¹ = (N : ℝ) ^ (-2 / 3 + τS) * (N : ℝ) ^ (-τS) := hs2.symm
      _ ≤ kappaW a z.re * (N : ℝ) ^ (-τS) := mul_le_mul_of_nonneg_right h1 hsS0
      _ = (N : ℝ) ^ (-τS) * kappaW a z.re := mul_comm _ _
      _ ≤ z.im := h3
  have hSd : ∀ z ∈ outDomW τS a, z ∈ domW τ N := by
    intro z hz
    obtain ⟨hη0, hκ0⟩ := hlowη z hz
    have hq16 : 0 < (q ^ 16)⁻¹ := by positivity
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hκpos : 0 < kappaW a z.re := lt_of_lt_of_le hq16 hκ0
    have hE := aux_E_bound hκpos h2 hp hm
    have hηκ : z.im ≤ kappaW a z.re := by
      calc z.im ≤ s * kappaW a z.re := h4
        _ ≤ 1 * kappaW a z.re := mul_le_mul_of_nonneg_right hs1 hκpos.le
        _ = kappaW a z.re := one_mul _
    refine ⟨by linarith, by linarith, hτe.trans hη0, by linarith⟩
  set Sh : Set ℂ := {z | z ∈ domW τ N ∧ ∃ w ∈ outDomW τS a, w.re = z.re ∧ w.im ≤ z.im}
    with hSh
  have hSpec : SpectralDomainW τ N Sh := by
    refine ⟨fun z hz => hz.1, fun z hz w hw hre him => ⟨hw, ?_⟩⟩
    obtain ⟨u, hu, h1, h2⟩ := hz.2
    exact ⟨u, hu, h1.trans hre.symm, h2.trans him⟩
  have hsub : outDomW τS a ⊆ Sh := fun z hz => ⟨hSd z hz, z, hz, rfl, le_rfl⟩
  have hShlow : ∀ z ∈ Sh, (q ^ 16)⁻¹ ≤ z.im ∧ (q ^ 16)⁻¹ ≤ kappaW a z.re := by
    intro z hz
    obtain ⟨w, hw, h1, h2⟩ := hz.2
    obtain ⟨hw1, hw2⟩ := hlowη w hw
    exact ⟨hw1.trans h2, h1 ▸ hw2⟩
  -- `Ψ^W ≤ N^{−1/4−1/24}` on `Ŝ`
  have hPsi : PsiSmallW (1 / 24) a Sh := by
    intro z hz
    obtain ⟨hη, hκ⟩ := hShlow z hz
    have hq16 : 0 < (q ^ 16)⁻¹ := by positivity
    have hI := hIm N hN3' a ha2 hSB z (lt_of_lt_of_le hq16 hη) (lt_of_lt_of_le hq16 hκ)
    show PsiW a z ≤ (N : ℝ) ^ (-1 / 4 - 1 / 24 : ℝ)
    rw [he7]
    exact aux_psi_bound hN1 hq1 hNq hqK hη hκ hI
  -- the control `Φ` on `Ŝ`
  set Φ : ℂ → ℝ := fun z => if z ∈ outDomW τS a then s / (N * z.im) else 1 / (N * z.im)
    with hΦ
  have hΦb : ∀ z ∈ Sh, 0 ≤ Φ z ∧ Φ z ≤ 1 / (N * z.im) := by
    intro z hz
    have hη0 : 0 < z.im := (hz.1).1
    have hNη0 : 0 < (N : ℝ) * z.im := by positivity
    simp only [hΦ]
    split_ifs
    · exact ⟨by positivity, div_le_div_of_nonneg_right hs1 hNη0.le⟩
    · exact ⟨by positivity, le_rfl⟩
  -- the Gaussian matrix `W^Gauss + D`
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal a
  have hDH : (diagonal a).IsHermitian := isHermitian_diagonal a
  have hDn : ‖diagonal a‖ ≤ τS⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]; exact habs i
  have hsymm : ∀ ω, (goeW N ω)ᵀ = goeW N ω := by
    intro ω; ext i j; simp [goeW, min_comm, max_comm]
  have hSB' : StandingBoundW τ (specOf (diagonal a)) (domW τ N) := by
    intro z hz i
    rw [he, mW_comp_perm]
    exact hSB z hz (e i)
  have hAvg'' : AveragedLawWAt N ε₁'' D₁'' (diagonal a) (goeW N) (domW τ N) := fun z hz =>
    (hAvg z hz).mono hN1 (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => by have := (hz.1); positivity) (min_le_right _ _) (le_max_right _ _)
  have hRig'' : RigidExtremesWAt N ε₁'' D₁'' (specOf (diagonal a))
      (fun ω => goeW N ω + diagonal a) := by
    unfold RigidExtremesWAt at hRig ⊢
    rw [he, LpW_comp_perm, LmW_comp_perm]
    have h0 : ∀ _ω : GOESpace N, (0 : ℝ) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) := fun _ =>
      Real.rpow_nonneg hNpos.le _
    exact ⟨hRig.1.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) h0 (min_le_right _ _)
      (le_max_right _ _), hRig.2.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) h0
      (min_le_right _ _) (le_max_right _ _)⟩
  have hOut := hO N hN2' (diagonal a) (goeW N) hDH hDn hsymm hSB' hAvg'' hRig''
  have houtEq : outDomW τS (specOf (diagonal a)) = outDomW τS a := by
    rw [he]; simp only [outDomW, kappaW, LpW_comp_perm, LmW_comp_perm]
  rw [houtEq] at hOut
  have hEnt' : EntrywiseLawWAt N ε₁' D₁' (diagonal a) (goeW N) Sh := fun z hz i j =>
    (hEnt z hz.1 i j).mono hN1 (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => aux_psi_nonneg hN1 _ (hz.1).1) (min_le_left _ _) (le_max_left _ _)
  have hPhi' : AveragedPhiLawWAt N ε₁' D₁' (diagonal a) (goeW N) Sh Φ := by
    intro z hz
    by_cases hzS : z ∈ outDomW τS a
    · have := hOut z hzS
      simp only [hΦ, hzS, ↓reduceIte]
      exact this
    · simp only [hΦ, hzS, ↓reduceIte]
      exact (hAvg z hz.1).mono hN1 (fun _ => le_rfl) (fun _ => le_rfl)
        (fun _ => by have := (hz.1).1; positivity) (min_le_left _ _) (le_max_left _ _)
  have hAτ : ‖A‖ ≤ τ⁻¹ := hAn.trans (by linarith)
  have hGout := hG N hN1' A W Sh Φ hA hAτ hW hSpec (fun z hz i => hSB z hz.1 i) (Or.inr hPsi)
    hΦb hEnt' hPhi'
  -- the final bound on `𝐒_τ`
  intro z hz
  have h := hGout z (hsub hz)
  obtain ⟨hη, hκ⟩ := hlowη z hz
  have hq16 : 0 < (q ^ 16)⁻¹ := by positivity
  have hη0 : 0 < z.im := lt_of_lt_of_le hq16 hη
  have hκ0 : 0 < kappaW a z.re := lt_of_lt_of_le hq16 hκ
  have hI := hIm N hN3' a ha2 hSB z hη0 hκ0
  have hsum := aux_out_bound hN1 hK.le hq1 hNq hs8 hs48 (by linarith) hη hκ0 hz.2.1 hz.2.2.2 hI
  have hΦz : Φ z = s / (N * z.im) := by
    simp only [hΦ, hz, ↓reduceIte]
  have hsum' : Φ z + PsiW a z ^ 2 + (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) / (N * z.im) ≤
      (4 + 2 * K * τS⁻¹) * (s / (N * z.im)) := by
    rw [hΦz]; exact hsum
  have hNη0 : 0 < (N : ℝ) * z.im := by positivity
  have hsY0 : 0 ≤ s / (N * z.im) := by positivity
  apply aux_dom_scale h
  intro _
  have hNε2 : 0 ≤ (N : ℝ) ^ (ε / 2) := by positivity
  calc (N : ℝ) ^ (ε / 2) * (Φ z + PsiW a z ^ 2 + (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) / (N * z.im))
      ≤ (N : ℝ) ^ (ε / 2) * ((4 + 2 * K * τS⁻¹) * (s / (N * z.im))) :=
        mul_le_mul_of_nonneg_left hsum' hNε2
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * (s / (N * z.im))) := by gcongr
    _ = (N : ℝ) ^ ε * (s / (N * z.im)) := by rw [← hNε]; ring

#print axioms wig_avg_outside

end Anisotropic
