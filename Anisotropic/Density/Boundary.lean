import Anisotropic.Density.SelfConsistent

/-!
# Boundary values of `m` on `ℝ ∖ {0}`

The boundary values `m(E) = lim_{z → E, z ∈ ℂ₊} m(z)` for real `E ≠ 0`, used in the proofs of
Lemmas 2.5 and 2.6 (Appendix A). For real `E ≠ 0`:
* the limit exists, and `m` extends continuously to `ℂ₊ ∪ (ℝ ∖ {0})`;
* `m(E)` is a root of `P_E` with `Im m(E) ≥ 0`, and `Im m(E) = 0` for `E < 0`;
* sign lemmas: for real `x` off `0` and off the poles `-1/σ_i`, with `f(x) ≠ 0`, `f'(x) > 0` gives
  `m(f(x)) = x`, and `f'(x) < 0` gives `m(f(x)) ≠ x`.

Existence of the limit: `P_E(m(z)) = (z - E) m(z) Π_s (1 + s m(z)) → 0` with `m` bounded, so
`m(z)` approaches the finite root set of `P_E ≠ 0`; the image under `m` of `B_r(E) ∩ ℂ₊` is
connected, so it stays near a single root. `Im m(E) = 0` for `E < 0`: for `w ∈ ℂ₊` with
`Im f(w) = 0`, `Re f(w) = N⁻¹ Σ_i σ_i |1 + σ_i w|⁻² ≥ 0`. Sign lemmas: the local inverse `h`
of `f` at `x` satisfies `Im h(E + iη) = η / f'(x) + o(η)`, and `Im h` does not vanish on
`B_r(E) ∩ ℂ₊`, since `f` maps real points to real points.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Boundary values of `m` -/

/-- `m` on `ℂ₊`, and its limit from `ℂ₊` elsewhere. -/
def mExt (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then mFun N σ z else limUnder (𝓝[upperHalf] z) (mFun N σ)

private lemma bd_convex_upperHalf : Convex ℝ upperHalf :=
  convex_halfSpace_im_gt 0

private lemma bd_ne_zero {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  rintro rfl
  simp at hw

private lemma bd_one_add_ne_zero {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : 0 < w.im) :
    1 + (s : ℂ) * w ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 : ((1 : ℂ) + (s : ℂ) * w).im = s * w.im := by simp
  rw [h2, Complex.zero_im] at h1
  exact (mul_pos hs hw).ne' h1

private lemma bd_mExt_ofReal (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) :
    mExt N σ E = limUnder (𝓝[upperHalf] (E : ℂ)) (mFun N σ) := by
  simp [mExt]

/-- Real points lie in the closure of `ℂ₊`. -/
private lemma bd_neBot (E : ℝ) : (𝓝[upperHalf] (E : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
  simp

/-- `P_E(w) = P_z(w) + (z - E) w Π_s (1 + s w)`. -/
private lemma bd_eval_sub (N : ℕ) (σ : Fin M → ℝ) (z E w : ℂ) :
    (scPoly N σ E).eval w =
      (scPoly N σ z).eval w + (z - E) * (w * ∏ s ∈ posVals σ, (1 + (s : ℂ) * w)) := by
  simp only [scPoly, eval_sub, eval_add, eval_neg, eval_mul, eval_X, eval_C, eval_prod,
    eval_one, eval_finsetSum]
  ring

/-- `P_E(m(z)) = (z - E) m(z) Π_s (1 + s m(z))` on `ℂ₊`. -/
private lemma bd_eval_mFun (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (E : ℂ) {z : ℂ}
    (hz : 0 < z.im) :
    (scPoly N σ E).eval (mFun N σ z) =
      (z - E) * (mFun N σ z * ∏ s ∈ posVals σ, (1 + (s : ℂ) * mFun N σ z)) := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  have h0 : (scPoly N σ z).eval (mFun N σ z) = 0 := by
    rw [scPoly_eval N σ hσ z (bd_ne_zero hm)
      (fun s hs => bd_one_add_ne_zero (Finset.mem_filter.mp hs).2 hm), hfm, sub_self, mul_zero]
  rw [bd_eval_sub N σ z E, h0, zero_add]

/-- `P_E(m(z)) → 0` as `z → E` in `ℂ₊`, for real `E ≠ 0`. -/
private lemma bd_tendsto_eval (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) :
    Tendsto (fun z => (scPoly N σ E).eval (mFun N σ z)) (𝓝[upperHalf] (E : ℂ)) (𝓝 0) := by
  set K : ℝ := 1 + √(massRatio N σ)
  have hK : 0 ≤ K := by positivity
  have hE0 : 0 < |E| := abs_pos.mpr hE
  set q : ℂ → ℂ := fun w => w * ∏ s ∈ posVals σ, (1 + (s : ℂ) * w)
  have hq : Continuous q := by fun_prop
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (2 * K / |E|)).exists_bound_of_continuousOn
    hq.continuousOn
  have hbound : ∀ᶠ z in 𝓝[upperHalf] (E : ℂ),
      ‖(scPoly N σ E).eval (mFun N σ z)‖ ≤ ‖z - E‖ * C := by
    filter_upwards [inter_mem_nhdsWithin upperHalf (Metric.ball_mem_nhds (E : ℂ)
      (half_pos hE0))] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    change 0 < z.im at hz1
    rw [Metric.mem_ball, dist_eq_norm] at hz2
    have hzn : |E| / 2 ≤ ‖z‖ := by
      have h1 : ‖(E : ℂ)‖ ≤ ‖z‖ + ‖z - E‖ := by
        have := norm_sub_le z (z - E)
        rw [sub_sub_cancel] at this
        linarith [norm_sub_rev z (E : ℂ)]
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
    have hm : ‖mFun N σ z‖ ≤ 2 * K / |E| := by
      refine (norm_mFun_le N σ hσ hz1).trans ?_
      rw [div_le_div_iff₀ (lt_of_lt_of_le (half_pos hE0) hzn) hE0]
      nlinarith
    rw [bd_eval_mFun N σ hσ E hz1, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ (mem_closedBall_zero_iff.mpr hm)) (norm_nonneg _)
  refine squeeze_zero_norm' hbound ?_
  have hc : Continuous fun z : ℂ => ‖z - E‖ * C := by fun_prop
  have := (hc.tendsto (E : ℂ)).mono_left (nhdsWithin_le_nhds (s := upperHalf))
  simpa using this

/-- A point where a nonzero polynomial is small lies near one of its roots. -/
private lemma bd_exists_root_near {P : ℂ[X]} {ε : ℝ} (hε : 0 < ε) {w : ℂ}
    (h : ‖P.eval w‖ < ‖P.leadingCoeff‖ * ε ^ Multiset.card P.roots) :
    ∃ ρ ∈ P.roots, dist w ρ < ε := by
  by_contra hc
  push Not at hc
  have hsplit : P.Splits := IsAlgClosed.splits P
  rw [hsplit.eval_eq_prod_roots, norm_mul, Multiset.norm_prod, Multiset.map_map] at h
  have hle := Multiset.prod_map_le_prod_map₀ (s := P.roots) (fun _ => ε)
    (norm ∘ fun ρ => w - ρ) (fun _ _ => hε.le) (fun ρ hρ => by
      simpa [dist_eq_norm] using hc ρ hρ)
  rw [Multiset.map_const', Multiset.prod_replicate] at hle
  have := mul_le_mul_of_nonneg_left hle (norm_nonneg P.leadingCoeff)
  linarith

/-- For real `E ≠ 0`, `m(z)` approaches the roots of `P_E` as `z → E` in `ℂ₊`. -/
private lemma bd_near_roots (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : E ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[upperHalf] (E : ℂ), ∃ ρ ∈ (scPoly N σ E).roots, dist (mFun N σ z) ρ < ε := by
  have hP : scPoly N σ E ≠ 0 := by
    intro h
    have := scPoly_eval_zero N σ E
    rw [h, eval_zero] at this
    norm_num at this
  have hlead : 0 < ‖(scPoly N σ E).leadingCoeff‖ :=
    norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP)
  have hpos : 0 < ‖(scPoly N σ E).leadingCoeff‖ * ε ^ Multiset.card (scPoly N σ E).roots := by
    positivity
  filter_upwards [(bd_tendsto_eval N σ hσ hE).norm.eventually (gt_mem_nhds (by simpa using hpos))]
    with z hz
  exact bd_exists_root_near hε hz

/-- A finite subset of `ℂ` has a positive separation. -/
private lemma bd_exists_sep (S : Finset ℂ) :
    ∃ δ > 0, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * δ < dist a b := by
  have h : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ p ∈ S ×ˢ S, p.1 ≠ p.2 → 2 * δ < dist p.1 p.2 := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hd : 2 * (0 : ℝ) < dist p.1 p.2 := by simpa using dist_pos.mpr hp
      have hc : Continuous fun δ : ℝ => 2 * δ := by fun_prop
      exact ((hc.tendsto 0).eventually (gt_mem_nhds hd)).mono fun _ h _ => h
  obtain ⟨δ, hδ, hδpos⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  exact ⟨δ, hδpos, fun a ha b hb hab => hδ (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩) hab⟩

/-- For real `E ≠ 0`, `m(z)` converges as `z → E` in `ℂ₊`. -/
private lemma bd_exists_tendsto (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) : ∃ ρ, Tendsto (mFun N σ) (𝓝[upperHalf] (E : ℂ)) (𝓝 ρ) := by
  set S : Finset ℂ := (scPoly N σ E).roots.toFinset
  have hnear : ∀ ε > 0, ∀ᶠ z in 𝓝[upperHalf] (E : ℂ), ∃ ρ ∈ S, dist (mFun N σ z) ρ < ε := by
    intro ε hε
    filter_upwards [bd_near_roots N σ hσ hE hε] with z ⟨ρ, hρ, hd⟩
    exact ⟨ρ, Multiset.mem_toFinset.mpr hρ, hd⟩
  obtain ⟨δ, hδ, hsep⟩ := bd_exists_sep S
  obtain ⟨r, hr, hW⟩ := Metric.mem_nhdsWithin_iff.mp (hnear δ hδ)
  set W : Set ℂ := Metric.ball (E : ℂ) r ∩ upperHalf
  have hz₀ : (E : ℂ) + (r / 2 : ℝ) * Complex.I ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · have h1 : ((E : ℂ) + (r / 2 : ℝ) * Complex.I).im = r / 2 := by simp
      change 0 < ((E : ℂ) + (r / 2 : ℝ) * Complex.I).im
      rw [h1]
      positivity
  obtain ⟨ρ₀, hρ₀, hd₀⟩ := hW hz₀
  -- the image of `W` is preconnected and covered by disjoint balls around the roots
  have hpre : IsPreconnected (mFun N σ '' W) := by
    refine ((convex_ball _ _).inter bd_convex_upperHalf).isPreconnected.image _ ?_
    exact (analyticOnNhd_mFun N σ hσ).continuousOn.mono Set.inter_subset_right
  set u : Set ℂ := Metric.ball ρ₀ δ
  set v : Set ℂ := ⋃ ρ ∈ S.erase ρ₀, Metric.ball ρ δ
  have hu : IsOpen u := Metric.isOpen_ball
  have hv : IsOpen v := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hdisj_ball : ∀ ρ ∈ S, ρ ≠ ρ₀ → ∀ y, y ∈ Metric.ball ρ₀ δ → y ∉ Metric.ball ρ δ := by
    intro ρ hρ hne y hy1 hy2
    have h1 := hsep ρ₀ hρ₀ ρ hρ hne.symm
    have h2 := dist_triangle ρ₀ y ρ
    rw [Metric.mem_ball, dist_comm] at hy1
    rw [Metric.mem_ball] at hy2
    linarith
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    intro y hyu hyv
    obtain ⟨ρ, hρ, hyρ⟩ := Set.mem_iUnion₂.mp hyv
    obtain ⟨hne, hρS⟩ := Finset.mem_erase.mp hρ
    exact hdisj_ball ρ hρS hne y hyu hyρ
  have hsub : mFun N σ '' W ⊆ u ∪ v := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨ρ, hρ, hd⟩ := hW hz
    by_cases hρe : ρ = ρ₀
    · subst hρe
      exact Or.inl hd
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨ρ, Finset.mem_erase.mpr ⟨hρe, hρ⟩, hd⟩)
  have hW0 : mFun N σ '' W ⊆ u :=
    hpre.subset_left_of_subset_union hu hv huv hsub ⟨_, ⟨_, hz₀, rfl⟩, hd₀⟩
  refine ⟨ρ₀, Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
  filter_upwards [hnear (min ε δ) (lt_min hε hδ),
    inter_mem_nhdsWithin upperHalf (Metric.ball_mem_nhds (E : ℂ) hr)] with z ⟨ρ, hρ, hd⟩ hz
  have hzu : mFun N σ z ∈ u := hW0 ⟨z, ⟨hz.2, hz.1⟩, rfl⟩
  by_cases hρe : ρ = ρ₀
  · subst hρe
    exact lt_of_lt_of_le hd (min_le_left _ _)
  · exact absurd (lt_of_lt_of_le hd (min_le_right _ _))
      (hdisj_ball ρ hρ hρe _ hzu)

theorem tendsto_mFun_of_ne_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) : Tendsto (mFun N σ) (𝓝[upperHalf] (E : ℂ)) (𝓝 (mExt N σ E)) := by
  rw [bd_mExt_ofReal]
  exact tendsto_nhds_limUnder (bd_exists_tendsto N σ hσ hE)

theorem continuousOn_mExt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (mExt N σ) (upperHalf ∪ {z | z.im = 0 ∧ z ≠ 0}) := by
  have hcl : upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0} ⊆ closure upperHalf := by
    rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
    rintro z (hz | ⟨hz, -⟩)
    · exact (show (0 : ℝ) < z.im from hz).le
    · exact hz.ge
  have hcont : ∀ z ∈ upperHalf, Tendsto (mFun N σ) (𝓝[upperHalf] z) (𝓝 (mFun N σ z)) :=
    fun z hz => ((analyticOnNhd_mFun N σ hσ z hz).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hlim : ∀ z ∈ upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0},
      ∃ y, Tendsto (mFun N σ) (𝓝[upperHalf] z) (𝓝 y) := by
    rintro z (hz | ⟨hz, hz0⟩)
    · exact ⟨_, hcont z hz⟩
    · have hzE : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz])
      rw [hzE]
      refine bd_exists_tendsto N σ hσ fun h => hz0 ?_
      rw [hzE, h, Complex.ofReal_zero]
  refine (continuousOn_extendFrom hcl hlim).congr fun z hz => ?_
  rcases hz with hz | ⟨hz, -⟩
  · simp only [mExt, show 0 < z.im from hz, ↓reduceIte]
    exact (extendFrom_eq (subset_closure hz) (hcont z hz)).symm
  · simp only [mExt, hz, lt_irrefl, ↓reduceIte]
    rfl

theorem scPoly_eval_mExt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : E ≠ 0) :
    (scPoly N σ E).eval (mExt N σ E) = 0 := by
  have := bd_neBot E
  have h1 : Tendsto (fun z => (scPoly N σ E).eval (mFun N σ z)) (𝓝[upperHalf] (E : ℂ))
      (𝓝 ((scPoly N σ E).eval (mExt N σ E))) :=
    ((Polynomial.continuous _).tendsto _).comp (tendsto_mFun_of_ne_zero N σ hσ hE)
  exact tendsto_nhds_unique h1 (bd_tendsto_eval N σ hσ hE)

theorem im_mExt_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : E ≠ 0) :
    0 ≤ (mExt N σ E).im := by
  have := bd_neBot E
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_mFun_of_ne_zero N σ hσ hE)
  exact ge_of_tendsto h (eventually_nhdsWithin_of_forall fun z hz =>
    (mFun_spec N σ hσ hz).1.le)

/-- `Re f(w) = N⁻¹ Σ_i σ_i |1 + σ_i w|⁻² - Re w (|w|⁻² - N⁻¹ Σ_i σ_i² |1 + σ_i w|⁻²)`. -/
private lemma bd_re_fC (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) :
    (fC N σ w).re = ∑ i, σ i / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) -
      w.re * ((‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)) := by
  have key : ∀ i, ((σ i : ℂ) / (N * (1 + σ i * w))).re
      = σ i / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) +
        w.re * (σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)) := by
    intro i
    have h : (σ i : ℂ) / (N * (1 + σ i * w)) = ((σ i / N : ℝ) : ℂ) * (1 + σ i * w)⁻¹ := by
      push_cast
      rw [← div_div, div_eq_mul_inv ((σ i : ℂ) / (N : ℂ))]
    rw [h, Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
    ring
  unfold fC
  rw [Complex.add_re, Complex.neg_re, Complex.inv_re, Complex.re_sum]
  simp_rw [key]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.normSq_eq_norm_sq]
  ring

theorem im_mExt_of_neg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E : ℝ}
    (hE : E < 0) : (mExt N σ E).im = 0 := by
  rcases (im_mExt_nonneg N σ hσ hE.ne).lt_or_eq with hpos | h0
  · exfalso
    set w := mExt N σ E
    have hev := scPoly_eval_mExt N σ hσ hE.ne
    have hprod : ∏ s ∈ posVals σ, (1 + (s : ℂ) * w) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun s hs => bd_one_add_ne_zero (Finset.mem_filter.mp hs).2 hpos
    rw [scPoly_eval N σ hσ _ (bd_ne_zero hpos)
      (fun s hs => bd_one_add_ne_zero (Finset.mem_filter.mp hs).2 hpos)] at hev
    have hf : fC N σ w = E :=
      sub_eq_zero.mp ((mul_eq_zero.mp hev).resolve_left (mul_ne_zero (bd_ne_zero hpos) hprod))
    have him : (fC N σ w).im = 0 := by rw [hf, Complex.ofReal_im]
    rw [im_fC] at him
    have hbr := (mul_eq_zero.mp him).resolve_left hpos.ne'
    have hre := bd_re_fC N σ w
    rw [hbr, mul_zero, sub_zero, hf, Complex.ofReal_re] at hre
    have : 0 ≤ ∑ i, σ i / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) :=
      Finset.sum_nonneg fun i _ => div_nonneg (hσ i) (by positivity)
    linarith
  · exact h0.symm

/-! ## Sign lemmas -/

private lemma bd_fCDeriv_ofReal (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) :
    fCDeriv N σ (x : ℂ) = ((fR1 N σ x : ℝ) : ℂ) := by
  unfold fCDeriv fR1
  push_cast
  rfl

private lemma bd_analyticAt_fC (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : w ≠ 0)
    (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) : AnalyticAt ℂ (fC N σ) w := by
  set U : Set ℂ := {v | v ≠ 0} ∩ ⋂ i, {v | 1 + (σ i : ℂ) * v ≠ 0}
  have hU : IsOpen U := isOpen_ne.inter (isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (by fun_prop) continuous_const)
  have hd : DifferentiableOn ℂ (fC N σ) U := fun v hv =>
    (hasDerivAt_fC N σ hv.1 (Set.mem_iInter.mp hv.2)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds ⟨hw, Set.mem_iInter.mpr hw'⟩)

/-- Local inverse `h` of `f` at a real point `x` with `f'(x) ≠ 0`: near `E = f(x)`, `f ∘ h = id`,
`f'(x) Im h > 0` on `ℂ₊`, `h → x`, and `h ∘ f = id` near `x`. -/
private lemma bd_localInverse (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) (hd : fR1 N σ x ≠ 0) :
    ∃ h : ℂ → ℂ, ∃ r > 0,
      (∀ z ∈ Metric.ball ((fR N σ x : ℝ) : ℂ) r ∩ upperHalf,
        fC N σ (h z) = z ∧ 0 < fR1 N σ x * (h z).im) ∧
      Tendsto h (𝓝 ((fR N σ x : ℝ) : ℂ)) (𝓝 (x : ℂ)) ∧
      ∀ᶠ w in 𝓝 (x : ℂ), h (fC N σ w) = w := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hx0' : ∀ i, 1 + (σ i : ℂ) * (x : ℂ) ≠ 0 := fun i => by exact_mod_cast hx' i
  have hA := bd_analyticAt_fC N σ hx0 hx0'
  have hderiv : deriv (fC N σ) (x : ℂ) = ((fR1 N σ x : ℝ) : ℂ) := by
    rw [(hasDerivAt_fC N σ hx0 hx0').deriv, bd_fCDeriv_ofReal]
  have hd' : deriv (fC N σ) (x : ℂ) ≠ 0 := by
    rw [hderiv]
    exact_mod_cast hd
  set h := hA.hasStrictDerivAt.localInverse _ _ _ hd' with hh
  have hhA : AnalyticAt ℂ h (fC N σ x) := hA.analyticAt_localInverse hd'
  have himg : h (fC N σ x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  have hright : ∀ᶠ y in 𝓝 (fC N σ x), fC N σ (h y) = y :=
    hA.hasStrictDerivAt.eventually_right_inverse hd'
  have hleft : ∀ᶠ w in 𝓝 (x : ℂ), h (fC N σ w) = w :=
    hA.hasStrictDerivAt.eventually_left_inverse hd'
  have hderh : HasDerivAt h (deriv (fC N σ) x)⁻¹ (fC N σ x) :=
    (hA.hasStrictDerivAt.to_localInverse hd').hasDerivAt
  rw [fC_ofReal] at hhA himg hright hderh
  rw [hderiv] at hderh
  clear_value h
  set E : ℝ := fR N σ x
  set c : ℝ := fR1 N σ x
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hhA.eventually_analyticAt.and hright)
  set W : Set ℂ := Metric.ball (E : ℂ) r ∩ upperHalf
  have hcont : ContinuousOn h W := fun z hz =>
    (hball z hz.1).1.continuousAt.continuousWithinAt
  -- `Im h` does not vanish on `W`, since `f` maps reals to reals
  have hne : ∀ z ∈ W, (h z).im ≠ 0 := by
    intro z hz him
    have hfz := (hball z hz.1).2
    have hre : h z = (((h z).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hre, fC_ofReal] at hfz
    have h2 : (0 : ℝ) < z.im := hz.2
    rw [← hfz, Complex.ofReal_im] at h2
    exact lt_irrefl 0 h2
  -- a point `E + i t` of `W` where `c Im h > 0`, from `Im h(E + i t) = t / c + o(t)`
  have hp : HasDerivAt (fun t : ℝ => (E : ℂ) + (t : ℂ) * Complex.I) Complex.I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).const_add (E : ℂ)
    simpa using this
  have hderh' : HasDerivAt h ((c : ℂ))⁻¹ ((fun t : ℝ => (E : ℂ) + (t : ℂ) * Complex.I) 0) := by
    simpa using hderh
  have hcomp := hderh'.comp (0 : ℝ) hp
  have hsl := (Complex.continuous_im.tendsto _).comp hcomp.tendsto_slope_zero_right
  have hlim : (((c : ℂ))⁻¹ * Complex.I).im = c⁻¹ := by
    simp [← Complex.ofReal_inv]
  rw [hlim] at hsl
  have hsl' := hsl.const_mul c
  rw [mul_inv_cancel₀ hd] at hsl'
  have hev1 := hsl'.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hev2 : Set.Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
  obtain ⟨t, ht1, ht2⟩ := (hev1.and hev2).exists
  have hE0 : h E = x := himg
  simp only [Function.comp_apply, zero_add, Complex.ofReal_zero, zero_mul, add_zero, hE0,
    Complex.smul_im, Complex.sub_im, Complex.ofReal_im, sub_zero, smul_eq_mul] at ht1
  have hz₀ : (E : ℂ) + (t : ℂ) * Complex.I ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_of_nonneg ht2.1.le]
      exact ht2.2
    · change 0 < ((E : ℂ) + (t : ℂ) * Complex.I).im
      simpa using ht2.1
  have hpos₀ : 0 < c * (h ((E : ℂ) + (t : ℂ) * Complex.I)).im := by
    have ht0 := ht2.1
    have : c * (t⁻¹ * (h ((E : ℂ) + (t : ℂ) * Complex.I)).im) =
        t⁻¹ * (c * (h ((E : ℂ) + (t : ℂ) * Complex.I)).im) := by ring
    rw [this] at ht1
    exact pos_of_mul_pos_right ht1 (inv_pos.mpr ht0).le
  -- the sign of `c Im h` is constant on the preconnected set `W`
  have hpre : IsPreconnected (h '' W) :=
    ((convex_ball _ _).inter bd_convex_upperHalf).isPreconnected.image _ hcont
  set u : Set ℂ := {w | 0 < c * w.im}
  set v : Set ℂ := {w | c * w.im < 0}
  have hu : IsOpen u := isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)
  have hv : IsOpen v := isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const
  have huv : Disjoint u v := Set.disjoint_left.mpr fun w hu hv =>
    lt_asymm (show (0 : ℝ) < c * w.im from hu) (show c * w.im < 0 from hv)
  have hsub : h '' W ⊆ u ∪ v := by
    rintro _ ⟨z, hz, rfl⟩
    rcases lt_or_gt_of_ne (mul_ne_zero hd (hne z hz)) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  have hWu : h '' W ⊆ u :=
    hpre.subset_left_of_subset_union hu hv huv hsub ⟨_, ⟨_, hz₀, rfl⟩, hpos₀⟩
  refine ⟨h, r, hr, fun z hz => ⟨(hball z hz.1).2, hWu ⟨z, hz, rfl⟩⟩, ?_, hleft⟩
  have := hhA.continuousAt.tendsto
  rwa [himg] at this

/-- Sign lemma, `f'(x) > 0`: then `m(f(x)) = x`. -/
theorem mExt_fR_of_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ i, 1 + σ i * x ≠ 0) (hf : fR N σ x ≠ 0) (hd : 0 < fR1 N σ x) :
    mExt N σ (fR N σ x) = x := by
  obtain ⟨h, r, hr, hW, htend, -⟩ := bd_localInverse N σ hx hx' hd.ne'
  have heq : h =ᶠ[𝓝[upperHalf] ((fR N σ x : ℝ) : ℂ)] mFun N σ := by
    filter_upwards [inter_mem_nhdsWithin upperHalf (Metric.ball_mem_nhds _ hr)] with z hz
    obtain ⟨hfz, hpos⟩ := hW z ⟨hz.2, hz.1⟩
    exact (mFun_eq_of_fC_eq N σ hσ hz.1 ((pos_iff_pos_of_mul_pos hpos).mp hd) hfz).symm
  have ht : Tendsto (mFun N σ) (𝓝[upperHalf] ((fR N σ x : ℝ) : ℂ)) (𝓝 (x : ℂ)) :=
    (htend.mono_left nhdsWithin_le_nhds).congr' heq
  have := bd_neBot (fR N σ x)
  rw [bd_mExt_ofReal]
  exact ht.limUnder_eq

/-- Sign lemma, `f'(x) < 0`: then `m(f(x)) ≠ x`. -/
theorem mExt_fR_ne_of_neg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ i, 1 + σ i * x ≠ 0) (hf : fR N σ x ≠ 0) (hd : fR1 N σ x < 0) :
    mExt N σ (fR N σ x) ≠ x := by
  intro hm
  obtain ⟨h, r, hr, hW, -, hleft⟩ := bd_localInverse N σ hx hx' hd.ne
  have ht := tendsto_mFun_of_ne_zero N σ hσ hf
  rw [hm] at ht
  have := bd_neBot (fR N σ x)
  have hev : ∀ᶠ z in 𝓝[upperHalf] ((fR N σ x : ℝ) : ℂ), False := by
    filter_upwards [ht.eventually hleft,
      inter_mem_nhdsWithin upperHalf (Metric.ball_mem_nhds _ hr)] with z h1 hz
    obtain ⟨-, hneg⟩ := hW z ⟨hz.2, hz.1⟩
    obtain ⟨hmpos, hfm⟩ := mFun_spec N σ hσ hz.1
    rw [hfm] at h1
    rw [h1] at hneg
    have := mul_neg_of_neg_of_pos hd hmpos
    linarith
  obtain ⟨_, hfalse⟩ := hev.exists
  exact hfalse

/-! ## Concrete instance (Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`) -/

example : Tendsto (mFun 2 (fun _ : Fin 1 => (1 : ℝ))) (𝓝[upperHalf] ((5 : ℝ) : ℂ))
    (𝓝 (mExt 2 (fun _ : Fin 1 => (1 : ℝ)) (5 : ℝ))) :=
  tendsto_mFun_of_ne_zero 2 _ (fun _ => by norm_num) (by norm_num)

example : ContinuousOn (mExt 2 (fun _ : Fin 1 => (1 : ℝ)))
    (upperHalf ∪ {z | z.im = 0 ∧ z ≠ 0}) :=
  continuousOn_mExt 2 _ (fun _ => by norm_num)

example : (scPoly 2 (fun _ : Fin 1 => (1 : ℝ)) ((5 : ℝ) : ℂ)).eval
    (mExt 2 (fun _ : Fin 1 => (1 : ℝ)) (5 : ℝ)) = 0 :=
  scPoly_eval_mExt 2 _ (fun _ => by norm_num) (by norm_num)

example : 0 ≤ (mExt 2 (fun _ : Fin 1 => (1 : ℝ)) (5 : ℝ)).im :=
  im_mExt_nonneg 2 _ (fun _ => by norm_num) (by norm_num)

/-- MP: `m` is real at `E = -1`. -/
example : (mExt 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 : ℝ)).im = 0 :=
  im_mExt_of_neg 2 _ (fun _ => by norm_num) (by norm_num) (by norm_num)

end Anisotropic
