import Anisotropic.Density.Stability.EdgeTools

/-!
# (z-a_taylor) and the density near a regular edge

Appendix A: (z-a_taylor), which follows Lemma A.3, and the first step of the proof of
Lemma A.4 (`lem:stab_edge1`): the square-root behaviour of the density. The constants are those
of Lemma A.3.

* `z_a_taylor`: on the closed upper half-disk `|z - a_k| ≤ τ'₀`, `m(z)` lies in the Taylor disk
  `|ζ - x_k| < ρ₁`, `f(m(z)) = z`, `|m(z) - x_k|² ≍ |z - a_k|`, and
  `z - a_k = (f''(x_k)/2)(m(z) - x_k)² + O(|m(z) - x_k|³)`.
* `rhoDens_edge`: `π ρ(E) ≍ √|E - a_k|` on the band side of `a_k`, `ρ(E) = 0` on the gap side.
* `kappa_edgeDomain`: `κ = |E - a_k|` on `𝐃^e_k(τ, τ'')` for `τ'' ≤ τ/2` (§3.3, (def_kappa)).

Proofs.
* Localization: for `w` in the half-disk with `|m(w) - x_k| ≤ ρ₁`, `f(m(w)) = w`, so the
  lower bound of Lemma A.3 gives `(c₂/4)|m(w) - x_k|² ≤ τ'₀ = c₂ρ₁²/8`. Along the segment from
  `a_k` (where `m(a_k) = x_k`, Lemma 2.5) to `z`, `|m - x_k|` is continuous, starts at `0` and
  never takes values in `(ρ₁/√2, ρ₁]`; the intermediate value theorem keeps it below `ρ₁`.
* Band side: the real part of (z-a_taylor) gives `(Im m(E))² ≥ 4|E - a_k|/(3|f''(x_k)|)`.
* Gap side: `E = f(y)` for a real `y` in the Taylor disk on the side of `x_k` where `f' > 0`
  (intermediate value theorem on `y ↦ f(y)`), so `m(E) = y` is real.
* `κ`: every other edge is at distance `≥ τ` from `a_k` by (reg: edge).
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Elementary consequences of the assumptions -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `τ ≤ 1` and some positive `σ i`. -/
private lemma etay_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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

/-- The constants: positivity, `ρ₁ ≤ ρ₀`, `C₃ ρ₁ ≤ c₂/4`, and `τ'₀ < τ`. -/
private lemma etay_consts {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgec2 τ ∧ 0 < edgeC3 τ ∧ 0 < edgeRho1 τ ∧ edgeRho1 τ ≤ edgeRho0 τ ∧
      edgeC3 τ * edgeRho1 τ ≤ edgec2 τ / 4 ∧ 0 < edgeTau0 τ ∧ edgeTau0 τ < τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have hc3 : edgeC3 τ * edgeRho1 τ ≤ edgec2 τ / 4 := by
    have := min_le_right (edgeRho0 τ) (edgec2 τ / (4 * edgeC3 τ))
    calc edgeC3 τ * edgeRho1 τ ≤ edgeC3 τ * (edgec2 τ / (4 * edgeC3 τ)) :=
          mul_le_mul_of_nonneg_left this h3.le
      _ = edgec2 τ / 4 := by field_simp
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
  exact ⟨h2, h3, h1, h10, hc3, ht0, htτ⟩

/-- At a regular edge: `x_k` finite, `a_k = f(x_k) > 0`, and `m(a_k) = x_k` (Lemma 2.5). -/
private lemma etay_reg {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) :
    edgeVal N σ k = fR N σ (xCrit N σ k) ∧
      mExt N σ (edgeVal N σ k) = xCrit N σ k := by
  obtain ⟨hN, -, hS⟩ := etay_facts h
  obtain ⟨hk1, hk2, hτa, -, -⟩ := hk
  have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨hk', hy⟩
    have : edgeVal N σ k = 0 := by
      unfold edgeVal
      simp only [hk', ↓reduceIte, hy]
      simp [FChart]
    linarith [h.pos]
  exact ⟨edgeVal_eq_fR N σ h.nonneg hN hS hk1 hk2 hfin,
    mExt_edgeVal N σ h.nonneg hN hS hk1 hk2 hfin⟩

/-- Taylor expansion of `f` and `f'` at `x_k` along the real line, on `|y - x_k| ≤ ρ₀`. -/
private lemma etay_real_taylor {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {y : ℝ}
    (hy : |y - xCrit N σ k| ≤ edgeRho0 τ) :
    y ≠ 0 ∧ (∀ i, 1 + σ i * y ≠ 0) ∧
    |fR1 N σ y - fR2 N σ (xCrit N σ k) * (y - xCrit N σ k)| ≤
      edgeC3 τ * |y - xCrit N σ k| ^ 2 ∧
    |fR N σ y - edgeVal N σ k - fR2 N σ (xCrit N σ k) / 2 * (y - xCrit N σ k) ^ 2| ≤
      edgeC3 τ * |y - xCrit N σ k| ^ 3 := by
  have hn : ‖(y : ℂ) - xCrit N σ k‖ = |y - xCrit N σ k| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hy' : ‖(y : ℂ) - xCrit N σ k‖ ≤ edgeRho0 τ := by rw [hn]; exact hy
  obtain ⟨h0, hp, -⟩ := norm_fCDeriv3_le h hk hy'
  obtain ⟨-, t2, t3⟩ := edge_taylor h hk hy'
  rw [fCDeriv_ofReal, hn] at t2
  rw [fC_ofReal, hn] at t3
  have e2 : (fR1 N σ y : ℂ) - (fR2 N σ (xCrit N σ k) : ℂ) * ((y : ℂ) - xCrit N σ k) =
      ((fR1 N σ y - fR2 N σ (xCrit N σ k) * (y - xCrit N σ k) : ℝ) : ℂ) := by push_cast; ring
  have e3 : (fR N σ y : ℂ) - edgeVal N σ k -
      (fR2 N σ (xCrit N σ k) : ℂ) / 2 * ((y : ℂ) - xCrit N σ k) ^ 2 =
      ((fR N σ y - edgeVal N σ k - fR2 N σ (xCrit N σ k) / 2 * (y - xCrit N σ k) ^ 2 : ℝ) :
        ℂ) := by push_cast; ring
  rw [e2, Complex.norm_real, Real.norm_eq_abs] at t2
  rw [e3, Complex.norm_real, Real.norm_eq_abs] at t3
  refine ⟨fun hy0 => h0 (by rw [hy0, Complex.ofReal_zero]), fun i hi => hp i ?_, t2, t3⟩
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hi

/-- Off `0` and the poles, a root of `P_z` at `w` gives `f(w) = z`. -/
private lemma etay_fC_eq_of_eval {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {z w : ℂ}
    (hw : w ≠ 0) (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (he : (scPoly N σ z).eval w = 0) :
    fC N σ w = z := by
  have hp : ∀ s ∈ posVals σ, 1 + (s : ℂ) * w ≠ 0 := by
    intro s hs
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hs
    obtain ⟨⟨i, rfl⟩, -⟩ := hs
    exact hw' i
  rw [scPoly_eval N σ hσ z hw hp] at he
  have hprod : ∏ s ∈ posVals σ, (1 + (s : ℂ) * w) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  rcases mul_eq_zero.mp he with h1 | h1
  · exact absurd h1 (mul_ne_zero hw hprod)
  · exact sub_eq_zero.mp h1

/-- A point of the closed half-disk `|z - a_k| ≤ τ'₀`, `Im z ≥ 0`, lies in the domain of
continuity of `m` (`Re z > 0`). -/
private lemma etay_mem_dom {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {z : ℂ} (hz : 0 ≤ z.im) (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    0 < z.re ∧ z ∈ upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0} := by
  obtain ⟨-, hτ1, -⟩ := etay_facts h
  obtain ⟨-, -, -, -, -, -, htτ⟩ := etay_consts h.pos hτ1
  have ha := hk.2.2.1
  have hre : |z.re - edgeVal N σ k| ≤ ‖z - edgeVal N σ k‖ := by
    have := Complex.abs_re_le_norm (z - edgeVal N σ k)
    simpa using this
  have hpos : 0 < z.re := by
    have := (abs_le.mp (hre.trans hza)).1
    linarith
  refine ⟨hpos, ?_⟩
  rcases hz.lt_or_eq with hz' | hz'
  · exact Or.inl hz'
  · refine Or.inr ⟨hz'.symm, fun h0 => ?_⟩
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

/-- Key step of the localization: at `w` in the half-disk with `m(w)` in the Taylor disk,
`f(m(w)) = w`. -/
private lemma etay_fC_mExt {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {w : ℂ} (hw : 0 ≤ w.im)
    (hwa : ‖w - edgeVal N σ k‖ ≤ edgeTau0 τ)
    (hm : ‖mExt N σ w - xCrit N σ k‖ ≤ edgeRho0 τ) : fC N σ (mExt N σ w) = w := by
  have hσ := h.nonneg
  obtain ⟨hre, -⟩ := etay_mem_dom h hk hw hwa
  rcases hw.lt_or_eq with hw' | hw'
  · have e : mExt N σ w = mFun N σ w := by simp [mExt, hw']
    rw [e]
    exact (mFun_spec N σ hσ hw').2
  · obtain ⟨h0, hp, -⟩ := norm_fCDeriv3_le h hk hm
    have hwE : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hw'])
    have he := scPoly_eval_mExt N σ hσ (E := w.re) hre.ne'
    rw [← hwE] at he
    exact etay_fC_eq_of_eval hσ h0 hp he

/-! ## (z-a_taylor) -/

/-- (z-a_taylor): on the closed upper half-disk `|z - a_k| ≤ τ'₀`, `m(z)` stays in the Taylor
disk, `f(m(z)) = z`, and `|m(z) - x_k|² ≍ |z - a_k|`. -/
theorem z_a_taylor {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {z : ℂ} (hz : 0 ≤ z.im)
    (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    ‖mExt N σ z - xCrit N σ k‖ < edgeRho1 τ ∧ fC N σ (mExt N σ z) = z ∧
    edgec2 τ / 4 * ‖mExt N σ z - xCrit N σ k‖ ^ 2 ≤ ‖z - edgeVal N σ k‖ ∧
    ‖z - edgeVal N σ k‖ ≤ edgeC2 τ * ‖mExt N σ z - xCrit N σ k‖ ^ 2 ∧
    ‖z - edgeVal N σ k - fR2 N σ (xCrit N σ k) / 2 * (mExt N σ z - xCrit N σ k) ^ 2‖ ≤
      edgeC3 τ * ‖mExt N σ z - xCrit N σ k‖ ^ 3 := by
  have hσ := h.nonneg
  obtain ⟨-, hτ1, -⟩ := etay_facts h
  obtain ⟨hc2, -, hρ1, hρ10, -, -, -⟩ := etay_consts h.pos hτ1
  obtain ⟨-, hmA⟩ := etay_reg h hk
  set a := edgeVal N σ k with ha
  set x := xCrit N σ k with hx
  set ρ := edgeRho1 τ with hρ
  -- the bound `(c₂/4)|m(w) - x_k|² ≤ τ'₀` whenever `m(w)` is in the closed Taylor disk
  have key : ∀ w : ℂ, 0 ≤ w.im → ‖w - a‖ ≤ edgeTau0 τ → ‖mExt N σ w - x‖ ≤ ρ →
      ‖mExt N σ w - x‖ ^ 2 ≤ ρ ^ 2 / 2 := by
    intro w hw hwa hm
    have hf := etay_fC_mExt h hk hw hwa (hm.trans hρ10)
    have hl := (edge_disk_lower h hk hm).1
    rw [hf] at hl
    have : edgec2 τ / 4 * ‖mExt N σ w - x‖ ^ 2 ≤ edgec2 τ * ρ ^ 2 / 8 :=
      hl.trans (hwa.trans le_rfl)
    nlinarith
  -- the segment from `a_k` to `z`
  set γ : ℝ → ℂ := fun t => (a : ℂ) + (t : ℂ) * (z - a) with hγ
  have hγim : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (γ t).im := by
    intro t ht
    simp only [hγ, Complex.add_im, Complex.ofReal_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add, sub_zero]
    exact mul_nonneg ht.1 hz
  have hγa : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ t - a‖ ≤ edgeTau0 τ := by
    intro t ht
    simp only [hγ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖z - a‖ ≤ 1 * ‖z - a‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ ≤ edgeTau0 τ := by rw [one_mul]; exact hza
  set g : ℝ → ℝ := fun t => ‖mExt N σ (γ t) - x‖ with hg
  have hgc : ContinuousOn g (Set.Icc 0 1) := by
    have hγc : Continuous γ := by simp only [hγ]; fun_prop
    have hm : ContinuousOn (fun t => mExt N σ (γ t)) (Set.Icc 0 1) :=
      (continuousOn_mExt N σ hσ).comp hγc.continuousOn
        (fun t ht => (etay_mem_dom h hk (hγim t ht) (hγa t ht)).2)
    exact (hm.sub continuousOn_const).norm
  have hg0 : g 0 = 0 := by
    simp only [hg, hγ, Complex.ofReal_zero, zero_mul, add_zero, hmA, sub_self, norm_zero]
  have hg1 : γ 1 = z := by simp [hγ]
  have hloc : ‖mExt N σ z - x‖ < ρ := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have hmem : 9 / 10 * ρ ∈ Set.Icc (g 0) (g 1) := by
      rw [hg0]
      refine ⟨by positivity, ?_⟩
      simp only [hg, hg1]
      linarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc zero_le_one hgc hmem
    have := key (γ t) (hγim t ht) (hγa t ht) (by
      simp only [hg] at hgt; rw [hgt]; linarith)
    simp only [hg] at hgt
    rw [hgt] at this
    nlinarith
  have hf := etay_fC_mExt h hk hz hza (hloc.le.trans hρ10)
  obtain ⟨l1, l2, -⟩ := edge_disk_lower h hk hloc.le
  obtain ⟨-, -, t3⟩ := edge_taylor h hk (hloc.le.trans hρ10)
  rw [hf] at l1 l2 t3
  exact ⟨hloc, hf, l1, l2, t3⟩

/-! ## The density near a regular edge -/

/-- Band side of `a_k`: `|E - a_k|/C₂ ≤ (Im m(E))²` and `(Im m(E))² ≤ 4|E - a_k|/c₂`, with
`s = (-1)^{k+1}`. -/
private lemma etay_band {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hsF : edgec2 τ ≤ s * fR2 N σ (xCrit N σ k)) {E : ℝ}
    (hE : |E - edgeVal N σ k| ≤ edgeTau0 τ) (hband : s * (E - edgeVal N σ k) ≤ 0) :
    √(|E - edgeVal N σ k| / edgeC2 τ) ≤ (mExt N σ E).im ∧
      (mExt N σ E).im ≤ 2 * √(|E - edgeVal N σ k| / edgec2 τ) := by
  have hσ := h.nonneg
  obtain ⟨hN, hτ1, -⟩ := etay_facts h
  obtain ⟨hc2, hC3, hρ1, hρ10, hc3, ht0, htτ⟩ := etay_consts h.pos hτ1
  obtain ⟨hafR, -⟩ := etay_reg h hk
  have hFC := abs_fR2_xCrit_le h hk
  set a := edgeVal N σ k with ha
  set x := xCrit N σ k with hx
  set F := fR2 N σ x with hFdef
  set t := |E - a| with htdef
  have hEpos : 0 < E := by
    have := (abs_le.mp hE).1
    linarith [hk.2.2.1]
  have hs2 : s * s = 1 := by rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
  have hsa : |s| = 1 := by rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
  have hza : ‖(E : ℂ) - a‖ = t := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨hloc, -, l1, -, hrem⟩ := z_a_taylor h hk (z := E) (by simp) (hza.le.trans hE)
  rw [← hx] at hloc
  rw [← ha, ← hx] at l1 hrem
  rw [← hFdef] at hrem
  rw [hza] at l1
  set v := mExt N σ (E : ℂ) - x with hv
  have hb : (mExt N σ E).im = v.im := by simp [hv]
  rw [hb]
  have hb0 : 0 ≤ v.im := by rw [← hb]; exact im_mExt_nonneg N σ hσ hEpos.ne'
  have hvn : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hvn0 : 0 ≤ ‖v‖ := norm_nonneg _
  -- the real part of the remainder
  have hre : |(E - a) - F / 2 * (v.re ^ 2 - v.im ^ 2)| ≤ edgeC3 τ * ‖v‖ ^ 3 := by
    refine le_trans ?_ hrem
    have e : ((E : ℂ) - a - (F : ℂ) / 2 * v ^ 2).re =
        (E - a) - F / 2 * (v.re ^ 2 - v.im ^ 2) := by
      simp [sq, Complex.mul_re]
    rw [← e]
    exact Complex.abs_re_le_norm _
  have hC : edgeC3 τ * ‖v‖ ^ 3 ≤ edgec2 τ / 4 * (v.re ^ 2 + v.im ^ 2) := by
    have h1 : edgeC3 τ * ‖v‖ ≤ edgec2 τ / 4 :=
      (mul_le_mul_of_nonneg_left hloc.le hC3.le).trans hc3
    rw [← hvn]
    calc edgeC3 τ * ‖v‖ ^ 3 = (edgeC3 τ * ‖v‖) * ‖v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hre' := abs_le.mp (hre.trans hC)
  have hFabs := abs_le.mp hFC
  -- `|E - a_k| ≤ C₂ (Im v)²`
  have hlow : t ≤ edgeC2 τ * v.im ^ 2 := by
    rcases hs with h1 | h1
    · rw [h1, one_mul] at hband hsF
      have ht : t = a - E := by rw [htdef, abs_of_nonpos (by linarith)]; ring
      nlinarith [sq_nonneg v.re, sq_nonneg v.im]
    · rw [h1] at hband hsF
      have ht : t = E - a := by rw [htdef, abs_of_nonneg (by linarith)]
      nlinarith [sq_nonneg v.re, sq_nonneg v.im]
  have hC2 : 0 < edgeC2 τ := by
    have : s * F ≤ |F| := by
      calc s * F ≤ |s * F| := le_abs_self _
        _ = |F| := by rw [abs_mul, hsa, one_mul]
    linarith
  constructor
  · rw [← Real.sqrt_sq hb0]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hC2]; linarith
  · have h2 : v.im ^ 2 ≤ 4 * (t / edgec2 τ) := by
      rw [mul_div_assoc', le_div_iff₀ hc2]
      nlinarith [sq_nonneg v.re]
    have h4 : (2 : ℝ) = √4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← Real.sqrt_sq hb0, h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h2

/-- Gap side of `a_k`: `ρ(E) = 0`, with `s = (-1)^{k+1}`. -/
private lemma etay_gap {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hsF : edgec2 τ ≤ s * fR2 N σ (xCrit N σ k)) {E : ℝ}
    (hE : |E - edgeVal N σ k| ≤ edgeTau0 τ) (hgap : 0 < s * (E - edgeVal N σ k)) :
    rhoDens N σ E = 0 := by
  have hσ := h.nonneg
  obtain ⟨hN, hτ1, -⟩ := etay_facts h
  obtain ⟨hc2, hC3, hρ1, hρ10, hc3, ht0, htτ⟩ := etay_consts h.pos hτ1
  obtain ⟨hafR, -⟩ := etay_reg h hk
  have hFC := abs_fR2_xCrit_le h hk
  set a := edgeVal N σ k with ha
  set x := xCrit N σ k with hx
  set F := fR2 N σ x with hFdef
  set t := |E - a| with htdef
  have hEpos : 0 < E := by
    have := (abs_le.mp hE).1
    linarith [hk.2.2.1]
  have hs2 : s * s = 1 := by rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
  have hsa : |s| = 1 := by rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
  have hsh : ∀ r : ℝ, |x + s * r - x| = |r| := by
    intro r; rw [add_sub_cancel_left, abs_mul, hsa, one_mul]
  set g : ℝ → ℝ := fun r => s * (fR N σ (x + s * r) - a) with hg
  have hgc : ContinuousOn g (Set.Icc 0 (edgeRho1 τ)) := by
    intro r hr
    have hr' : |x + s * r - x| ≤ edgeRho0 τ := by
      rw [hsh, abs_of_nonneg hr.1]; exact hr.2.trans hρ10
    obtain ⟨hy0, hyp, -, -⟩ := etay_real_taylor h hk hr'
    have hc : ContinuousAt (fun r => fR N σ (x + s * r)) r :=
      ContinuousAt.comp (g := fR N σ) (hasDerivAt_fR N σ hy0 hyp).continuousAt
        (by fun_prop)
    exact (continuousAt_const.mul (hc.sub continuousAt_const)).continuousWithinAt
  have hg0 : g 0 = 0 := by simp [hg, hafR]
  have hgρ : edgeTau0 τ ≤ g (edgeRho1 τ) := by
    have hr' : |x + s * edgeRho1 τ - x| ≤ edgeRho0 τ := by
      rw [hsh, abs_of_pos hρ1]; exact hρ10
    obtain ⟨-, -, -, t3⟩ := etay_real_taylor h hk hr'
    rw [hsh, abs_of_pos hρ1, add_sub_cancel_left] at t3
    have hsq : (s * edgeRho1 τ) ^ 2 = edgeRho1 τ ^ 2 := by
      rw [mul_pow, sq s, hs2, one_mul]
    rw [hsq] at t3
    set r := fR N σ (x + s * edgeRho1 τ) - a - F / 2 * edgeRho1 τ ^ 2 with hr
    have hgr : g (edgeRho1 τ) = s * F / 2 * edgeRho1 τ ^ 2 + s * r := by
      simp only [hg, hr]; ring
    have hsr : |s * r| ≤ edgeC3 τ * edgeRho1 τ ^ 3 := by rw [abs_mul, hsa, one_mul]; exact t3
    have h3 : edgeC3 τ * edgeRho1 τ ^ 3 ≤ edgec2 τ / 4 * edgeRho1 τ ^ 2 := by
      calc edgeC3 τ * edgeRho1 τ ^ 3 = (edgeC3 τ * edgeRho1 τ) * edgeRho1 τ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc3 (sq_nonneg _)
    have hsF' : edgec2 τ / 2 * edgeRho1 τ ^ 2 ≤ s * F / 2 * edgeRho1 τ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hsF (sq_nonneg (edgeRho1 τ))
      linarith
    rw [hgr]
    unfold edgeTau0
    linarith [(abs_le.mp hsr).1, mul_nonneg hc2.le (sq_nonneg (edgeRho1 τ))]
  have hmem : s * (E - a) ∈ Set.Icc (g 0) (g (edgeRho1 τ)) := by
    rw [hg0]
    refine ⟨hgap.le, ?_⟩
    have : s * (E - a) ≤ t := by
      calc s * (E - a) ≤ |s * (E - a)| := le_abs_self _
        _ = t := by rw [abs_mul, hsa, one_mul]
    linarith
  obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc hρ1.le hgc hmem
  have hr0 : 0 < r := by
    rcases hr.1.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, hg0] at hgr; linarith
  have hr' : |x + s * r - x| ≤ edgeRho0 τ := by
    rw [hsh, abs_of_pos hr0]; exact hr.2.trans hρ10
  obtain ⟨hy0, hyp, t2, -⟩ := etay_real_taylor h hk hr'
  rw [hsh, abs_of_pos hr0, add_sub_cancel_left, ← hx, ← hFdef] at t2
  have hfy : fR N σ (x + s * r) = E := by
    have h1 : s * (fR N σ (x + s * r) - a) = s * (E - a) := hgr
    have h2 := congrArg (fun u => s * u) h1
    simp only [← mul_assoc, hs2, one_mul] at h2
    linarith
  have hd : 0 < fR1 N σ (x + s * r) := by
    have h1 : edgeC3 τ * r ^ 2 ≤ edgec2 τ / 4 * r := by
      calc edgeC3 τ * r ^ 2 = (edgeC3 τ * r) * r := by ring
        _ ≤ (edgeC3 τ * edgeRho1 τ) * r := by gcongr; exact hr.2
        _ ≤ _ := mul_le_mul_of_nonneg_right hc3 hr0.le
    have h2 : edgec2 τ * r ≤ F * (s * r) := by
      have := mul_le_mul_of_nonneg_right hsF hr0.le
      linarith
    linarith [(abs_le.mp t2).1, mul_pos hc2 hr0]
  have hm := mExt_fR_of_pos N σ hσ hN hy0 hyp (by rw [hfy]; exact hEpos.ne') hd
  rw [hfy] at hm
  unfold rhoDens
  rw [hm, Complex.ofReal_im, zero_div]

/-- Square-root behaviour of the density near a regular edge: on the band side
(`(-1)^{k+1}(E - a_k) ≤ 0`) `π ρ(E) ≍ √|E - a_k|`, on the gap side `ρ(E) = 0`. -/
theorem rhoDens_edge {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {E : ℝ} (hE : |E - edgeVal N σ k| ≤ edgeTau0 τ) :
    ((-1 : ℝ) ^ (k + 1) * (E - edgeVal N σ k) ≤ 0 →
      √(|E - edgeVal N σ k| / edgeC2 τ) ≤ Real.pi * rhoDens N σ E ∧
        Real.pi * rhoDens N σ E ≤ 2 * √(|E - edgeVal N σ k| / edgec2 τ)) ∧
    (0 < (-1 : ℝ) ^ (k + 1) * (E - edgeVal N σ k) → rhoDens N σ E = 0) := by
  have hs : (-1 : ℝ) ^ (k + 1) = 1 ∨ (-1 : ℝ) ^ (k + 1) = -1 := neg_one_pow_eq_or ℝ (k + 1)
  have hsF := edgec2_le_fR2_xCrit h hk
  have hπ : Real.pi * rhoDens N σ E = (mExt N σ E).im := by
    unfold rhoDens; field_simp
  rw [hπ]
  exact ⟨etay_band h hk hs hsF hE, etay_gap h hk hs hsF hE⟩

/-! ## `κ` on `𝐃^e_k` -/

/-- On `𝐃^e_k` with `τ'' ≤ τ/2`, `κ = |E - a_k|`. -/
theorem kappa_edgeDomain {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ τ / 2) {z : ℂ}
    (hz : z ∈ edgeDomain τ τ'' N σ k) : kappa N σ z.re = |z.re - edgeVal N σ k| := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  have hE : |z.re - edgeVal N σ k| ≤ τ'' := by
    obtain ⟨-, h1, h2⟩ := hz
    rw [abs_le]; constructor <;> linarith
  have hmem : k ∈ Finset.Icc 1 (2 * numBands N σ) := Finset.mem_Icc.2 ⟨hk1, hk2⟩
  have : Nonempty (Finset.Icc 1 (2 * numBands N σ)) := ⟨⟨k, hmem⟩⟩
  unfold kappa
  refine le_antisymm ?_ ?_
  · refine ciInf_le ⟨0, ?_⟩ (⟨k, hmem⟩ : Finset.Icc 1 (2 * numBands N σ))
    rintro _ ⟨l, rfl⟩
    exact abs_nonneg _
  · refine le_ciInf fun l => ?_
    by_cases hl : (l : ℕ) = k
    · rw [hl]
    · obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 l.2
      have h1 := hsep l hl1 hl2 hl
      have h2 : |edgeVal N σ k - edgeVal N σ l| ≤
          |z.re - edgeVal N σ l| + |z.re - edgeVal N σ k| := by
        have := abs_sub (z.re - edgeVal N σ l) (z.re - edgeVal N σ k)
        rwa [show z.re - edgeVal N σ l - (z.re - edgeVal N σ k) =
          edgeVal N σ k - edgeVal N σ l by ring] at this
      linarith

/-! ## Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `τ = 1/20` (`φ = 1/2`, `p = 1`, `x_1 = √2 - 2`,
`a_1 = 3/2 + √2`), at the edge `k = 1`. -/

local notation "σMP" => (fun _ : Fin 1 => (1 : ℝ))
local notation "xMP" => xCrit 2 σMP 1
local notation "aMP" => edgeVal 2 σMP 1

end Anisotropic
