import Anisotropic.EdgeUniv.SmCount
import Anisotropic.Entrywise.Defs
import Anisotropic.Framework.Domination
import Anisotropic.LinAlg.Basic
import Anisotropic.LinAlg.Expansion
import Anisotropic.LinAlg.ResolventId
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The smoothed count as an integral of `Im m_N`, and its entry derivatives -/

/-- `m_N` is the average of the resolvent poles of `Q_N`. -/
private lemma derivative_mN_eq_sum {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    mN Sig Xm z = (N : ℂ)⁻¹ * ∑ j, ((specOf (QN Sig Xm) j : ℂ) - z)⁻¹ := by
  rw [mN_eq_resolventTransform hSig Xm hz, resolventTransform_apply, empMeasure,
    integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
    rw [Complex.real_smul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp [QN]
  · intro k _
    exact integrable_dirac (by simp [resolvent, Ring.inverse_eq_inv'])

/-- The imaginary part of one pole term of `m_N`. -/
private lemma derivative_im_pole (lam y η : ℝ) :
    (((lam : ℂ) - (y + η * Complex.I))⁻¹).im = η / ((lam - y) ^ 2 + η ^ 2) := by
  rw [Complex.inv_im]
  have h1 : ((lam : ℂ) - (y + η * Complex.I)).im = -η := by simp
  rw [h1, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, zero_sub]
  rw [neg_neg]
  congr 1; ring

/-- `∫_{E₁}^{E₂} η / ((λ - y)² + η²) dy = arctan((E₂ - λ)/η) - arctan((E₁ - λ)/η)`. -/
private lemma derivative_integral_pole (lam η E₁ E₂ : ℝ) (hη : 0 < η) :
    ∫ y in E₁..E₂, η / ((lam - y) ^ 2 + η ^ 2) =
      Real.arctan ((E₂ - lam) / η) - Real.arctan ((E₁ - lam) / η) := by
  have hd : ∀ y ∈ Set.uIcc E₁ E₂,
      HasDerivAt (fun y : ℝ => Real.arctan ((y - lam) / η)) (η / ((lam - y) ^ 2 + η ^ 2)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => (y - lam) / η) (1 / η) y :=
      ((hasDerivAt_id y).sub_const lam).div_const η
    have h2 := h1.arctan
    convert h2 using 1
    field_simp
    ring
  have hc : Continuous fun y : ℝ => η / ((lam - y) ^ 2 + η ^ 2) := by
    refine continuous_const.div (by fun_prop) fun y => by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)

/-- `𝒳_{[E₁,E₂]}(Q_N) = (N/π) ∫_{E₁}^{E₂} Im m_N(y + iη) dy`. -/
theorem smCount_eq_integral {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    smCount (QN Sig Xm) η E₁ E₂ =
      N / Real.pi * ∫ y in E₁..E₂, (mN Sig Xm (y + η * Complex.I)).im := by
  have hz : ∀ y : ℝ, 0 < ((y : ℂ) + η * Complex.I).im := fun y => by simpa using hη
  have him : ∀ y : ℝ, (mN Sig Xm (y + η * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ j, η / ((specOf (QN Sig Xm) j - y) ^ 2 + η ^ 2) := by
    intro y
    rw [derivative_mN_eq_sum hSig Xm (hz y)]
    have : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [derivative_im_pole _ y η]
  simp only [him]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp [smCount]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · simp only [derivative_integral_pole _ η E₁ E₂ hη]
      unfold smCount
      have hN : (N : ℝ) ≠ 0 := by positivity
      rw [← Finset.sum_div]
      field_simp
    · intro j _
      exact (by
        refine Continuous.intervalIntegrable ?_ _ _
        refine continuous_const.div (by fun_prop) fun y => by positivity)

/-! ### Derivatives of `G` along the entry `(i, μ)` -/

/-- `Delta i μ c = c • Delta i μ 1`. -/
private lemma derivative_Delta_smul (i : Fin M) (μ : Fin N) (c : ℝ) :
    Delta i μ c = (c : ℂ) • Delta i μ 1 := by
  ext s t
  simp only [Delta, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `(B Δ¹ C)_{st} = B_{s i} C_{μ t} + B_{s μ} C_{i t}`. -/
private lemma derivative_mul_Delta_mul (B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    (B * Delta i μ 1 * C) s t = B s (Sum.inl i) * C (Sum.inr μ) t +
      B s (Sum.inr μ) * C (Sum.inl i) t := by
  have hBD : ∀ r, (B * Delta i μ 1) s r =
      (if r = Sum.inr μ then B s (Sum.inl i) else 0) +
        (if r = Sum.inl i then B s (Sum.inr μ) else 0) := by
    intro r
    rw [Matrix.mul_apply]
    rcases r with j | ν
    · by_cases hj : j = i <;> simp [Delta, hj]
    · by_cases hν : ν = μ <;> simp [Delta, hν]
  rw [Matrix.mul_apply]
  simp only [hBD, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def DerivMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma derivative_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : DerivMD f f' x) (hg : DerivMD g g' x) :
    DerivMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma derivative_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    DerivMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

/-- `y ↦ G(X^{y}_{(iμ)}, z)` is jointly continuous with `z = w + iη`. -/
private lemma derivative_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (i : Fin M) (μ : Fin N) :
    Continuous fun p : ℝ × ℝ =>
      G Sig (Xupd A i μ p.1) ((p.2 : ℂ) + η * Complex.I) := by
  have hX : Continuous fun y : ℝ => cplx (Xupd A i μ y) := by
    refine continuous_matrix fun a b => ?_
    by_cases h : a = i ∧ b = μ
    · simpa [cplx, Xupd, h] using Complex.continuous_ofReal
    · simpa [cplx, Xupd, h] using continuous_const
  have hXt : Continuous fun y : ℝ => cplx (Xupd A i μ y)ᵀ := by
    refine continuous_matrix fun a b => ?_
    by_cases h : b = i ∧ a = μ
    · simpa [cplx, Xupd, h] using Complex.continuous_ofReal
    · simpa [cplx, Xupd, h] using continuous_const
  have hH : Continuous fun p : ℝ × ℝ =>
      H Sig (Xupd A i μ p.1) ((p.2 : ℂ) + η * Complex.I) := by
    have h1 : Continuous fun p : ℝ × ℝ => cplx (Xupd A i μ p.1) := hX.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => cplx (Xupd A i μ p.1)ᵀ := hXt.comp continuous_fst
    have h3 : Continuous fun p : ℝ × ℝ =>
        -(((p.2 : ℂ) + η * Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const).neg
    exact continuous_const.matrix_fromBlocks h1 h2 h3
  rw [continuous_iff_continuousAt]
  intro p
  have hu := (Matrix.isUnit_iff_isUnit_det _).1
    (H_isUnit hSig (Xupd A i μ p.1) (z := (p.2 : ℂ) + η * Complex.I) (by simpa using hη))
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  change ContinuousAt (fun p : ℝ × ℝ =>
    (H Sig (Xupd A i μ p.1) ((p.2 : ℂ) + η * Complex.I))⁻¹) p
  exact hinv.comp (f := fun p : ℝ × ℝ => H Sig (Xupd A i μ p.1) ((p.2 : ℂ) + η * Complex.I))
    hH.continuousAt

/-- `y ↦ G(X^{y}_{(iμ)}, z)` is continuous. -/
private lemma derivative_continuousAt_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ) :
    ContinuousAt (fun y => G Sig (Xupd A i μ y) z) x := by
  have hc := derivative_continuous_G hSig A hz i μ
  have hz' : (z.re : ℂ) + z.im * Complex.I = z := Complex.re_add_im z
  have h2 : Continuous fun y : ℝ => G Sig (Xupd A i μ y) z := by
    have := hc.comp (Continuous.prodMk continuous_id (continuous_const (y := z.re)))
    simpa [Function.comp_def, hz'] using this
  exact h2.continuousAt

/-- `d/dy G(X^{y}_{(iμ)}) = -G Δ¹ G`. -/
private lemma derivative_MD_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ) :
    DerivMD (fun y => G Sig (Xupd A i μ y) z)
      (-(G Sig (Xupd A i μ x) z * Delta i μ 1 * G Sig (Xupd A i μ x) z)) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set G0 := G Sig (Xupd A i μ x) z with hG0
  have hid : ∀ h : ℝ, G Sig (Xupd A i μ (x + h)) z - G0 =
      (-(h : ℂ)) • (G Sig (Xupd A i μ (x + h)) z * Delta i μ 1 * G0) := by
    intro h
    have e := res_exp hSig A hz i μ x (x + h) 0
    rw [show x - (x + h) = -h by ring, derivative_Delta_smul] at e
    simp only [zero_add, pow_one, Finset.Icc_eq_empty_of_lt one_pos,
      Finset.sum_empty, add_zero] at e
    rw [show G Sig (Xupd A i μ (x + h)) z - G0 = G Sig (Xupd A i μ (x + h)) z *
      (((-h : ℝ) : ℂ) • Delta i μ 1 * G0) from sub_eq_iff_eq_add'.2 e]
    push_cast
    simp [Matrix.mul_assoc]
  have hc : ∀ r, ContinuousAt (fun h : ℝ => G Sig (Xupd A i μ (x + h)) z s r) 0 := fun r => by
    have h2 : ContinuousAt (fun h : ℝ => x + h) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have h3 : ContinuousAt ((fun y => G Sig (Xupd A i μ y) z) ∘ fun h : ℝ => x + h) 0 :=
      ContinuousAt.comp_of_eq (derivative_continuousAt_G hSig A hz i μ x) h2 (by simp)
    exact ((continuous_apply r).comp (continuous_apply s)).continuousAt.comp h3
  have hE : ContinuousAt
      (fun h : ℝ => (G Sig (Xupd A i μ (x + h)) z * Delta i μ 1 * G0) s t) 0 := by
    simp only [derivative_mul_Delta_mul]
    exact ((hc _).mul continuousAt_const).add ((hc _).mul continuousAt_const)
  have hlim := hE.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [add_zero] at hlim
  refine hlim.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℂ) ≠ 0 := by simpa using hh
  have := congrFun (congrFun (hid h) s) t
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this, Complex.real_smul]
  push_cast
  field_simp

/-- `(B P_N C)_{st} = ∑_ν B_{s ν} C_{ν t}`. -/
private lemma derivative_PN_apply (B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (s t : Fin M ⊕ Fin N) :
    (B * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) * C) s t =
      ∑ ν, B s (Sum.inr ν) * C (Sum.inr ν) t := by
  have hBP : ∀ r, (B * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)) s r =
      Sum.elim (fun _ => 0) (fun ν => B s (Sum.inr ν)) r := by
    intro r
    rw [Matrix.mul_apply]
    rcases r with j | ν
    · simp [PN, Fintype.sum_sum_type]
    · simp [PN, Fintype.sum_sum_type, Matrix.one_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hBP, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]

/-- The trace over the `𝓘_N` block of `G Δ¹ G`, for a symmetric `G`. -/
private lemma derivative_trace_GDG {B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ}
    (hB : Bᵀ = B) (i : Fin M) (μ : Fin N) :
    ∑ ν, (B * Delta i μ 1 * B) (Sum.inr ν) (Sum.inr ν) =
      2 * (B * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) * B) (Sum.inr μ) (Sum.inl i) := by
  have hs : ∀ a b, B a b = B b a := fun a b => by
    have := congrFun (congrFun hB b) a
    simpa [Matrix.transpose_apply] using this
  rw [derivative_PN_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [derivative_mul_Delta_mul, hs (Sum.inr ν) (Sum.inl i), hs (Sum.inr ν) (Sum.inr μ)]
  ring

private lemma derivative_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  exact this

/-- `∂_t tr_N G = -2 (G P_N G)_{μ i}`. -/
private lemma derivative_hasDerivAt_trN {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ) :
    HasDerivAt (fun t => ∑ ν, G Sig (Xupd Xm i μ t) z (Sum.inr ν) (Sum.inr ν))
      (-(2 * (G Sig (Xupd Xm i μ x) z * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
        G Sig (Xupd Xm i μ x) z) (Sum.inr μ) (Sum.inl i))) x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun ν _ =>
    derivative_MD_G hSig Xm hz i μ x (Sum.inr ν) (Sum.inr ν)
  refine h.congr_deriv ?_
  rw [← derivative_trace_GDG (G_transpose hSig _ hz), ← Finset.sum_neg_distrib]
  simp only [Matrix.neg_apply]

/-- `d/dy G(X, y + iη)_{st} = (G P_N G)_{st}`. -/
private lemma derivative_hasDerivAt_G_re {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (y : ℝ) (s t : Fin M ⊕ Fin N) :
    HasDerivAt (fun w : ℝ => G Sig X ((w : ℂ) + η * Complex.I) s t)
      ((G Sig X ((y : ℂ) + η * Complex.I) * (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
        G Sig X ((y : ℂ) + η * Complex.I)) s t) y := by
  have hz : 0 < (((y : ℂ)) + η * Complex.I).im := by simpa using hη
  have h1 := hasDerivAt_G hSig X hz s t
  have h2 : HasDerivAt (fun w : ℂ => G Sig X (w + η * Complex.I) s t) _ (y : ℂ) :=
    HasDerivAt.comp_add_const (y : ℂ) (η * Complex.I) h1
  exact h2.comp_ofReal

/-- `𝒳 = π⁻¹ ∫_{E₁}^{E₂} Im tr_N G(y + iη) dy`. -/
private lemma derivative_smCount_eq_trace {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (hN : N ≠ 0) :
    smCount (QN Sig Xm) η E₁ E₂ = Real.pi⁻¹ *
      ∫ y in E₁..E₂, (∑ ν, G Sig Xm ((y : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
  rw [smCount_eq_integral hSig Xm hη]
  have him : ∀ y : ℝ, (mN Sig Xm (y + η * Complex.I)).im =
      (N : ℝ)⁻¹ * (∑ ν, G Sig Xm ((y : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
    intro y
    have : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [mN, this, Complex.im_ofReal_mul]
  simp only [him]
  rw [intervalIntegral.integral_const_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp

/-- The integrand `Im tr_N G(X^{t}_{(iμ)}, y + iη)` of the smoothed count. -/
private def derivF (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (η : ℝ)
    (i : Fin M) (μ : Fin N) (t y : ℝ) : ℝ :=
  (∑ ν, G Sig (Xupd Xm i μ t) ((y : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im

/-- Its derivative in the entry: `-2 Im (G P_N G)_{μ i}`. -/
private def derivF' (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (η : ℝ)
    (i : Fin M) (μ : Fin N) (t y : ℝ) : ℝ :=
  -(2 * ((G Sig (Xupd Xm i μ t) ((y : ℂ) + η * Complex.I) *
    (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
      G Sig (Xupd Xm i μ t) ((y : ℂ) + η * Complex.I)) (Sum.inr μ) (Sum.inl i)).im)

private lemma derivative_continuous_derivF {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (i : Fin M) (μ : Fin N) :
    Continuous fun p : ℝ × ℝ => derivF Sig Xm η i μ p.1 p.2 := by
  have hGc := derivative_continuous_G hSig Xm hη i μ
  simp only [derivF]
  fun_prop

private lemma derivative_continuous_derivF' {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (i : Fin M) (μ : Fin N) :
    Continuous fun p : ℝ × ℝ => derivF' Sig Xm η i μ p.1 p.2 := by
  have hGc := derivative_continuous_G hSig Xm hη i μ
  simp only [derivF']
  fun_prop

private lemma derivative_hasDerivAt_derivF {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (i : Fin M) (μ : Fin N) (x y : ℝ) :
    HasDerivAt (fun t => derivF Sig Xm η i μ t y) (derivF' Sig Xm η i μ x y) x := by
  have hz : 0 < (((y : ℂ)) + η * Complex.I).im := by simpa using hη
  have h1 := derivative_hasDerivAt_im (derivative_hasDerivAt_trN hSig Xm hz i μ x)
  refine h1.congr_deriv ?_
  simp only [derivF']
  rw [show (-(2 * (G Sig (Xupd Xm i μ x) ((y : ℂ) + η * Complex.I) *
      (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
      G Sig (Xupd Xm i μ x) ((y : ℂ) + η * Complex.I)) (Sum.inr μ) (Sum.inl i))).im =
    -(2 * ((G Sig (Xupd Xm i μ x) ((y : ℂ) + η * Complex.I) *
      (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
      G Sig (Xupd Xm i μ x) ((y : ℂ) + η * Complex.I)) (Sum.inr μ) (Sum.inl i)).im) by
    simp]

/-- The entry derivative: `∂_{X_{iμ}} 𝒳_{[E₁,E₂]} = -(2/π) Im (G_{μi}(E₂ + iη) - G_{μi}(E₁ + iη))`. -/
theorem hasDerivAt_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (u : ℝ) :
    HasDerivAt (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂)
      (-(2 / Real.pi) * ((G Sig (Xupd Xm i μ u) (E₂ + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im -
        (G Sig (Xupd Xm i μ u) (E₁ + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im)) u := by
  have hN : N ≠ 0 := (Fin.pos μ).ne'
  have hFc := derivative_continuous_derivF hSig Xm hη i μ
  have hF'c := derivative_continuous_derivF' hSig Xm hη i μ
  have hFy : ∀ t, Continuous fun y => derivF Sig Xm η i μ t y := fun t => by
    have h := hFc.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)
    exact h
  have hF'y : ∀ t, Continuous fun y => derivF' Sig Xm η i μ t y := fun t => by
    have h := hF'c.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)
    exact h
  -- a uniform bound on the derivative near `u`
  obtain ⟨C, hC⟩ := ((isCompact_closedBall u 1).prod (isCompact_uIcc (a := E₁) (b := E₂))
    ).exists_bound_of_continuousOn hF'c.continuousOn
  -- differentiation under the integral sign
  have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := E₁) (b := E₂) (F := derivF Sig Xm η i μ) (F' := derivF' Sig Xm η i μ)
    (x₀ := u) (s := Metric.ball u 1)
    (bound := fun _ => C) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun t => (hFy t).aestronglyMeasurable)
    ((hFy u).intervalIntegrable _ _) (hF'y u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y hy x hx => by
      have := hC (x, y) ⟨Metric.ball_subset_closedBall hx, Set.uIoc_subset_uIcc hy⟩
      simpa using this)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun y _ x _ =>
      derivative_hasDerivAt_derivF hSig Xm hη i μ x y)
  -- the fundamental theorem of calculus in the spectral variable
  have hGy : Continuous fun p : ℝ × ℝ => G Sig (Xupd Xm i μ p.1) ((p.2 : ℂ) + η * Complex.I) :=
    derivative_continuous_G hSig Xm hη i μ
  have hg' : Continuous fun y : ℝ =>
      ((G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I) *
        (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
          G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I)) (Sum.inr μ) (Sum.inl i)).im := by
    have h := hGy.comp (Continuous.prodMk (continuous_const (y := u)) continuous_id)
    have h' : Continuous fun y : ℝ => G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I) := h
    fun_prop
  have hFTC : ∫ y in E₁..E₂, derivF' Sig Xm η i μ u y =
      -2 * ((G Sig (Xupd Xm i μ u) ((E₂ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im -
        (G Sig (Xupd Xm i μ u) ((E₁ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im) := by
    have hint : ∫ y in E₁..E₂, ((G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I) *
        (PN : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) *
          G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I)) (Sum.inr μ) (Sum.inl i)).im =
        (G Sig (Xupd Xm i μ u) ((E₂ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im -
          (G Sig (Xupd Xm i μ u) ((E₁ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)).im :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => (G Sig (Xupd Xm i μ u) ((y : ℂ) + η * Complex.I)
          (Sum.inr μ) (Sum.inl i)).im)
        (fun y _ => derivative_hasDerivAt_im
          (derivative_hasDerivAt_G_re hSig (Xupd Xm i μ u) hη y (Sum.inr μ) (Sum.inl i)))
        (hg'.intervalIntegrable _ _)
    simp only [derivF']
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, hint]
    ring
  have hform : (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) =
      fun t => Real.pi⁻¹ * ∫ y in E₁..E₂, derivF Sig Xm η i μ t y := by
    funext t
    exact derivative_smCount_eq_trace hSig (Xupd Xm i μ t) hη E₁ E₂ hN
  rw [hform]
  have h := hdiff.2.const_mul Real.pi⁻¹
  rw [hFTC] at h
  convert h using 1
  field_simp

/-! ### The higher entry derivatives -/

/-- `d/dt (Δ¹ G)^k = -k (Δ¹ G)^{k+1}`. -/
private lemma derivative_MD_pow {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ)
    (k : ℕ) :
    DerivMD (fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k)
      (-(k : ℂ) • (Delta i μ 1 * G Sig (Xupd A i μ x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using derivative_MD_const (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) x
  | succ k ih =>
    have hDG := derivative_MD_mul (derivative_MD_const (Delta i μ 1) x)
      (derivative_MD_G hSig A hz i μ x)
    have h := derivative_MD_mul ih hDG
    have e : (fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ (k + 1)) =
        fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k *
          (Delta i μ 1 * G Sig (Xupd A i μ y) z) :=
      funext fun y => pow_succ _ _
    rw [e]
    convert h using 1
    have e2 : Delta i μ 1 * -(G Sig (Xupd A i μ x) z * Delta i μ 1 * G Sig (Xupd A i μ x) z) =
        -((Delta i μ 1 * G Sig (Xupd A i μ x) z) * (Delta i μ 1 * G Sig (Xupd A i μ x) z)) := by
      simp [Matrix.mul_assoc]
    rw [Matrix.zero_mul, zero_add, e2, smul_mul_assoc, ← pow_succ, Matrix.mul_neg,
      ← Matrix.mul_assoc, ← pow_succ, ← pow_succ, Nat.cast_succ, neg_add, add_smul, neg_one_smul]

/-- `d/dt tr (Δ¹ G)^k = -k tr (Δ¹ G)^{k+1}`. -/
private lemma derivative_hasDerivAt_trace_pow {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y => Matrix.trace ((Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k))
      (-(k : ℂ) * Matrix.trace ((Delta i μ 1 * G Sig (Xupd A i μ x) z) ^ (k + 1))) x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
    derivative_MD_pow hSig A hz i μ x k s s
  refine h.congr_deriv ?_
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]

/-- `(Δ¹ C)_{st} = 1_{s = i} C_{μ t} + 1_{s = μ} C_{i t}`. -/
private lemma derivative_Delta_mul_apply (C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    (Delta i μ 1 * C) s t = (if s = Sum.inl i then C (Sum.inr μ) t else 0) +
      (if s = Sum.inr μ then C (Sum.inl i) t else 0) := by
  have := derivative_mul_Delta_mul (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) C i μ s t
  rw [Matrix.one_mul] at this
  rw [this]
  simp [Matrix.one_apply]

/-- `tr (Δ¹ C) = C_{μ i} + C_{i μ}`. -/
private lemma derivative_trace_Delta_mul (C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) :
    Matrix.trace (Delta i μ 1 * C) = C (Sum.inr μ) (Sum.inl i) + C (Sum.inl i) (Sum.inr μ) := by
  simp only [Matrix.trace, Matrix.diag_apply, derivative_Delta_mul_apply, Finset.sum_add_distrib]
  simp

/-- The entry-derivative coefficients: the `k`-th is `-π⁻¹ (-1)^k k! Im [tr (Δ¹ G)^{k+1}]`
between the endpoints. -/
private def derivPsi (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (η E₁ E₂ : ℝ)
    (i : Fin M) (μ : Fin N) (k : ℕ) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (((-1 : ℝ) ^ k * (k.factorial : ℝ)) *
    ((Matrix.trace ((Delta i μ 1 *
        G Sig (Xupd Xm i μ t) ((E₂ : ℂ) + η * Complex.I)) ^ (k + 1))).im -
      (Matrix.trace ((Delta i μ 1 *
        G Sig (Xupd Xm i μ t) ((E₁ : ℂ) + η * Complex.I)) ^ (k + 1))).im))

private lemma derivative_hasDerivAt_derivPsi {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (derivPsi Sig Xm η E₁ E₂ i μ k) (derivPsi Sig Xm η E₁ E₂ i μ (k + 1) x) x := by
  have hb : 0 < ((E₂ : ℂ) + η * Complex.I).im := by simpa using hη
  have ha : 0 < ((E₁ : ℂ) + η * Complex.I).im := by simpa using hη
  have h2 := derivative_hasDerivAt_im (derivative_hasDerivAt_trace_pow hSig Xm hb i μ x (k + 1))
  have h1 := derivative_hasDerivAt_im (derivative_hasDerivAt_trace_pow hSig Xm ha i μ x (k + 1))
  have h := (h2.sub h1).const_mul (-(1 / Real.pi) * ((-1 : ℝ) ^ k * (k.factorial : ℝ)))
  unfold derivPsi
  convert h using 1
  · funext t
    simp only [Pi.sub_apply]
    ring
  · have e : ∀ w : ℂ, (-((k + 1 : ℕ) : ℂ) * w).im = -((k : ℝ) + 1) * w.im := fun w => by
      simp [Complex.mul_im]
    rw [e, e]
    simp only [Nat.factorial_succ, pow_succ]
    push_cast
    ring

private lemma derivative_hasDerivAt_smCount_psi {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ)
    (i : Fin M) (μ : Fin N) (x : ℝ) :
    HasDerivAt (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂)
      (derivPsi Sig Xm η E₁ E₂ i μ 0 x) x := by
  have hb : 0 < ((E₂ : ℂ) + η * Complex.I).im := by simpa using hη
  have ha : 0 < ((E₁ : ℂ) + η * Complex.I).im := by simpa using hη
  refine (hasDerivAt_smCount hSig Xm hη E₁ E₂ i μ x).congr_deriv ?_
  have hs : ∀ {z : ℂ}, 0 < z.im → (Matrix.trace (Delta i μ 1 * G Sig (Xupd Xm i μ x) z)).im =
      2 * (G Sig (Xupd Xm i μ x) z (Sum.inr μ) (Sum.inl i)).im := by
    intro z hz
    rw [derivative_trace_Delta_mul]
    have := congrFun (congrFun (G_transpose hSig (Xupd Xm i μ x) hz) (Sum.inl i)) (Sum.inr μ)
    rw [Matrix.transpose_apply] at this
    rw [Complex.add_im, this, two_mul]
  simp only [derivPsi, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one]
  rw [hs hb, hs ha]
  ring

private lemma derivative_iteratedDeriv_eq_psi {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ)
    (i : Fin M) (μ : Fin N) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) =
      derivPsi Sig Xm η E₁ E₂ i μ n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext x
    exact (derivative_hasDerivAt_smCount_psi hSig Xm hη E₁ E₂ i μ x).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (derivative_hasDerivAt_derivPsi hSig Xm hη E₁ E₂ i μ n x).deriv

/-- The word formula for the entry derivatives of the smoothed count: the `(n+1)`-st derivative in
the entry `X_{iμ}` is `-π⁻¹ (-1)^n n! Im [tr (Δ¹ G)^{n+1}]`, taken between the endpoints
`E₁ + iη` and `E₂ + iη`, where `Δ¹ = Delta i μ 1` has entries `1` at `(i, μ)` and `(μ, i)`.
For `n = 0` this is the first-derivative formula, since `tr (Δ¹ G) = 2 G_{μi}`. -/
theorem derivative_iteratedDeriv_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) (u : ℝ) :
    iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) u =
      -(1 / Real.pi) * (((-1 : ℝ) ^ n * (n.factorial : ℝ)) *
        ((Matrix.trace ((Delta i μ 1 *
            G Sig (Xupd Xm i μ u) ((E₂ : ℂ) + η * Complex.I)) ^ (n + 1))).im -
          (Matrix.trace ((Delta i μ 1 *
            G Sig (Xupd Xm i μ u) ((E₁ : ℂ) + η * Complex.I)) ^ (n + 1))).im)) := by
  rw [derivative_iteratedDeriv_eq_psi hSig Xm hη E₁ E₂ i μ n]
  rfl

/-- The smoothed count is smooth in an entry of `X`. -/
theorem derivative_contDiff_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) :
    ContDiff ℝ n (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) := by
  have hP : ∀ m : ℕ, ∀ k : ℕ, ContDiff ℝ m (derivPsi Sig Xm η E₁ E₂ i μ k) := by
    intro m
    induction m with
    | zero =>
      intro k
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
        (derivative_hasDerivAt_derivPsi hSig Xm hη E₁ E₂ i μ k x).continuousAt)
    | succ m ih =>
      intro k
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun x => (derivative_hasDerivAt_derivPsi hSig Xm hη E₁ E₂ i μ k x).differentiableAt,
        fun h => absurd h (by simp), ?_⟩
      have : deriv (derivPsi Sig Xm η E₁ E₂ i μ k) = derivPsi Sig Xm η E₁ E₂ i μ (k + 1) :=
        funext fun x => (derivative_hasDerivAt_derivPsi hSig Xm hη E₁ E₂ i μ k x).deriv
      rw [this]
      exact ih (k + 1)
  cases n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (derivative_hasDerivAt_smCount_psi hSig Xm hη E₁ E₂ i μ x).continuousAt)
  | succ m =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (derivative_hasDerivAt_smCount_psi hSig Xm hη E₁ E₂ i μ x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) =
        derivPsi Sig Xm η E₁ E₂ i μ 0 :=
      funext fun x => (derivative_hasDerivAt_smCount_psi hSig Xm hη E₁ E₂ i μ x).deriv
    rw [this]
    exact hP m 0

/-! ### A bound on `G` uniform in `X` -/

/-- For a real vector, `x ⬝ᵥ Σ x ≤ ‖Σ‖ x ⬝ᵥ x`. -/
private lemma derivative_quad_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (x : ι → ℝ) : x ⬝ᵥ P *ᵥ x ≤ ‖P‖ * (x ⬝ᵥ x) := by
  have h1 := Matrix.l2_opNorm_mulVec P (WithLp.toLp 2 x)
  have h2 := real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 (P *ᵥ x))
  have h3 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  have h4 : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 (P *ᵥ x)) =
      x ⬝ᵥ P *ᵥ x := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [h4] at h2
  have h1' : ‖(WithLp.toLp 2 (P *ᵥ x) : EuclideanSpace ℝ ι)‖ ≤
      ‖P‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := h1
  calc x ⬝ᵥ P *ᵥ x ≤ _ := h2
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
          (‖P‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) :=
        mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
    _ = ‖P‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by ring
    _ = ‖P‖ * (x ⬝ᵥ x) := by rw [h3]

/-- `Σ⁻¹ ≥ a⁻¹` as a real quadratic form: `x ⬝ᵥ x ≤ a · x ⬝ᵥ Σ⁻¹ x` when `‖Σ‖ ≤ a`. -/
private lemma derivative_quad_inv_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Sig : Matrix ι ι ℝ} (hSig : Sig.PosDef) {a : ℝ} (ha0 : 0 < a) (ha : ‖Sig‖ ≤ a)
    (x : ι → ℝ) : x ⬝ᵥ x ≤ a * (x ⬝ᵥ Sig⁻¹ *ᵥ x) := by
  have hBpd := hSig.inv
  have hB : Sig⁻¹ᵀ = Sig⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hBpd.1.eq
  have hBS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hsym : ∀ (P : Matrix ι ι ℝ), Pᵀ = P → ∀ u w : ι → ℝ, u ⬝ᵥ P *ᵥ w = w ⬝ᵥ P *ᵥ u := by
    intro P hP u w
    rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]
  set t : ℝ := 1 / a with ht
  set y : ι → ℝ := x - t • (Sig *ᵥ x) with hy
  have hpos : 0 ≤ y ⬝ᵥ Sig⁻¹ *ᵥ y := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hBpd.posSemidef).2 y
    simpa using this
  have hBSx : Sig⁻¹ *ᵥ (Sig *ᵥ x) = x := by
    rw [mulVec_mulVec, hBS, one_mulVec]
  have e1 : x ⬝ᵥ Sig⁻¹ *ᵥ (Sig *ᵥ x) = x ⬝ᵥ x := by rw [hBSx]
  have e2 : (Sig *ᵥ x) ⬝ᵥ Sig⁻¹ *ᵥ x = x ⬝ᵥ x := by
    rw [hsym _ hB, e1]
  have e3 : (Sig *ᵥ x) ⬝ᵥ Sig⁻¹ *ᵥ (Sig *ᵥ x) = x ⬝ᵥ Sig *ᵥ x := by
    rw [hBSx, dotProduct_comm]
  have hexp : y ⬝ᵥ Sig⁻¹ *ᵥ y = x ⬝ᵥ Sig⁻¹ *ᵥ x - 2 * t * (x ⬝ᵥ x) + t ^ 2 * (x ⬝ᵥ Sig *ᵥ x) := by
    simp only [hy, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, e1, e2, e3]
    ring
  have h1 := derivative_quad_le_opNorm Sig x
  have h2 : ‖Sig‖ * (x ⬝ᵥ x) ≤ a * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right ha (by simpa using dotProduct_self_star_nonneg x)
  have h3 : t ^ 2 * (x ⬝ᵥ Sig *ᵥ x) ≤ t ^ 2 * (a * (x ⬝ᵥ x)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg t)
  have h4 : t ^ 2 * (a * (x ⬝ᵥ x)) = t * (x ⬝ᵥ x) := by
    rw [ht]; field_simp
  have h5 : 2 * t * (x ⬝ᵥ x) - t * (x ⬝ᵥ x) = (x ⬝ᵥ x) / a := by
    rw [ht]; field_simp; ring
  have : (x ⬝ᵥ x) / a ≤ x ⬝ᵥ Sig⁻¹ *ᵥ x := by linarith
  rw [div_le_iff₀ ha0] at this
  linarith

/-- Cauchy–Schwarz for a complex pairing. -/
private lemma derivative_norm_pair_le {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ s, (starRingEnd ℂ) (f s) * g s‖ ≤
      Real.sqrt (∑ s, ‖f s‖ ^ 2) * Real.sqrt (∑ s, ‖g s‖ ^ 2) := by
  calc ‖∑ s, (starRingEnd ℂ) (f s) * g s‖ ≤ ∑ s, ‖(starRingEnd ℂ) (f s) * g s‖ := norm_sum_le _ _
    _ = ∑ s, ‖f s‖ * ‖g s‖ := by simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- A complex quadratic form of a real symmetric matrix is real. -/
private lemma derivative_quad_split {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (hP : Pᵀ = P)
    (a : ι → ℂ) :
    ∑ s, (starRingEnd ℂ) (a s) * ∑ t, (P s t : ℂ) * a t =
      (((fun s => (a s).re) ⬝ᵥ P *ᵥ (fun s => (a s).re) +
        (fun s => (a s).im) ⬝ᵥ P *ᵥ (fun s => (a s).im) : ℝ) : ℂ) := by
  have hs : ∀ s t, P s t = P t s := fun s t => by
    have := congrFun (congrFun hP t) s
    simpa [Matrix.transpose_apply] using this
  have hanti : ∑ s, ∑ t, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) = 0 := by
    have h1 : ∑ s, ∑ t, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) =
        ∑ t, ∑ s, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) := Finset.sum_comm
    have h2 : ∑ t, ∑ s, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) =
        -∑ s, ∑ t, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hs s t]
      ring
    linarith
  have hre : (∑ s, (starRingEnd ℂ) (a s) * ∑ t, (P s t : ℂ) * a t).re =
      ∑ s, ∑ t, P s t * ((a s).re * (a t).re + (a s).im * (a t).im) := by
    simp only [Finset.mul_sum, Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have him : (∑ s, (starRingEnd ℂ) (a s) * ∑ t, (P s t : ℂ) * a t).im =
      ∑ s, ∑ t, P s t * ((a s).re * (a t).im - (a s).im * (a t).re) := by
    simp only [Finset.mul_sum, Complex.im_sum, Complex.mul_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  · rw [him, hanti, Complex.ofReal_im]

/-- The real inequality behind the resolvent bound. -/
private lemma derivative_energy_arith {α β ν₁ ν₂ A η zn : ℝ}
    (hν₁ : 0 ≤ ν₁) (hν₂ : 0 ≤ ν₂) (hA : 0 < A) (hη : 0 < η) (hzn : 0 ≤ zn)
    (h1 : η * β ^ 2 ≤ α * ν₁ + β * ν₂)
    (h2 : α ^ 2 ≤ A * (β * ν₂ + zn * β ^ 2 + α * ν₁)) :
    Real.sqrt (α ^ 2 + β ^ 2) ≤
      (2 * A + (A * zn + 1) / η) * Real.sqrt (ν₁ ^ 2 + ν₂ ^ 2) := by
  set w := Real.sqrt (α ^ 2 + β ^ 2) with hw
  set ν := Real.sqrt (ν₁ ^ 2 + ν₂ ^ 2) with hν
  have hw2 : w ^ 2 = α ^ 2 + β ^ 2 := Real.sq_sqrt (by positivity)
  have hν2 : ν ^ 2 = ν₁ ^ 2 + ν₂ ^ 2 := Real.sq_sqrt (by positivity)
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hαw : α ≤ w := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg β])
  have hβw : β ≤ w := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg α])
  have hν₁ν : ν₁ ≤ ν := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ν₂])
  have hν₂ν : ν₂ ≤ ν := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ν₁])
  -- Cauchy–Schwarz in the plane
  have hcs : α * ν₁ + β * ν₂ ≤ w * ν := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    rw [mul_pow, hw2, hν2]
    nlinarith [sq_nonneg (α * ν₂ - β * ν₁)]
  have hb2 : β ^ 2 ≤ w * ν / η := by
    rw [le_div_iff₀ hη]; nlinarith
  have hα2 : α ^ 2 ≤ A * (2 * (w * ν) + zn * β ^ 2) := by
    have e1 : β * ν₂ ≤ w * ν := mul_le_mul hβw hν₂ν hν₂ hw0
    have e2 : α * ν₁ ≤ w * ν := mul_le_mul hαw hν₁ν hν₁ hw0
    calc α ^ 2 ≤ A * (β * ν₂ + zn * β ^ 2 + α * ν₁) := h2
      _ ≤ A * (2 * (w * ν) + zn * β ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          linarith
  have hfin : w ^ 2 ≤ (2 * A + (A * zn + 1) / η) * ν * w := by
    have e3 : (A * zn + 1) * β ^ 2 ≤ (A * zn + 1) * (w * ν / η) :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    have e4 : (A * zn + 1) * (w * ν / η) = (A * zn + 1) / η * ν * w := by ring
    nlinarith
  by_cases hw00 : w = 0
  · rw [hw00]; positivity
  · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw00)
    nlinarith

/-- The energy estimate for `H v = u`, in blocks `v = (a, b)`, `u = (u₁, u₂)`. -/
private lemma derivative_energy {B : Matrix (Fin M) (Fin M) ℝ} (hB : Bᵀ = B)
    (Xr : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) {A : ℝ} (hA : 0 < A)
    (hB0 : ∀ x : Fin M → ℝ, 0 ≤ x ⬝ᵥ B *ᵥ x)
    (hBA : ∀ x : Fin M → ℝ, x ⬝ᵥ x ≤ A * (x ⬝ᵥ B *ᵥ x))
    (a u₁ : Fin M → ℂ) (b u₂ : Fin N → ℂ)
    (hE1 : ∀ s, u₁ s = -(∑ t, (B s t : ℂ) * a t) + ∑ ν, (Xr s ν : ℂ) * b ν)
    (hE2 : ∀ ν, u₂ ν = (∑ s, (Xr s ν : ℂ) * a s) - z * b ν) :
    Real.sqrt (∑ s, ‖a s‖ ^ 2 + ∑ ν, ‖b ν‖ ^ 2) ≤
      (2 * A + (A * ‖z‖ + 1) / z.im) *
        Real.sqrt (∑ s, ‖u₁ s‖ ^ 2 + ∑ ν, ‖u₂ ν‖ ^ 2) := by
  set α := Real.sqrt (∑ s, ‖a s‖ ^ 2) with hα
  set β := Real.sqrt (∑ ν, ‖b ν‖ ^ 2) with hβ
  set ν₁ := Real.sqrt (∑ s, ‖u₁ s‖ ^ 2) with hν₁
  set ν₂ := Real.sqrt (∑ ν, ‖u₂ ν‖ ^ 2) with hν₂
  have hα2 : α ^ 2 = ∑ s, ‖a s‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have hβ2 : β ^ 2 = ∑ ν, ‖b ν‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have hν₁2 : ν₁ ^ 2 = ∑ s, ‖u₁ s‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have hν₂2 : ν₂ ^ 2 = ∑ ν, ‖u₂ ν‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  rw [← hα2, ← hβ2, ← hν₁2, ← hν₂2]
  -- the four pairings
  set Q : ℂ := ∑ s, (starRingEnd ℂ) (a s) * ∑ t, (B s t : ℂ) * a t with hQ
  set P : ℂ := ∑ s, (starRingEnd ℂ) (a s) * ∑ ν, (Xr s ν : ℂ) * b ν with hP
  set S : ℂ := ∑ s, (starRingEnd ℂ) (a s) * u₁ s with hS
  set T : ℂ := ∑ ν, (starRingEnd ℂ) (b ν) * u₂ ν with hT
  set bb : ℂ := ∑ ν, (starRingEnd ℂ) (b ν) * b ν with hbb
  have hbbr : bb = ((β ^ 2 : ℝ) : ℂ) := by
    rw [hβ2, hbb, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have hSe : S = -Q + P := by
    rw [hS, hQ, hP, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hE1 s]
    ring
  have hcP : (starRingEnd ℂ) P = ∑ ν, ∑ s, (starRingEnd ℂ) (b ν) * ((Xr s ν : ℂ) * a s) := by
    rw [hP, map_sum]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hTe : T = (starRingEnd ℂ) P - z * bb := by
    rw [hcP, hT, hbb, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hE2 ν, mul_sub, Finset.mul_sum]
    ring
  -- `Q` is real, and `α² ≤ A Q`
  set qr : ℝ := (fun s => (a s).re) ⬝ᵥ B *ᵥ (fun s => (a s).re) +
    (fun s => (a s).im) ⬝ᵥ B *ᵥ (fun s => (a s).im) with hqr
  have hQr : Q = (qr : ℂ) := derivative_quad_split B hB a
  have hqr0 : 0 ≤ qr := add_nonneg (hB0 _) (hB0 _)
  have hαq : α ^ 2 ≤ A * qr := by
    rw [hα2, hqr, mul_add]
    have h1 := hBA (fun s => (a s).re)
    have h2 := hBA (fun s => (a s).im)
    have e : ∑ s, ‖a s‖ ^ 2 = (fun s => (a s).re) ⬝ᵥ (fun s => (a s).re) +
        (fun s => (a s).im) ⬝ᵥ (fun s => (a s).im) := by
      simp only [dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]
    linarith
  -- the imaginary part of `S + T`
  have hST : (S + T).im = -(z.im * β ^ 2) := by
    have : S + T = -Q + (P + (starRingEnd ℂ) P) - z * bb := by rw [hSe, hTe]; ring
    rw [this, hQr, hbbr, Complex.add_conj]
    simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re]
    ring
  have hS1 : ‖S‖ ≤ α * ν₁ := derivative_norm_pair_le a u₁
  have hT1 : ‖T‖ ≤ β * ν₂ := derivative_norm_pair_le b u₂
  have h1 : z.im * β ^ 2 ≤ α * ν₁ + β * ν₂ := by
    have h3 : -(S + T).im ≤ ‖S + T‖ := neg_le_abs _ |>.trans (Complex.abs_im_le_norm _)
    have h4 : ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le _ _
    rw [hST] at h3
    linarith
  have hQT : Q = (starRingEnd ℂ) T + (starRingEnd ℂ) z * bb - S := by
    have hbc : (starRingEnd ℂ) bb = bb := by rw [hbbr]; exact Complex.conj_ofReal _
    rw [hTe, map_sub, map_mul, hbc, Complex.conj_conj]
    rw [hSe]; ring
  have h2 : α ^ 2 ≤ A * (β * ν₂ + ‖z‖ * β ^ 2 + α * ν₁) := by
    have h3 : ‖Q‖ ≤ ‖T‖ + ‖z‖ * β ^ 2 + ‖S‖ := by
      rw [hQT]
      calc ‖(starRingEnd ℂ) T + (starRingEnd ℂ) z * bb - S‖
          ≤ ‖(starRingEnd ℂ) T + (starRingEnd ℂ) z * bb‖ + ‖S‖ := norm_sub_le _ _
        _ ≤ ‖(starRingEnd ℂ) T‖ + ‖(starRingEnd ℂ) z * bb‖ + ‖S‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖T‖ + ‖z‖ * β ^ 2 + ‖S‖ := by
            rw [hbbr, Complex.norm_conj, norm_mul, Complex.norm_conj, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (sq_nonneg β)]
    have h4 : ‖Q‖ = qr := by rw [hQr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hqr0]
    rw [h4] at h3
    calc α ^ 2 ≤ A * qr := hαq
      _ ≤ A * (β * ν₂ + ‖z‖ * β ^ 2 + α * ν₁) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          linarith
  exact derivative_energy_arith (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hz
    (norm_nonneg z) h1 h2

/-- `‖G(z)‖ ≤ 2a + (a|z| + 1)/Im z` for `‖Σ‖ ≤ a`, uniformly in `X`. -/
theorem derivative_norm_G_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {a : ℝ}
    (ha0 : 0 < a) (ha : ‖Sig‖ ≤ a) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖G Sig Xm z‖ ≤ 2 * a + (a * ‖z‖ + 1) / z.im := by
  have hB : Sig⁻¹ᵀ = Sig⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.inv.1.eq
  have hB0 : ∀ x : Fin M → ℝ, 0 ≤ x ⬝ᵥ Sig⁻¹ *ᵥ x := fun x => by
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.1 hSig.inv.posSemidef).2 x
  have hBA := derivative_quad_inv_ge hSig ha0 ha
  have hK : 0 ≤ 2 * a + (a * ‖z‖ + 1) / z.im := by positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun u => ?_
  set v : Fin M ⊕ Fin N → ℂ := G Sig Xm z *ᵥ u.ofLp with hv
  have hvu : H Sig Xm z *ᵥ v = u.ofLp := by
    rw [hv, mulVec_mulVec, H_mul_G hSig Xm hz, one_mulVec]
  have hE1 : ∀ s, u.ofLp (Sum.inl s) = -(∑ t, (Sig⁻¹ s t : ℂ) * v (Sum.inl t)) +
      ∑ ν, (Xm s ν : ℂ) * v (Sum.inr ν) := by
    intro s
    have := congrFun hvu (Sum.inl s)
    rw [← this]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, H, linH, cplx, Finset.sum_neg_distrib]
  have hE2 : ∀ ν, u.ofLp (Sum.inr ν) = (∑ s, (Xm s ν : ℂ) * v (Sum.inl s)) - z * v (Sum.inr ν) := by
    intro ν
    have := congrFun hvu (Sum.inr ν)
    rw [← this]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, H, linH, cplx, Matrix.one_apply]
    ring
  have h := derivative_energy hB Xm hz ha0 hB0 hBA (fun s => v (Sum.inl s))
    (fun s => u.ofLp (Sum.inl s)) (fun ν => v (Sum.inr ν)) (fun ν => u.ofLp (Sum.inr ν)) hE1 hE2
  have e1 : ‖(Matrix.toEuclideanCLM (n := Fin M ⊕ Fin N) (𝕜 := ℂ) (G Sig Xm z)) u‖ =
      Real.sqrt (∑ s, ‖v (Sum.inl s)‖ ^ 2 + ∑ ν, ‖v (Sum.inr ν)‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
    rfl
  have e2 : ‖u‖ = Real.sqrt (∑ s, ‖u.ofLp (Sum.inl s)‖ ^ 2 + ∑ ν, ‖u.ofLp (Sum.inr ν)‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  change ‖(Matrix.toEuclideanCLM (n := Fin M ⊕ Fin N) (𝕜 := ℂ) (G Sig Xm z)) u‖ ≤ _
  rw [e1, e2]
  exact h

/-- An entry of a matrix is at most its operator norm. -/
private lemma derivative_entry_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (s t : ι) : ‖A s t‖ ≤ ‖A‖ := by
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (Pi.single t (1 : ℂ)))
  have h2 : ‖(WithLp.toLp 2 (Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
    simp
  have h3 : ‖A s t‖ ≤ ‖(WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι) s
    simpa [mulVec_single_one] using this
  rw [h2, mul_one] at h1
  exact h3.trans h1

/-- The bound `‖G(E + iη)‖ ≤ (a² + 3a + 1)/η²` for `‖Σ‖ ≤ a`, `|E| ≤ a`, `0 < η ≤ 1`,
uniformly in `X`. -/
theorem derivative_norm_G_le_sq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {a : ℝ}
    (ha0 : 0 < a) (ha : ‖Sig‖ ≤ a) (Xm : Matrix (Fin M) (Fin N) ℝ) {E η : ℝ} (hE : |E| ≤ a)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ‖G Sig Xm ((E : ℂ) + η * Complex.I)‖ ≤ (a ^ 2 + 3 * a + 1) / η ^ 2 := by
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
  have h := derivative_norm_G_le hSig ha0 ha Xm hz
  have hzn : ‖(E : ℂ) + η * Complex.I‖ ≤ a + 1 := by
    calc ‖(E : ℂ) + η * Complex.I‖ ≤ ‖(E : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |E| + η := by simp [abs_of_pos hη]
      _ ≤ a + 1 := by linarith
  have him : ((E : ℂ) + η * Complex.I).im = η := by simp
  rw [him] at h
  refine h.trans ?_
  have e1 : (a * ‖(E : ℂ) + η * Complex.I‖ + 1) / η ≤ (a * (a + 1) + 1) / η :=
    div_le_div_of_nonneg_right (by nlinarith) hη.le
  have e2 : 2 * a ≤ 2 * a / η := by
    rw [le_div_iff₀ hη]; nlinarith
  have e3 : 2 * a / η + (a * (a + 1) + 1) / η = (a ^ 2 + 3 * a + 1) / η := by
    field_simp; ring
  have e4 : (a ^ 2 + 3 * a + 1) / η ≤ (a ^ 2 + 3 * a + 1) / η ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  linarith


/-- Every entry of `G(E + iη)` is at most `(a² + 3a + 1)/η²` in modulus, under the hypotheses of
the operator-norm bound. -/
theorem derivative_norm_G_entry_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {a : ℝ}
    (ha0 : 0 < a) (ha : ‖Sig‖ ≤ a) (Xm : Matrix (Fin M) (Fin N) ℝ) {E η : ℝ} (hE : |E| ≤ a)
    (hη : 0 < η) (hη1 : η ≤ 1) (s t : Fin M ⊕ Fin N) :
    ‖G Sig Xm ((E : ℂ) + η * Complex.I) s t‖ ≤ (a ^ 2 + 3 * a + 1) / η ^ 2 :=
  (derivative_entry_le_norm _ s t).trans (derivative_norm_G_le_sq hSig ha0 ha Xm hE hη hη1)

end Anisotropic

#print axioms Anisotropic.smCount_eq_integral
#print axioms Anisotropic.hasDerivAt_smCount
#print axioms Anisotropic.derivative_iteratedDeriv_smCount
#print axioms Anisotropic.derivative_contDiff_smCount
#print axioms Anisotropic.derivative_norm_G_le
#print axioms Anisotropic.derivative_norm_G_le_sq
#print axioms Anisotropic.derivative_norm_G_entry_le
