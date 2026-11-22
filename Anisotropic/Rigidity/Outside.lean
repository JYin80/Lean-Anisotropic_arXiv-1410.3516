module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Outside
public import Anisotropic.Density.Varrho
public import Anisotropic.Endpoints.Main
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.LinAlg.Spectral
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Rigidity.Gap

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 3.7 (`G_outside`) under (T_diag) with the edge hypothesis at `τ/2` only -/

/-- `Im m(E + iy) = y ∫ dϱ(x)/((x − E)² + y²)` for `y > 0` (Lemma 2.2, Definition 2.3). -/
private lemma outside_im_mFun_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E y : ℝ}
    (hy : 0 < y) :
    (mFun N σ (↑E + ↑y * Complex.I)).im =
      y * ∫ x, 1 / ((x - E) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hz : 0 < (↑E + ↑y * Complex.I : ℂ).im := by simpa using hy
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  have hres : ∀ x : ℝ, resolvent (↑E + ↑y * Complex.I : ℂ) x =
      ((x : ℂ) - (↑E + ↑y * Complex.I))⁻¹ := by
    intro x
    simp [resolvent, Ring.inverse_eq_inv']
  simp_rw [hres]
  have hne : ∀ x : ℝ, (x - E) ^ 2 + y ^ 2 ≠ 0 := fun x => by positivity
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - (↑E + ↑y * Complex.I))⁻¹) (varrho N σ) := by
    refine Integrable.of_bound (C := y⁻¹) ?_ (ae_of_all _ fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine (Complex.continuous_ofReal.sub continuous_const).inv₀ fun x h => ?_
      have := congrArg Complex.im h
      simp at this
      linarith
    · rw [norm_inv]
      have h1 : y ≤ ‖((x : ℂ) - (↑E + ↑y * Complex.I))‖ := by
        have := Complex.abs_im_le_norm ((x : ℂ) - (↑E + ↑y * Complex.I))
        simpa [abs_of_pos hy] using this
      exact inv_anti₀ hy h1
  have him := integral_im (𝕜 := ℂ) hint
  simp only [RCLike.im_to_complex] at him
  rw [← him]
  have hpt : ∀ x : ℝ, (((x : ℂ) - (↑E + ↑y * Complex.I))⁻¹).im =
      y * (1 / ((x - E) ^ 2 + y ^ 2)) := by
    intro x
    rw [Complex.inv_im, Complex.normSq_apply]
    simp
    field_simp
  simp_rw [hpt]
  exact integral_const_mul y _

/-- Below the cutoff: for `E` at distance `≥ η₁` from `supp ϱ` and `0 < η ≤ η₁`, the ratio
`Im m(E + iη)/η` is at least its value at `η₁` and at most twice it. -/
theorem im_mFun_ratio (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E η η₁ : ℝ}
    (hη : 0 < η) (hηη₁ : η ≤ η₁) (hd : η₁ ≤ Metric.infDist E (varrho N σ).support) :
    (mFun N σ (↑E + ↑η₁ * Complex.I)).im / η₁ ≤ (mFun N σ (↑E + ↑η * Complex.I)).im / η ∧
      (mFun N σ (↑E + ↑η * Complex.I)).im / η ≤
        2 * ((mFun N σ (↑E + ↑η₁ * Complex.I)).im / η₁) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hη₁ : 0 < η₁ := hη.trans_le hηη₁
  rw [outside_im_mFun_eq σ hσ hN hη, outside_im_mFun_eq σ hσ hN hη₁,
    mul_div_cancel_left₀ _ hη.ne', mul_div_cancel_left₀ _ hη₁.ne']
  have hintg : ∀ {y : ℝ}, 0 < y → Integrable (fun x : ℝ => 1 / ((x - E) ^ 2 + y ^ 2))
      (varrho N σ) := by
    intro y hy
    refine Integrable.of_bound (C := (y ^ 2)⁻¹) ?_ (ae_of_all _ fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact continuous_const.div (by fun_prop) fun x => by positivity
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
      exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg (x - E)])
  refine ⟨integral_mono (hintg hη₁) (hintg hη) fun x => ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · rw [← integral_const_mul]
    refine integral_mono_ae (hintg hη) ((hintg hη₁).const_mul 2) ?_
    filter_upwards [Measure.support_mem_ae (μ := varrho N σ)] with x hx
    have h1 : η₁ ≤ |x - E| := by
      have := Metric.infDist_le_dist_of_mem (x := E) hx
      rw [Real.dist_eq, abs_sub_comm] at this
      linarith
    have h2 : η₁ ^ 2 ≤ (x - E) ^ 2 := by
      rw [← sq_abs (x - E)]; exact pow_le_pow_left₀ hη₁.le h1 2
    rw [div_le_iff₀ (by positivity)]
    rw [show 2 * (1 / ((x - E) ^ 2 + η₁ ^ 2)) * ((x - E) ^ 2 + η ^ 2) =
      2 * ((x - E) ^ 2 + η ^ 2) / ((x - E) ^ 2 + η₁ ^ 2) by ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith


/-- `‖(λ − E − iη)⁻¹ − (λ − E − iη')⁻¹‖ ≤ 2 Im (λ − E − iη')⁻¹` when `0 < η ≤ η' ≤ |λ − E|`. -/
private lemma outside_term_le {l E η η' : ℝ} (hη : 0 < η) (hηη' : η ≤ η') (hgap : η' ≤ |l - E|) :
    ‖((l : ℂ) - (↑E + ↑η * Complex.I))⁻¹ - ((l : ℂ) - (↑E + ↑η' * Complex.I))⁻¹‖ ≤
      2 * (((l : ℂ) - (↑E + ↑η' * Complex.I))⁻¹).im := by
  have hη' : 0 < η' := hη.trans_le hηη'
  set a : ℂ := (l : ℂ) - (↑E + ↑η * Complex.I) with ha
  set b : ℂ := (l : ℂ) - (↑E + ↑η' * Complex.I) with hb
  have hna : ‖a‖ ^ 2 = (l - E) ^ 2 + η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [ha]; ring
  have hnb : ‖b‖ ^ 2 = (l - E) ^ 2 + η' ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hb]; ring
  have ha0 : 0 < ‖a‖ := by
    have : 0 < ‖a‖ ^ 2 := by rw [hna]; positivity
    exact lt_of_le_of_ne (norm_nonneg a) fun h => by rw [← h] at this; simp at this
  have hb0 : 0 < ‖b‖ := by
    have : 0 < ‖b‖ ^ 2 := by rw [hnb]; positivity
    exact lt_of_le_of_ne (norm_nonneg b) fun h => by rw [← h] at this; simp at this
  have ha0' : a ≠ 0 := norm_pos_iff.1 ha0
  have hb0' : b ≠ 0 := norm_pos_iff.1 hb0
  have hdiff : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  have hba : b - a = ((η - η' : ℝ) : ℂ) * Complex.I := by
    rw [ha, hb]; push_cast; ring
  have him : (b⁻¹).im = η' / ‖b‖ ^ 2 := by
    rw [Complex.inv_im, Complex.normSq_eq_norm_sq]; simp [hb]
  rw [hdiff, him, norm_div, norm_mul, hba, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [div_le_iff₀ (by positivity)]
  have hgap2 : η' ^ 2 ≤ (l - E) ^ 2 := by
    rw [← sq_abs (l - E)]; exact pow_le_pow_left₀ hη'.le hgap 2
  -- reduce to `(η' − η) ‖b‖ ≤ 2 η' ‖a‖`, then square
  have key : (η' - η) * ‖b‖ ≤ 2 * η' * ‖a‖ := by
    have h1 : ((η' - η) * ‖b‖) ^ 2 ≤ (2 * η' * ‖a‖) ^ 2 := by
      rw [mul_pow, mul_pow, hna, hnb]
      have h3 : (η' - η) ^ 2 ≤ η' ^ 2 := by nlinarith
      have h4 : (l - E) ^ 2 + η' ^ 2 ≤ 2 * ((l - E) ^ 2 + η ^ 2) := by nlinarith
      calc (η' - η) ^ 2 * ((l - E) ^ 2 + η' ^ 2) ≤ η' ^ 2 * (2 * ((l - E) ^ 2 + η ^ 2)) :=
            mul_le_mul h3 h4 (by positivity) (by positivity)
        _ ≤ (2 * η') ^ 2 * ((l - E) ^ 2 + η ^ 2) := by nlinarith [sq_nonneg η', sq_nonneg (l - E)]
    exact (pow_le_pow_iff_left₀ (by nlinarith) (by positivity) two_ne_zero).1 h1
  calc η' - η = (η' - η) * ‖b‖ / ‖b‖ := by field_simp
    _ ≤ 2 * η' * ‖a‖ / ‖b‖ := by gcongr
    _ = 2 * (η' / ‖b‖ ^ 2) * (‖a‖ * ‖b‖) := by field_simp

/-- The termwise comparison in the spectral decomposition (decompfullG): if every `λ_k` is at
distance `≥ η'` from `E` and `0 < η ≤ η'`, then
`|∑_k ((λ_k − z)⁻¹ − (λ_k − z')⁻¹) a_k b_k| ≤ 2 (∑_k a_k² Im (λ_k − z')⁻¹)^{1/2}
(∑_k b_k² Im (λ_k − z')⁻¹)^{1/2}` for `z = E + iη`, `z' = E + iη'`. -/
theorem resolvent_compare {K : ℕ} (lam a b : Fin K → ℝ) {E η η' : ℝ} (hη : 0 < η)
    (hηη' : η ≤ η') (hgap : ∀ k, η' ≤ |lam k - E|) :
    ‖∑ k, (((lam k : ℂ) - (↑E + ↑η * Complex.I))⁻¹ - ((lam k : ℂ) - (↑E + ↑η' * Complex.I))⁻¹) *
        ((a k * b k : ℝ) : ℂ)‖ ≤
      2 * √(∑ k, a k ^ 2 * (((lam k : ℂ) - (↑E + ↑η' * Complex.I))⁻¹).im) *
        √(∑ k, b k ^ 2 * (((lam k : ℂ) - (↑E + ↑η' * Complex.I))⁻¹).im) := by
  set w : Fin K → ℝ := fun k => (((lam k : ℂ) - (↑E + ↑η' * Complex.I))⁻¹).im with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    have := (norm_nonneg _).trans (outside_term_le hη hηη' (hgap k))
    simp only [hw]; linarith
  calc _ ≤ ∑ k, ‖(((lam k : ℂ) - (↑E + ↑η * Complex.I))⁻¹ -
          ((lam k : ℂ) - (↑E + ↑η' * Complex.I))⁻¹) * ((a k * b k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k, 2 * ((√(w k) * |a k|) * (√(w k) * |b k|)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 := outside_term_le hη hηη' (hgap k)
        have h2 : √(w k) * |a k| * (√(w k) * |b k|) = w k * (|a k| * |b k|) := by
          rw [show √(w k) * |a k| * (√(w k) * |b k|) = (√(w k) * √(w k)) * (|a k| * |b k|) by
            ring, Real.mul_self_sqrt (hw0 k)]
        rw [h2]
        calc _ ≤ 2 * w k * (|a k| * |b k|) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = _ := by ring
    _ = 2 * ∑ k, (√(w k) * |a k|) * (√(w k) * |b k|) := by rw [Finset.mul_sum]
    _ ≤ 2 * (√(∑ k, (√(w k) * |a k|) ^ 2) * √(∑ k, (√(w k) * |b k|) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by norm_num)
    _ = _ := by
        have e : ∀ c : Fin K → ℝ, ∑ k, (√(w k) * |c k|) ^ 2 = ∑ k, c k ^ 2 * w k := fun c =>
          Finset.sum_congr rfl fun k _ => by rw [mul_pow, Real.sq_sqrt (hw0 k), sq_abs]; ring
        rw [e a, e b]
        ring


/-- `⟨v, A w⟩ = ∑_{s,t} v_s A_{st} w_t`. -/
private lemma outside_tB_expand {ι : Type*} [Fintype ι] (v w : ι → ℝ) (A : Matrix ι ι ℂ) :
    testBilin v A w = ∑ s, ∑ t, (v s : ℂ) * A s t * (w t : ℂ) := by
  unfold testBilin
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- The diagonal of `Π` for `Σ = diag(σ)`: `(m_1, …, m_M, m, …, m)` with
`m_i = −σ_i/(1 + σ_i m)` ((def_Pi)). -/
private def outsidePd (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : Fin M ⊕ Fin N → ℂ :=
  Sum.elim (fun i => -(σ i : ℂ) / (1 + σ i * mFun N σ z)) fun _ => mFun N σ z

private lemma outside_PiDiag_eq (σ : Fin M → ℝ) (z : ℂ) :
    PiDiag N σ z = diagonal (outsidePd N σ z) := by
  unfold PiDiag outsidePd
  rw [smul_one_eq_diagonal, fromBlocks_diagonal]

/-- The eigenvector `y_k = Σ̲ J ζ_k` of (decompfullG) for `Σ = diag(σ)`. -/
private def outsideY {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (k : Fin N) : Fin M ⊕ Fin N → ℝ :=
  SigU (n := Fin N) (diagonal σ) *ᵥ Jmat Xm *ᵥ
    ((XSX_isHermitian (posDef_diagonal_iff.2 hσ).1 Xm).eigenvectorBasis k).ofLp

/-- The eigenvalues `λ_k` of `Xᵀ diag(σ) X`. -/
private def outsideLam {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (k : Fin N) : ℝ :=
  (XSX_isHermitian (posDef_diagonal_iff.2 hσ).1 Xm).eigenvalues k

/-- The coefficient `⟨Σ̲⁻¹ v, y_k⟩`. -/
private def outsideCoef {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ s, v s * outsideY hσ Xm k s / sigS (N := N) σ s

/-- The spectral representation of `⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ w⟩` for `Σ = diag(σ)` ((decompfullG)):
a real constant, plus `∑_k (λ_k − z)⁻¹ a_k b_k`, minus the `Π` part. -/
private lemma outside_rep {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (v w : Fin M ⊕ Fin N → ℝ) :
    testBilin v (lawMat (diagonal σ) Xm z) w =
      -((∑ s, ∑ t, v s * (fromBlocks (diagonal σ) 0 0 (0 : Matrix (Fin N) (Fin N) ℝ)) s t * w t /
          (sigS (N := N) σ s * sigS (N := N) σ t) : ℝ) : ℂ) +
        ∑ k, ((outsideLam hσ Xm k : ℂ) - z)⁻¹ *
          ((outsideCoef hσ Xm v k * outsideCoef hσ Xm w k : ℝ) : ℂ) -
        ∑ s, ((v s * w s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) * outsidePd N σ z s := by
  have hS : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  set ς := sigS (N := N) σ with hς
  have hς0 : ∀ s, (ς s : ℂ) ≠ 0 := by
    intro s
    cases s with
    | inl i => simpa [hς, sigS] using (hσ i).ne'
    | inr μ => simp [hς, sigS]
  have hent : ∀ s t, lawMat (diagonal σ) Xm z s t =
      (G (diagonal σ) Xm z s t - PiDiag N σ z s t) / ((ς s : ℂ) * ς t) := by
    intro s t
    unfold lawMat
    rw [piMat_diagonal (fun i => (hσ i).le) hz, ← wEnt_eq hσ]
    rfl
  have hG : ∀ s t, G (diagonal σ) Xm z s t =
      -((fromBlocks (diagonal σ) 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) s t : ℝ) : ℂ) +
        ∑ k, ((outsideLam hσ Xm k : ℂ) - z)⁻¹ *
          ((outsideY hσ Xm k s : ℂ) * (outsideY hσ Xm k t : ℂ)) := by
    intro s t
    rw [decompfullG_spec hS Xm hz]
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    rfl
  have hP : ∀ s t, PiDiag N σ z s t = if s = t then outsidePd N σ z s else 0 := by
    intro s t
    rw [outside_PiDiag_eq, diagonal_apply]
  rw [outside_tB_expand]
  simp only [hent, hG, hP]
  obtain ⟨D, hD⟩ : ∃ D : Fin M ⊕ Fin N → Fin M ⊕ Fin N → ℝ,
      D = fromBlocks (diagonal σ) 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) := ⟨_, rfl⟩
  rw [← hD]
  obtain ⟨y, hy⟩ : ∃ y : Fin N → Fin M ⊕ Fin N → ℝ, y = outsideY hσ Xm := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin N → ℂ, r = fun k => ((outsideLam hσ Xm k : ℂ) - z)⁻¹ := ⟨_, rfl⟩
  have hr' : ∀ k, ((outsideLam hσ Xm k : ℂ) - z)⁻¹ = r k := fun k => by rw [hr]
  simp only [← hy, hr']
  unfold outsideCoef
  rw [← hy]
  have e1 : ∀ s t, (v s : ℂ) * ((-((D s t : ℝ) : ℂ) + ∑ k, r k * ((y k s : ℂ) * (y k t : ℂ)) -
      (if s = t then outsidePd N σ z s else 0)) / ((ς s : ℂ) * ς t)) * (w t : ℂ) =
      -(((v s * D s t * w t / (ς s * ς t) : ℝ) : ℂ)) +
        ∑ k, r k * (((v s * y k s / ς s : ℝ) : ℂ) * ((w t * y k t / ς t : ℝ) : ℂ)) -
        (if s = t then ((v s * w s / ς s ^ 2 : ℝ) : ℂ) * outsidePd N σ z s else 0) := by
    intro s t
    have h1 := hς0 s
    have h2 := hς0 t
    split_ifs with hst
    · subst hst
      push_cast
      rw [sub_div, add_div, Finset.sum_div]
      simp only [mul_add, mul_sub, add_mul, sub_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · congr 1
        · field_simp
        · refine Finset.sum_congr rfl fun k _ => ?_
          field_simp
      · field_simp
    · push_cast
      simp only [sub_zero]
      rw [add_div, Finset.sum_div]
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  congr 1
  · push_cast
    rfl
  · rw [Finset.sum_congr rfl fun s _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]

/-- `Im(−σ/(1 + σm)) = σ² Im m/|1 + σm|²`. -/
private lemma outside_im_pd (s : ℝ) (m : ℂ) :
    (-(s : ℂ) / (1 + s * m)).im = s ^ 2 * m.im / ‖(1 : ℂ) + s * m‖ ^ 2 := by
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im, ← Complex.normSq_eq_norm_sq]
  simp
  ring

/-- The `Π` part of the imaginary part of `⟨v, Σ̲⁻¹ G Σ̲⁻¹ v⟩`, per coordinate: at most
`c⁻² Im m v_s²` when `|1 + σ_i m| ≥ c`, `0 < c ≤ 1`. -/
private lemma outside_pd_im_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {z : ℂ} (hz : 0 < z.im)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (v : Fin M ⊕ Fin N → ℝ) (s : Fin M ⊕ Fin N) :
    v s * v s / sigS (N := N) σ s ^ 2 * (outsidePd N σ z s).im ≤
      c⁻¹ ^ 2 * (mFun N σ z).im * v s ^ 2 := by
  have hm := (mFun_spec N σ (fun i => (hσ i).le) hz).1
  have hc2 : 1 ≤ c⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hc |>.2 hc1)
  cases s with
  | inl i =>
    simp only [sigS, Sum.elim_inl, outsidePd]
    rw [outside_im_pd]
    have hσi := hσ i
    have hn := hcz i
    have hn2 : c ^ 2 ≤ ‖(1 : ℂ) + σ i * mFun N σ z‖ ^ 2 := pow_le_pow_left₀ hc.le hn 2
    have hpos : 0 < ‖(1 : ℂ) + σ i * mFun N σ z‖ ^ 2 := lt_of_lt_of_le (by positivity) hn2
    rw [show v (Sum.inl i) * v (Sum.inl i) / σ i ^ 2 *
        (σ i ^ 2 * (mFun N σ z).im / ‖(1 : ℂ) + σ i * mFun N σ z‖ ^ 2) =
        (mFun N σ z).im * v (Sum.inl i) ^ 2 / ‖(1 : ℂ) + σ i * mFun N σ z‖ ^ 2 by
      field_simp]
    rw [div_le_iff₀ hpos, inv_pow]
    calc (mFun N σ z).im * v (Sum.inl i) ^ 2 =
        (c ^ 2)⁻¹ * (mFun N σ z).im * v (Sum.inl i) ^ 2 * c ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn2 (by positivity)
  | inr μ =>
    simp only [sigS, Sum.elim_inr, outsidePd]
    nlinarith [sq_nonneg (v (Sum.inr μ)), mul_nonneg (sq_nonneg (v (Sum.inr μ))) hm.le]

/-- The `Π` difference per coordinate: `|v_s w_s| ‖Δπ_s‖/σ̲_s² ≤ c⁻² |m − m'| |v_s| |w_s|`. -/
private lemma outside_pd_diff_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {z z' : ℂ}
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hcz' : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z'‖) (v w : Fin M ⊕ Fin N → ℝ)
    (s : Fin M ⊕ Fin N) :
    ‖((v s * w s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) * (outsidePd N σ z s - outsidePd N σ z' s)‖ ≤
      c⁻¹ ^ 2 * ‖mFun N σ z - mFun N σ z'‖ * (|v s| * |w s|) := by
  have hc2 : 1 ≤ c⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hc |>.2 hc1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  cases s with
  | inl i =>
    simp only [sigS, Sum.elim_inl, outsidePd]
    set m := mFun N σ z
    set m' := mFun N σ z'
    have hq : (1 : ℂ) + σ i * m ≠ 0 := by
      intro h; have := hcz i; rw [h, norm_zero] at this; linarith
    have hq' : (1 : ℂ) + σ i * m' ≠ 0 := by
      intro h; have := hcz' i; rw [h, norm_zero] at this; linarith
    have hσi := hσ i
    have e : -(σ i : ℂ) / (1 + σ i * m) - -(σ i : ℂ) / (1 + σ i * m') =
        (σ i : ℂ) ^ 2 * (m - m') / ((1 + σ i * m) * (1 + σ i * m')) := by
      field_simp; ring
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσi]
    have hn := hcz i
    have hn' := hcz' i
    have hden : c * c ≤ ‖(1 : ℂ) + σ i * m‖ * ‖(1 : ℂ) + σ i * m'‖ :=
      mul_le_mul hn hn' hc.le (hc.le.trans hn)
    have hpos : 0 < ‖(1 : ℂ) + σ i * m‖ * ‖(1 : ℂ) + σ i * m'‖ :=
      lt_of_lt_of_le (by positivity) hden
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < σ i ^ 2)]
    rw [show |v (Sum.inl i)| * |w (Sum.inl i)| / σ i ^ 2 *
        (σ i ^ 2 * ‖m - m'‖ / (‖(1 : ℂ) + σ i * m‖ * ‖(1 : ℂ) + σ i * m'‖)) =
        |v (Sum.inl i)| * |w (Sum.inl i)| * ‖m - m'‖ /
          (‖(1 : ℂ) + σ i * m‖ * ‖(1 : ℂ) + σ i * m'‖) by field_simp]
    rw [div_le_iff₀ hpos, inv_pow]
    calc |v (Sum.inl i)| * |w (Sum.inl i)| * ‖m - m'‖ =
        (c ^ 2)⁻¹ * ‖m - m'‖ * (|v (Sum.inl i)| * |w (Sum.inl i)|) * (c * c) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  | inr μ =>
    simp only [sigS, Sum.elim_inr, outsidePd, one_pow, div_one, abs_mul]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (v (Sum.inr μ))) (abs_nonneg (w (Sum.inr μ))))
      (norm_nonneg (mFun N σ z - mFun N σ z'))]

/-- The comparison `z ↔ z'` at fixed `X` for `Σ = diag(σ)`: with `z = E + iη`, `z' = E + iη'`,
`0 < η ≤ η'`, every eigenvalue of `Xᵀ Σ X` at distance `≥ η'` from `E`, and `|1 + σ_i m| ≥ c`
at `z` and `z'` (`0 < c ≤ 1`),
`|⟨v,B(z)w⟩| ≤ |⟨v,B(z')w⟩| + 2 (|⟨v,B(z')v⟩| + c⁻² Im m(z')|v|²)^{1/2}
(|⟨w,B(z')w⟩| + c⁻² Im m(z')|w|²)^{1/2} + c⁻² |m(z) − m(z')| |v| |w|`,
`B = Σ̲⁻¹(G − Π)Σ̲⁻¹` ((decompfullG)). -/
private lemma outside_det_diag {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {E η η' c : ℝ} (hη : 0 < η) (hηη' : η ≤ η')
    (hgap : ∀ k, η' ≤ |specOf (QN (diagonal σ) Xm) k - E|) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑η * Complex.I)‖)
    (hcz' : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑η' * Complex.I)‖)
    (v w : Fin M ⊕ Fin N → ℝ) :
    ‖testBilin v (lawMat (diagonal σ) Xm (↑E + ↑η * Complex.I)) w‖ ≤
      ‖testBilin v (lawMat (diagonal σ) Xm (↑E + ↑η' * Complex.I)) w‖ +
        2 * √(‖testBilin v (lawMat (diagonal σ) Xm (↑E + ↑η' * Complex.I)) v‖ +
            c⁻¹ ^ 2 * (mFun N σ (↑E + ↑η' * Complex.I)).im * testNorm v ^ 2) *
          √(‖testBilin w (lawMat (diagonal σ) Xm (↑E + ↑η' * Complex.I)) w‖ +
            c⁻¹ ^ 2 * (mFun N σ (↑E + ↑η' * Complex.I)).im * testNorm w ^ 2) +
        c⁻¹ ^ 2 * ‖mFun N σ (↑E + ↑η * Complex.I) - mFun N σ (↑E + ↑η' * Complex.I)‖ *
          (testNorm v * testNorm w) := by
  have hη' : 0 < η' := hη.trans_le hηη'
  set z : ℂ := ↑E + ↑η * Complex.I with hzdef
  set z' : ℂ := ↑E + ↑η' * Complex.I with hz'def
  have hz : 0 < z.im := by simpa [hzdef] using hη
  have hz' : 0 < z'.im := by simpa [hz'def] using hη'
  have hlam : ∀ k, outsideLam hσ Xm k = specOf (QN (diagonal σ) Xm) k := by
    intro k
    rw [QN, specOf_eq (XSX_isHermitian (posDef_diagonal_iff.2 hσ).1 Xm)]
    rfl
  obtain ⟨lam, hlamdef⟩ : ∃ lam : Fin N → ℝ, lam = outsideLam hσ Xm := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin N → ℝ, a = outsideCoef hσ Xm v := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N → ℝ, b = outsideCoef hσ Xm w := ⟨_, rfl⟩
  have hgap' : ∀ k, η' ≤ |lam k - E| := fun k => by rw [hlamdef, hlam]; exact hgap k
  -- the three representations
  have rz := outside_rep hσ Xm hz v w
  have rz' := outside_rep hσ Xm hz' v w
  have rvv := outside_rep hσ Xm hz' v v
  have rww := outside_rep hσ Xm hz' w w
  rw [← hlamdef, ← ha, ← hb] at rz rz'
  rw [← hlamdef] at rvv rww
  set Fz := testBilin v (lawMat (diagonal σ) Xm z) w
  set Fz' := testBilin v (lawMat (diagonal σ) Xm z') w
  set Fvv := testBilin v (lawMat (diagonal σ) Xm z') v
  set Fww := testBilin w (lawMat (diagonal σ) Xm z') w
  -- the difference
  have hdiff : Fz - Fz' = ∑ k, (((lam k : ℂ) - z)⁻¹ - ((lam k : ℂ) - z')⁻¹) *
        ((a k * b k : ℝ) : ℂ) -
      ∑ s, ((v s * w s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) *
        (outsidePd N σ z s - outsidePd N σ z' s) := by
    rw [rz, rz']
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  -- the imaginary parts
  have himS : ∀ (u : Fin M ⊕ Fin N → ℝ) (F : ℂ), F = -((∑ s, ∑ t, u s *
      (fromBlocks (diagonal σ) 0 0 (0 : Matrix (Fin N) (Fin N) ℝ)) s t * u t /
        (sigS (N := N) σ s * sigS (N := N) σ t) : ℝ) : ℂ) +
        ∑ k, ((lam k : ℂ) - z')⁻¹ * ((outsideCoef hσ Xm u k * outsideCoef hσ Xm u k : ℝ) : ℂ) -
        ∑ s, ((u s * u s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) * outsidePd N σ z' s →
      ∑ k, outsideCoef hσ Xm u k ^ 2 * (((lam k : ℂ) - z')⁻¹).im ≤
        ‖F‖ + c⁻¹ ^ 2 * (mFun N σ z').im * testNorm u ^ 2 := by
    intro u F hF
    have hS : ∑ k, outsideCoef hσ Xm u k ^ 2 * (((lam k : ℂ) - z')⁻¹).im =
        F.im + ∑ s, u s * u s / sigS (N := N) σ s ^ 2 * (outsidePd N σ z' s).im := by
      rw [hF]
      simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
        zero_add, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, mul_zero, add_zero,
        zero_mul]
      rw [sub_add_cancel]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hS]
    have h1 : F.im ≤ ‖F‖ := Complex.im_le_norm F
    have h2 : ∑ s, u s * u s / sigS (N := N) σ s ^ 2 * (outsidePd N σ z' s).im ≤
        c⁻¹ ^ 2 * (mFun N σ z').im * testNorm u ^ 2 := by
      rw [testNorm, Real.sq_sqrt (Finset.sum_nonneg fun s _ => sq_nonneg (u s)), Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => outside_pd_im_le hσ hz' hc hc1 hcz' u s
    linarith
  have hva := himS v Fvv rvv
  have hwb := himS w Fww rww
  -- the spectral sum
  have hsum := resolvent_compare lam a b hη hηη' hgap'
  -- the `Π` difference
  have hpi : ‖∑ s, ((v s * w s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) *
      (outsidePd N σ z s - outsidePd N σ z' s)‖ ≤
      c⁻¹ ^ 2 * ‖mFun N σ z - mFun N σ z'‖ * (testNorm v * testNorm w) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun s _ => outside_pd_diff_le hσ hc hc1 hcz hcz' v w s).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun s => |v s|) (fun s => |w s|)
    simpa only [sq_abs, testNorm] using this
  calc ‖Fz‖ = ‖Fz' + (Fz - Fz')‖ := by rw [add_sub_cancel]
    _ ≤ ‖Fz'‖ + ‖Fz - Fz'‖ := norm_add_le _ _
    _ ≤ ‖Fz'‖ + (‖∑ k, (((lam k : ℂ) - z)⁻¹ - ((lam k : ℂ) - z')⁻¹) * ((a k * b k : ℝ) : ℂ)‖ +
        ‖∑ s, ((v s * w s / sigS (N := N) σ s ^ 2 : ℝ) : ℂ) *
          (outsidePd N σ z s - outsidePd N σ z' s)‖) := by
        rw [hdiff]; gcongr; exact norm_sub_le _ _
    _ ≤ _ := by
        have h3 : 2 * √(∑ k, a k ^ 2 * (((lam k : ℂ) - z')⁻¹).im) *
            √(∑ k, b k ^ 2 * (((lam k : ℂ) - z')⁻¹).im) ≤
            2 * √(‖Fvv‖ + c⁻¹ ^ 2 * (mFun N σ z').im * testNorm v ^ 2) *
              √(‖Fww‖ + c⁻¹ ^ 2 * (mFun N σ z').im * testNorm w ^ 2) := by
          gcongr
          · rw [ha]; exact hva
          · rw [hb]; exact hwb
        linarith

/-- `Uᵀ` is orthogonal with `U`. -/
private lemma outside_transpose_mem {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin K) ℝ) : Uᵀ ∈ Matrix.orthogonalGroup (Fin K) ℝ :=
  (Matrix.mem_orthogonalGroup_iff _ _).2 (by
    rw [transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hU)

/-- The comparison `z ↔ z'` of `outside_det_diag` for a general `Σ > 0`, through the rotation
`Uᵀ Σ U = diag(σ)` ((rotation of matrix)). -/
private lemma outside_det {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {E η η' c : ℝ} (hη : 0 < η) (hηη' : η ≤ η')
    (hgap : ∀ k, η' ≤ |specOf (QN Sig Xm) k - E|) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcz : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) (↑E + ↑η * Complex.I)‖)
    (hcz' : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) (↑E + ↑η' * Complex.I)‖)
    (v w : Fin M ⊕ Fin N → ℝ) :
    ‖testBilin v (lawMat Sig Xm (↑E + ↑η * Complex.I)) w‖ ≤
      ‖testBilin v (lawMat Sig Xm (↑E + ↑η' * Complex.I)) w‖ +
        2 * √(‖testBilin v (lawMat Sig Xm (↑E + ↑η' * Complex.I)) v‖ +
            c⁻¹ ^ 2 * (mFun N (specOf Sig) (↑E + ↑η' * Complex.I)).im * testNorm v ^ 2) *
          √(‖testBilin w (lawMat Sig Xm (↑E + ↑η' * Complex.I)) w‖ +
            c⁻¹ ^ 2 * (mFun N (specOf Sig) (↑E + ↑η' * Complex.I)).im * testNorm w ^ 2) +
        c⁻¹ ^ 2 * ‖mFun N (specOf Sig) (↑E + ↑η * Complex.I) -
          mFun N (specOf Sig) (↑E + ↑η' * Complex.I)‖ * (testNorm v * testNorm w) := by
  obtain ⟨U, hU, hUD⟩ := exists_orth_diag hSig.1
  have hσ : ∀ i, 0 < specOf Sig i := fun i => by
    rw [specOf_eq hSig.1]; exact hSig.eigenvalues_pos i
  have hUT := outside_transpose_mem hU
  have hON : (1 : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.orthogonalGroup (Fin N) ℝ := one_mem _
  set Q := blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ) with hQ
  have hQm : Q ∈ Matrix.orthogonalGroup (Fin M ⊕ Fin N) ℝ := blockQ_mem hUT hON
  have hQQ : (cplx Q)ᵀ * cplx Q = 1 := by
    rw [← cplx_transpose, ← cplx_mul, (Matrix.mem_orthogonalGroup_iff' _ _).1 hQm, cplx_one]
  set Xd := Uᵀ * Xm * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ with hXd
  have hrot : ∀ z, lawMat Sig Xm z = (cplx Q)ᵀ * lawMat (diagonal (specOf Sig)) Xd z * cplx Q := by
    intro z
    have e := lawMat_rotate hUT hON Sig Xm z
    rw [transpose_transpose, hUD] at e
    rw [← e]
    change _ = (cplx Q)ᵀ * (cplx Q * lawMat Sig Xm z * (cplx Q)ᵀ) * cplx Q
    calc lawMat Sig Xm z = 1 * lawMat Sig Xm z * 1 := by simp
      _ = _ := by rw [← hQQ]; simp only [Matrix.mul_assoc]
  have hB : ∀ z (u u' : Fin M ⊕ Fin N → ℝ), testBilin u (lawMat Sig Xm z) u' =
      testBilin (Q *ᵥ u) (lawMat (diagonal (specOf Sig)) Xd z) (Q *ᵥ u') := by
    intro z u u'
    rw [hrot, testBilin_conj]
  have hQN : QN (diagonal (specOf Sig)) Xd = QN Sig Xm := by
    have hUU : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
    have hS : U * diagonal (specOf Sig) * Uᵀ = Sig := by
      rw [← hUD]
      calc U * (Uᵀ * Sig * U) * Uᵀ = (U * Uᵀ) * Sig * (U * Uᵀ) := by simp only [Matrix.mul_assoc]
        _ = Sig := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    unfold QN
    rw [hXd, transpose_one, Matrix.mul_one, transpose_mul, transpose_transpose]
    conv_rhs => rw [← hS]
    simp only [Matrix.mul_assoc]
  have h := outside_det_diag hσ Xd hη hηη' (by rw [hQN]; exact hgap) hc hc1 hcz hcz'
    (Q *ᵥ v) (Q *ᵥ w)
  rw [testNorm_orth hQm, testNorm_orth hQm] at h
  simp only [hB]
  exact h

/-- `x ↦ (x − z)⁻¹` is `ϱ`-integrable for `Im z > 0`. -/
private lemma outside_integrable_inv (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) (varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  refine Integrable.of_bound (C := z.im⁻¹) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (Complex.continuous_ofReal.sub continuous_const).inv₀ fun x h => ?_
    have := congrArg Complex.im h
    simp at this
    linarith
  · rw [norm_inv]
    have h1 : z.im ≤ ‖((x : ℂ) - z)‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) - z)
      simpa [abs_of_pos hz] using this
    exact inv_anti₀ hz h1

/-- `m(z) = ∫ dϱ(x)/(x − z)` (Lemma 2.2, Definition 2.3). -/
private lemma outside_mFun_eq_integral (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) : mFun N σ z = ∫ x, ((x : ℂ) - z)⁻¹ ∂(varrho N σ) := by
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

/-- `|m(E + iη) − m(E + iη')| ≤ 2 Im m(E + iη')` for `0 < η ≤ η' ≤ dist(E, supp ϱ)`. -/
private lemma outside_mFun_diff_le (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {E η η' : ℝ} (hη : 0 < η) (hηη' : η ≤ η')
    (hd : η' ≤ Metric.infDist E (varrho N σ).support) :
    ‖mFun N σ (↑E + ↑η * Complex.I) - mFun N σ (↑E + ↑η' * Complex.I)‖ ≤
      2 * (mFun N σ (↑E + ↑η' * Complex.I)).im := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hη' : 0 < η' := hη.trans_le hηη'
  have hz : 0 < (↑E + ↑η * Complex.I : ℂ).im := by simpa using hη
  have hz' : 0 < (↑E + ↑η' * Complex.I : ℂ).im := by simpa using hη'
  have hf := outside_integrable_inv σ hσ hN hz
  have hg := outside_integrable_inv σ hσ hN hz'
  rw [outside_mFun_eq_integral σ hσ hN hz, outside_mFun_eq_integral σ hσ hN hz',
    ← integral_sub hf hg]
  refine (norm_integral_le_integral_norm _).trans ?_
  have him := integral_im (𝕜 := ℂ) hg
  simp only [RCLike.im_to_complex] at him
  rw [← him, ← integral_const_mul]
  refine integral_mono_ae (hf.sub hg).norm ((hg.im).const_mul 2) ?_
  filter_upwards [Measure.support_mem_ae (μ := varrho N σ)] with x hx
  have h1 : η' ≤ |x - E| := by
    have := Metric.infDist_le_dist_of_mem (x := E) hx
    rw [Real.dist_eq, abs_sub_comm] at this
    linarith
  exact outside_term_le hη hηη' h1

/-- An edge `a_l > 0` lies in `supp ϱ` (Lemma 2.6). -/
private lemma outside_edge_mem_support (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands N σ)
    (hpos : 0 < edgeVal N σ l) : edgeVal N σ l ∈ (varrho N σ).support := by
  rw [mem_support_varrho_iff N σ hσ hN hS hpos]
  rcases Nat.even_or_odd l with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hle := (edgeVal_band_lt N σ hσ hN hS (k := k) (by omega) (by omega)).le
    refine ⟨k, by omega, by omega, ?_, ?_⟩
    · rw [hk, show k + k = 2 * k by ring]
    · rw [hk, show k + k = 2 * k by ring]; exact hle
  · have hle := (edgeVal_band_lt N σ hσ hN hS (k := k + 1) (by omega) (by omega)).le
    refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
    · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hle; rw [hk]; exact hle
    · rw [hk, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

/-- `κ(E) ≥ min(dist(E, supp ϱ), E)` for `E > 0`. -/
private lemma outside_kappa_ge (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : 0 < E) :
    min (Metric.infDist E (varrho N σ).support) E ≤ kappa N σ E := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  have hne : Nonempty (Finset.Icc 1 (2 * numBands N σ)) :=
    ⟨⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩⟩
  unfold kappa
  refine le_ciInf fun l => ?_
  obtain ⟨l, hl⟩ := l
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hl
  rcases lt_or_ge 0 (edgeVal N σ l) with hpos | hnpos
  · have hmem := outside_edge_mem_support σ hσ hN hS hl1 hl2 hpos
    have := Metric.infDist_le_dist_of_mem (x := E) hmem
    rw [Real.dist_eq] at this
    exact (min_le_left _ _).trans this
  · refine (min_le_right _ _).trans ?_
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- `dist(E, supp ϱ) ≥ min(κ(E), E)` for `E > 0`, `E ∉ supp ϱ`: the nearest point of the
support is an edge or lies below `0`. -/
private lemma outside_dist_ge (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : 0 < E) (hEs : E ∉ (varrho N σ).support) :
    min (kappa N σ E) E ≤ Metric.infDist E (varrho N σ).support := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hp := (card_innerCrit N σ hσ hN hS).2
  by_contra hlt
  rw [not_le] at hlt
  have hne : (varrho N σ).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hne).1 hlt
  rw [Real.dist_eq] at hdy
  have hdy1 : |E - y| < kappa N σ E := hdy.trans_le (min_le_left _ _)
  have hdy2 : |E - y| < E := hdy.trans_le (min_le_right _ _)
  obtain ⟨h1, h2⟩ := abs_lt.1 hdy2
  have hy0 : 0 < y := by linarith
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ hσ hN hS hy0).1 hy
  have hEk : E ∉ Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) := fun hm =>
    hEs ((mem_support_varrho_iff N σ hσ hN hS hE).2 ⟨k, hk1, hk2, hm⟩)
  have hkap : ∀ l, 1 ≤ l → l ≤ 2 * numBands N σ → kappa N σ E ≤ |E - edgeVal N σ l| := by
    intro l hl1 hl2
    exact ciInf_le (f := fun l : Finset.Icc 1 (2 * numBands N σ) => |E - edgeVal N σ (l : ℕ)|)
      (Finite.bddBelow_range _) ⟨l, Finset.mem_Icc.2 ⟨hl1, hl2⟩⟩
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hEk
  rcases hEk with hlo | hhi
  · have := hkap (2 * k) (by omega) (by omega)
    rw [abs_of_neg (by linarith)] at this
    have := abs_lt.1 hdy1
    linarith [hyk.1]
  · have := hkap (2 * k - 1) (by omega) (by omega)
    rw [abs_of_pos (by linarith)] at this
    have := abs_lt.1 hdy1
    linarith [hyk.2]

/-- `K ≤ N^a` for all large `N`, `a > 0`. -/
private lemma outside_ev_rpow {a : ℝ} (ha : 0 < a) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

/-- `√(n^x) = n^{x/2}` for `n > 0`. -/
private lemma outside_sqrt_rpow {n : ℝ} (hn : 0 < n) (x : ℝ) : √(n ^ x) = n ^ (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  ring_nf

/-- A property that is monotone in `x` and holds at `a` and at `b` holds at `min a b`. -/
private lemma outside_min_of {P : ℝ → Prop} {a b : ℝ} (ha : P a) (hb : P b) : P (min a b) := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

/-- The large-`N` conditions of the proof of Theorem 3.7, with `m₀ = min(N^{−2/3+τ}, τ)`. -/
private lemma outside_eventually {τ τ₀ ε : ℝ} (Kc K : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτ₀ : 0 < τ₀) (hτ₀6 : τ₀ ≤ 1 / 6) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ N ∧
      2 * (N : ℝ) ^ (-2 / 3 + τ / 2) ≤ (N : ℝ) ^ (-2 / 3 + τ) ∧
      4 ≤ (N : ℝ) * min ((N : ℝ) ^ (-2 / 3 + τ)) τ * √(min ((N : ℝ) ^ (-2 / 3 + τ)) τ) ∧
      √(kappaMax τ) / N ≤ τ ^ 2 / 16 ∧
      (N : ℝ) ^ (-1 + τ) ≤ min ((N : ℝ) ^ (-2 / 3 + τ)) τ ∧
      ((N : ℝ) ^ (-1 + τ₀)) ^ 2 ≤ √(min ((N : ℝ) ^ (-2 / 3 + τ)) τ) / N ∧
      Kc ≤ (N : ℝ) * √(min ((N : ℝ) ^ (-2 / 3 + τ)) τ) ∧
      K ≤ (N : ℝ) ^ (ε / 2) := by
  have hsτ : 0 < √τ := Real.sqrt_pos.2 hτ
  -- `N^{1−τ} ≥ τ⁻¹`, or `τ = 1`
  have h6 : ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) → (N : ℝ) ^ (-1 + τ) ≤ τ := by
    rcases hτ1.lt_or_eq with hlt | heq
    · filter_upwards [outside_ev_rpow (a := 1 - τ) (by linarith) τ⁻¹] with N hN hN1
      have hn0 : 0 < (N : ℝ) := by linarith
      rw [show -1 + τ = -(1 - τ) by ring, Real.rpow_neg hn0.le]
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos hn0 _) hτ]
      exact hN
    · exact Filter.Eventually.of_forall fun N _ => by rw [heq]; norm_num
  filter_upwards [outside_ev_rpow (a := 1) one_pos 4,
    outside_ev_rpow (a := τ / 2) (by positivity) 2,
    outside_ev_rpow (a := 1) one_pos (4 / (τ * √τ)),
    outside_ev_rpow (a := 3 * τ / 2) (by positivity) 4,
    outside_ev_rpow (a := 1) one_pos (16 * √(kappaMax τ) / τ ^ 2),
    h6,
    outside_ev_rpow (a := 1 - 2 * τ₀) (by linarith) (√τ)⁻¹,
    outside_ev_rpow (a := 2 / 3 + τ / 2) (by positivity) Kc,
    outside_ev_rpow (a := 1) one_pos (Kc / √τ),
    outside_ev_rpow (a := ε / 2) (by positivity) K] with N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [Real.rpow_one] at h1 h3 h5 h9
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  set n : ℝ := (N : ℝ) with hn
  set δ := n ^ (-2 / 3 + τ) with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hn0 _
  have hsδ : √δ = n ^ ((-2 / 3 + τ) / 2) := outside_sqrt_rpow hn0 _
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, h10⟩
  · have e : n ^ (-2 / 3 + τ) = n ^ (-2 / 3 + τ / 2) * n ^ (τ / 2) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [hδ, e]
    nlinarith [Real.rpow_pos_of_pos hn0 (-2 / 3 + τ / 2)]
  · refine outside_min_of (P := fun x => 4 ≤ n * x * √x) ?_ ?_
    · show 4 ≤ n * δ * √δ
      rw [hsδ, hδ]
      calc (4 : ℝ) ≤ n ^ (3 * τ / 2) := h4
        _ = n ^ (1 : ℝ) * n ^ (-2 / 3 + τ) * n ^ ((-2 / 3 + τ) / 2) := by
            rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; ring_nf
        _ = _ := by rw [Real.rpow_one]
    · show 4 ≤ n * τ * √τ
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
  · rw [div_le_iff₀ hn0]
    rw [div_le_iff₀ (by positivity)] at h5
    linarith
  · refine outside_min_of (P := fun x => n ^ (-1 + τ) ≤ x) ?_ (h6 hn1)
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · refine outside_min_of (P := fun x => (n ^ (-1 + τ₀)) ^ 2 ≤ √x / n) ?_ ?_
    · show (n ^ (-1 + τ₀)) ^ 2 ≤ √δ / n
      rw [hsδ, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, div_eq_mul_inv,
        ← Real.rpow_neg_one, ← Real.rpow_add hn0]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
    · show (n ^ (-1 + τ₀)) ^ 2 ≤ √τ / n
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, le_div_iff₀ hn0]
      rw [inv_le_iff_one_le_mul₀ hsτ] at h7
      have e : n ^ ((-1 + τ₀) * ((2 : ℕ) : ℝ)) * n = n ^ (-1 + 2 * τ₀) := by
        rw [← Real.rpow_add_one hn0.ne']; congr 1; push_cast; ring
      rw [e]
      calc n ^ (-1 + 2 * τ₀) ≤ n ^ (-1 + 2 * τ₀) * (n ^ (1 - 2 * τ₀) * √τ) :=
            le_mul_of_one_le_right (by positivity) h7
        _ = √τ := by
            rw [← mul_assoc, ← Real.rpow_add hn0]; ring_nf; rw [Real.rpow_zero, one_mul]
  · refine outside_min_of (P := fun x => Kc ≤ n * √x) ?_ ?_
    · show Kc ≤ n * √δ
      rw [hsδ]
      calc Kc ≤ n ^ (2 / 3 + τ / 2) := h8
        _ = n ^ (1 : ℝ) * n ^ ((-2 / 3 + τ) / 2) := by rw [← Real.rpow_add hn0]; ring_nf
        _ = _ := by rw [Real.rpow_one]
    · show Kc ≤ n * √τ
      rw [div_le_iff₀ hsτ] at h9
      exact h9

/-- `N > 0` and some `σ_i > 0` under (phi_bounded), (bound_Sigma) and (Sigma_gap). -/
private lemma outside_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso; have := h.phi_lower; simp [phiRatio, h0] at this; linarith
    · exact h0
  have hS : (posVals σ).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hM : M ≠ 0 := by
      rintro rfl; have := h.phi_lower; simp [phiRatio] at this; linarith
    have hall : ∀ i, σ i = 0 := by
      intro i
      by_contra hi
      have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
      have : σ i ∈ posVals σ := by
        simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨i, rfl⟩, hpos⟩
      rw [hne] at this; simp at this
    have hgap := h.Sigma_gap
    have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
      simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
        Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul]
      congr 1
      rw [Finset.sum_congr rfl fun i _ => Set.indicator_of_mem
        (show σ i ∈ Set.Icc 0 τ by rw [hall i]; exact ⟨le_rfl, hτ.le⟩) (1 : ℝ → ℝ≥0∞)]
      simp
    rw [happ, ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _),
      ENNReal.toReal_one] at hgap
    linarith
  exact ⟨hN, hS⟩

/-- `E + iy ∈ 𝐃(τ, N)` for `E ∈ [τ, τ⁻¹]`, `N^{−1+τ} ≤ y ≤ τ⁻¹`. -/
private lemma outside_mem_specDomain {τ E y : ℝ} (hE : E ∈ Set.Icc τ τ⁻¹) (hτ : 0 < τ)
    (hy1 : (N : ℝ) ^ (-1 + τ) ≤ y) (hy2 : y ≤ τ⁻¹) (hy0 : 0 < y) :
    (↑E + ↑y * Complex.I : ℂ) ∈ specDomain τ N := by
  have hre : (↑E + ↑y * Complex.I : ℂ).re = E := by simp
  have him : (↑E + ↑y * Complex.I : ℂ).im = y := by simp
  refine ⟨by rw [him]; exact hy0, ?_, ?_, by rw [him]; exact hy1, by rw [him]; exact hy2⟩
  · have := Complex.abs_re_le_norm (↑E + ↑y * Complex.I : ℂ)
    rw [hre, abs_of_pos (hτ.trans_le hE.1)] at this
    exact hE.1.trans this
  · rw [hre, abs_of_pos (hτ.trans_le hE.1)]; exact hE.2

/-- The scale `η̃ = N^{−1/2} κ^{1/4}` of the proof of Theorem 3.7 and its window: with
`m₀ = min(N^{−2/3+τ}, τ)`, `dist(E, supp ϱ) ≥ N^{−2/3+τ}`, `E ∈ [τ, τ⁻¹]`,
`N m₀^{3/2} ≥ 4` and `N^{−1} C_κ^{1/2} ≤ τ²/16`: `κ ≥ m₀`, `N η̃² = √κ`,
`η̃ ≤ κ/2`, `η̃ ≤ τ/4`, `η̃ ≤ dist(E, supp ϱ)/2`. -/
private lemma outside_geom (σ : Fin M → ℝ) {τ : ℝ} (h : DensityAssumptions τ N σ) {E : ℝ}
    (hE : E ∈ Set.Icc τ τ⁻¹) (hd : (N : ℝ) ^ (-2 / 3 + τ) ≤
      Metric.infDist E (varrho N σ).support)
    (h3 : 4 ≤ (N : ℝ) * min ((N : ℝ) ^ (-2 / 3 + τ)) τ * √(min ((N : ℝ) ^ (-2 / 3 + τ)) τ))
    (h4 : √(kappaMax τ) / N ≤ τ ^ 2 / 16) :
    E ∉ (varrho N σ).support ∧ min ((N : ℝ) ^ (-2 / 3 + τ)) τ ≤ kappa N σ E ∧
      0 < kappa N σ E ∧ 0 < √(√(kappa N σ E) / N) ∧
      (N : ℝ) * √(√(kappa N σ E) / N) ^ 2 = √(kappa N σ E) ∧
      √(√(kappa N σ E) / N) ≤ kappa N σ E / 2 ∧ √(√(kappa N σ E) / N) ≤ τ / 4 ∧
      √(√(kappa N σ E) / N) ≤ Metric.infDist E (varrho N σ).support / 2 := by
  have hτ := h.pos
  obtain ⟨hN, hS⟩ := outside_facts h
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  set d := Metric.infDist E (varrho N σ).support with hd'
  set δ := (N : ℝ) ^ (-2 / 3 + τ) with hδ
  set κ := kappa N σ E with hκ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hn0 _
  have hE0 : 0 < E := hτ.trans_le hE.1
  have hEs : E ∉ (varrho N σ).support := fun hm => by
    have := Metric.infDist_zero_of_mem hm
    rw [← hd'] at this; linarith
  have hκm : min δ τ ≤ κ :=
    (min_le_min hd hE.1).trans (outside_kappa_ge σ h.nonneg hN hS hE0)
  have hm0 : 0 < min δ τ := lt_min hδ0 hτ
  have hκ0 : 0 < κ := hm0.trans_le hκm
  have hdκ := outside_dist_ge σ h.nonneg hN hS hE0 hEs
  have hκmax : κ ≤ kappaMax τ := kappa_le h (abs_le.2 ⟨by linarith [hE.1, inv_pos.2 hτ], hE.2⟩)
  set η := √(√κ / N) with hη
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
  have hη0 : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη2 : η ^ 2 = √κ / N := Real.sq_sqrt (by positivity)
  have hNη : (N : ℝ) * η ^ 2 = √κ := by rw [hη2]; field_simp
  -- `η ≤ κ/2`
  have hk1 : η ≤ κ / 2 := by
    rw [hη, Real.sqrt_le_left (by positivity)]
    · rw [div_le_iff₀ hn0]
      have hsm : √(min δ τ) ≤ √κ := Real.sqrt_le_sqrt hκm
      have hsq : √κ * √κ = κ := Real.mul_self_sqrt hκ0.le
      have : 4 ≤ (N : ℝ) * κ * √κ :=
        h3.trans (mul_le_mul (mul_le_mul_of_nonneg_left hκm hn0.le) hsm
          (Real.sqrt_nonneg _) (by positivity))
      nlinarith
  -- `η ≤ τ/4`
  have hk2 : η ≤ τ / 4 := by
    rw [hη, Real.sqrt_le_left (by positivity)]
    calc √κ / N ≤ √(kappaMax τ) / N :=
          div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hκmax) hn0.le
      _ ≤ τ ^ 2 / 16 := h4
      _ = (τ / 4) ^ 2 := by ring
  refine ⟨hEs, hκm, hκ0, hη0, hNη, hk1, hk2, ?_⟩
  rcases min_choice κ E with hmin | hmin
  · rw [hmin] at hdκ; linarith
  · rw [hmin] at hdκ; linarith [hE.1]

/-- (im_m_asymp) on the vertical line through `E`, extended below the cutoff by
`im_mFun_ratio`: for `0 < η ≤ τ⁻¹`, `Im m(E + iη) ≥ c η (κ + max(η, N^{−1+τ}))^{−1/2}` and,
for `η ≤ dist(E, supp ϱ)`, `Im m(E + iη) ≤ 2 C η κ^{−1/2}`. -/
private lemma outside_im_bounds (σ : Fin M → ℝ) {τ : ℝ} (h : DensityAssumptions τ N σ)
    (hreg : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    (hτ1 : τ ≤ 1) {E : ℝ} (hE : E ∈ Set.Icc τ τ⁻¹) (hEs : E ∉ (varrho N σ).support)
    (hη₁d : (N : ℝ) ^ (-1 + τ) ≤ Metric.infDist E (varrho N σ).support) :
    (∀ η : ℝ, 0 < η → η ≤ τ⁻¹ →
      imAsympLower τ * (η / √(kappa N σ E + max η ((N : ℝ) ^ (-1 + τ)))) ≤
        (mFun N σ (↑E + ↑η * Complex.I)).im) ∧
    (∀ η : ℝ, 0 < η → η ≤ Metric.infDist E (varrho N σ).support → η ≤ τ⁻¹ →
      0 < kappa N σ E →
      (mFun N σ (↑E + ↑η * Complex.I)).im ≤ 2 * imAsympUpper τ * (η / √(kappa N σ E))) := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso; have := h.phi_lower; simp [phiRatio, h0] at this; linarith
    · exact h0
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set η₁ := (N : ℝ) ^ (-1 + τ) with hη₁
  have hη₁0 : 0 < η₁ := Real.rpow_pos_of_pos (by linarith) _
  have hη₁1 : η₁ ≤ τ⁻¹ :=
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)).trans (one_le_inv₀ hτ |>.2 hτ1)
  set κ := kappa N σ E with hκ
  have hasy : ∀ y, η₁ ≤ y → y ≤ τ⁻¹ →
      imAsympLower τ * (y / √(κ + y)) ≤ (mFun N σ (↑E + ↑y * Complex.I)).im ∧
        (mFun N σ (↑E + ↑y * Complex.I)).im ≤ imAsympUpper τ * (y / √(κ + y)) := by
    intro y h1 h2
    have hy0 : 0 < y := hη₁0.trans_le h1
    have hz := outside_mem_specDomain (N := N) hE hτ h1 h2 hy0
    have := im_m_asymp h hreg hz (by simpa using hE) (by simpa using hEs)
    simpa using this
  have hκ0 : 0 ≤ κ := kappa_nonneg N σ E
  refine ⟨fun η hη hητ => ?_, fun η hη hηd hητ hκpos => ?_⟩
  · rcases le_or_gt η₁ η with hle | hlt
    · rw [max_eq_left hle]; exact (hasy η hle hητ).1
    · rw [max_eq_right hlt.le]
      have h1 := (hasy η₁ le_rfl hη₁1).1
      have h2 := (im_mFun_ratio σ h.nonneg hN hη hlt.le hη₁d).1
      have hs : 0 < √(κ + η₁) := Real.sqrt_pos.2 (by linarith)
      have h3 : imAsympLower τ / √(κ + η₁) ≤ (mFun N σ (↑E + ↑η₁ * Complex.I)).im / η₁ := by
        rw [le_div_iff₀ hη₁0]
        calc imAsympLower τ / √(κ + η₁) * η₁ = imAsympLower τ * (η₁ / √(κ + η₁)) := by ring
          _ ≤ _ := h1
      have h4 := h3.trans h2
      rw [le_div_iff₀ hη] at h4
      calc imAsympLower τ * (η / √(κ + η₁)) = imAsympLower τ / √(κ + η₁) * η := by ring
        _ ≤ _ := h4
  · have hCu : 0 ≤ imAsympUpper τ := by
      unfold imAsympUpper
      exact le_trans (by positivity) (le_max_right _ _)
    set η₂ := max η η₁ with hη₂
    have hη₂d : η₂ ≤ Metric.infDist E (varrho N σ).support := max_le hηd hη₁d
    have hη₂0 : 0 < η₂ := lt_max_of_lt_left hη
    have h1 := (hasy η₂ (le_max_right _ _) (max_le hητ hη₁1)).2
    have h2 := (im_mFun_ratio σ h.nonneg hN hη (le_max_left _ _) hη₂d).2
    have hs : 0 < √κ := Real.sqrt_pos.2 hκpos
    have hs2 : √κ ≤ √(κ + η₂) := Real.sqrt_le_sqrt (by linarith)
    have h3 : (mFun N σ (↑E + ↑η₂ * Complex.I)).im / η₂ ≤ imAsympUpper τ / √κ := by
      rw [div_le_iff₀ hη₂0]
      calc _ ≤ imAsympUpper τ * (η₂ / √(κ + η₂)) := h1
        _ = imAsympUpper τ / √(κ + η₂) * η₂ := by ring
        _ ≤ imAsympUpper τ / √κ * η₂ := by gcongr
    have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))
    rw [div_le_iff₀ hη] at h4
    calc _ ≤ 2 * (imAsympUpper τ / √κ) * η := h4
      _ = _ := by ring

/-- `τ'(τ) > 0` (the window of Lemmas A.4 and A.5). -/
private lemma outside_edgeTau'_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau' τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  unfold edgeTau' edgeTau0
  positivity

/-- The constant `c` of (im_m_asymp) is positive. -/
private lemma outside_imAsympLower_pos {τ : ℝ} (hτ : 0 < τ) : 0 < imAsympLower τ := by
  have ht : 0 < τ / 2 := by positivity
  have hcx : 0 < edgecx (τ / 2) := by unfold edgecx; positivity
  have hCx : 0 < edgeCx (τ / 2) := by unfold edgeCx; positivity
  have hC2 : 0 < edgeC2 (τ / 2) := by unfold edgeC2; positivity
  have hte := outside_edgeTau'_pos ht
  have hCm : 0 < mBoundConst (τ / 2) := by unfold mBoundConst genPropConst; positivity
  have hsq : 0 < sqLower (τ / 2) := by
    unfold sqLower
    refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity
  have hout : 0 < outImLower τ := by unfold outImLower; positivity
  unfold imAsympLower
  exact lt_min hsq (by positivity)

/-- The covering of the vertical line through `E ∈ [τ, τ⁻¹] ∖ supp ϱ`: a point of `𝐃(τ₀, N)`
on it lies in `𝐃^o(τ₀, τ'')` or in `𝐃^e_l(τ₀, τ'')` for an edge `a_l ≥ τ/2`, which is then
regular at `τ₀` by the edge hypothesis at `τ/2` (`τ₀ ≤ τ/2`, `τ'' ≤ τ/4`). -/
private lemma outside_cover (σ : Fin M → ℝ) {τ τ₀ τ'' : ℝ} (h : DensityAssumptions τ N σ)
    (hreg : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    {E : ℝ} (hE : E ∈ Set.Icc τ τ⁻¹) (hEs : E ∉ (varrho N σ).support)
    (hτ₀τ : τ₀ ≤ τ / 2) (hτ''τ : τ'' ≤ τ / 4) {w : ℂ} (hw : w ∈ specDomain τ₀ N)
    (hwre : w.re = E) :
    w ∈ outsideDomain τ₀ τ'' N σ ∨ ∃ l, RegularEdge τ₀ N σ l ∧ w ∈ edgeDomain τ₀ τ'' N σ l := by
  have hτ := h.pos
  obtain ⟨hN, hS⟩ := outside_facts h
  have hE0 : 0 < E := hτ.trans_le hE.1
  by_cases hk : τ'' ≤ kappa N σ E
  · left
    refine ⟨hw, ?_⟩
    rw [hwre]
    refine le_trans ?_ (outside_dist_ge σ h.nonneg hN hS hE0 hEs)
    exact le_min hk (by linarith [hE.1])
  · right
    rw [not_le] at hk
    have hp := (card_innerCrit N σ h.nonneg hN hS).2
    have hne : Nonempty (Finset.Icc 1 (2 * numBands N σ)) :=
      ⟨⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩⟩
    obtain ⟨⟨l, hl⟩, hlt⟩ := exists_lt_of_ciInf_lt (f := fun l : Finset.Icc 1 (2 * numBands N σ) =>
      |E - edgeVal N σ (l : ℕ)|) hk
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hl
    simp only at hlt
    obtain ⟨h1, h2⟩ := abs_lt.1 hlt
    have hreg' := regularEdge_mono (hreg l hl1 hl2 (by linarith [hE.1])) hτ₀τ
    exact ⟨l, hreg', hw, by rw [hwre]; constructor <;> linarith⟩

/-- (1+xm) on the covering of `outside_cover`, with
`c_x = min(c_x(𝐃^e), c_x(𝐃^o))`. -/
private lemma outside_onexm (σ : Fin M → ℝ) {τ₀ τ'' : ℝ} (hD : DensityAssumptions τ₀ N σ)
    (hτ'' : 0 < τ'') (hτ''le : τ'' ≤ edgeTau' τ₀) {w : ℂ}
    (hw : w ∈ outsideDomain τ₀ τ'' N σ ∨ ∃ l, RegularEdge τ₀ N σ l ∧
      w ∈ edgeDomain τ₀ τ'' N σ l) :
    ∀ i, min (oneXmConst (edgeMz τ₀) (mBoundConst τ₀)) (oneXmConst (outMz τ₀ τ'') (mBoundConst τ₀))
      ≤ ‖1 + (σ i : ℂ) * mFun N σ w‖ := by
  have hτ₀ := hD.pos
  have hCm : 0 < mBoundConst τ₀ := by unfold mBoundConst genPropConst; positivity
  have hmz : 0 < outMz τ₀ τ'' := by unfold outMz outcr outImLower; positivity
  intro i
  rcases hw with ho | ⟨l, hl, he⟩
  · exact (min_le_right _ _).trans (one_add_mul_ge_of_mz_reg hD.nonneg hmz hCm
      (gen_prop_m_specDomain hD ho.1).2.1 (mz_reg_outside hD hτ'' ho) i)
  · exact (min_le_left _ _).trans (one_add_mul_mFun_edge hD hl hτ''le he i)

/-- Above `η̃`: from `Im m ≥ c η (κ + max(η, a))^{−1/2}` with `a ≤ κ`, `N η̃² = √κ`,
`η̃ ≤ κ/2` and `η ≥ η̃`, one gets `N η Im m ≥ c/√2`. -/
private lemma outside_arith_high {n κ ηt η a c I : ℝ} (hn : 0 < n) (hηt : 0 < ηt)
    (hηtη : ηt ≤ η) (hNηt : n * ηt ^ 2 = √κ) (hηtκ : ηt ≤ κ / 2) (ha : a ≤ κ) (hc : 0 < c)
    (hm : c * (η / √(κ + max η a)) ≤ I) : c / √2 ≤ n * η * I := by
  have hκ0 : 0 < κ := by linarith
  have hη0 : 0 < η := hηt.trans_le hηtη
  have hκ : κ = n ^ 2 * ηt ^ 4 := by
    have := congrArg (· ^ 2) hNηt
    simp only [Real.sq_sqrt hκ0.le] at this
    rw [← this]; ring
  have hq : n ^ 2 * ηt ^ 4 ≤ n ^ 2 * η ^ 4 := by gcongr
  have h3 : 2 ≤ n ^ 2 * ηt ^ 3 := by
    have e : n ^ 2 * ηt ^ 3 * ηt = κ := by rw [hκ]; ring
    have h' : 2 * ηt ≤ n ^ 2 * ηt ^ 3 * ηt := by rw [e]; linarith
    exact le_of_mul_le_mul_right h' hηt
  have h3' : n ^ 2 * ηt ^ 3 ≤ n ^ 2 * η ^ 3 := by gcongr
  have hmax : max η a ≤ n ^ 2 * η ^ 4 := by
    refine max_le ?_ (ha.trans (hκ.le.trans hq))
    nlinarith
  have hs : √(κ + max η a) ≤ √2 * (n * η ^ 2) := by
    rw [show √2 * (n * η ^ 2) = √(2 * (n * η ^ 2) ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 < √(κ + max η a) := Real.sqrt_pos.2 (by
    have := le_max_left η a; linarith)
  have h2 : 0 < √2 := by positivity
  calc c / √2 = c * (n * η ^ 2) / (√2 * (n * η ^ 2)) := by field_simp
    _ ≤ c * (n * η ^ 2) / √(κ + max η a) := by gcongr
    _ = n * η * (c * (η / √(κ + max η a))) := by ring
    _ ≤ n * η * I := by gcongr

/-- Below `η̃`: `Im m/(Nη) ≥ (c/√2) B²`, `B = 1/(N η̃)`, from
`Im m ≥ c η (κ + max(η, a))^{−1/2}` with `η, a ≤ κ` and `N η̃² = √κ`. -/
private lemma outside_arith_low {n κ ηt η a c I : ℝ} (hn : 0 < n) (hηt : 0 < ηt) (hη0 : 0 < η)
    (hηκ : η ≤ κ) (hNηt : n * ηt ^ 2 = √κ) (ha : a ≤ κ) (hc : 0 < c)
    (hm : c * (η / √(κ + max η a)) ≤ I) :
    √(c / √2) * (1 / (n * ηt)) ≤ √(I / (n * η)) := by
  have hκ0 : 0 < κ := hη0.trans_le hηκ
  have hs : √(κ + max η a) ≤ √2 * √κ := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by have := max_le hηκ ha; linarith)
  have hs0 : 0 < √(κ + max η a) := Real.sqrt_pos.2 (by have := le_max_left η a; linarith)
  have h2 : 0 < √2 := by positivity
  have hI : c / (√2 * √κ) * η ≤ I := by
    calc c / (√2 * √κ) * η ≤ c / √(κ + max η a) * η := by gcongr
      _ = c * (η / √(κ + max η a)) := by ring
      _ ≤ I := hm
  have key : c / √2 * (1 / (n * ηt)) ^ 2 ≤ I / (n * η) := by
    rw [le_div_iff₀ (by positivity)]
    calc c / √2 * (1 / (n * ηt)) ^ 2 * (n * η) = c / (√2 * (n * ηt ^ 2)) * η := by
          field_simp
      _ = c / (√2 * √κ) * η := by rw [hNηt]
      _ ≤ I := hI
  calc √(c / √2) * (1 / (n * ηt)) = √(c / √2 * (1 / (n * ηt)) ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ √(I / (n * η)) := Real.sqrt_le_sqrt key

/-- The final collection of the bounds below `η̃`. -/
private lemma outside_arith_collect {X X₁ X₂ X₃ I Δ P Ψ B ζ c C K₅ K₆ a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hI0 : 0 ≤ I) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h : X ≤ X₁ + 2 * √(X₂ + c⁻¹ ^ 2 * I * a ^ 2) * √(X₃ + c⁻¹ ^ 2 * I * b ^ 2) +
      c⁻¹ ^ 2 * Δ * (a * b))
    (h₁ : X₁ ≤ P * (Ψ * a * b)) (h₂ : X₂ ≤ P * (Ψ * a * a)) (h₃ : X₃ ≤ P * (Ψ * b * b))
    (hΨ : Ψ ≤ (√(2 * C) + 1) * B) (hI : I ≤ 2 * C * B) (hΔ : Δ ≤ 2 * I) (hP : 1 ≤ P)
    (hK₅ : K₅ = 3 * (√(2 * C) + 1) + 8 * c⁻¹ ^ 2 * C) (hBζ : B ≤ K₆ * ζ) (hK : K₅ * K₆ ≤ P)
    (hΨ0 : 0 ≤ Ψ) (hζ : 0 ≤ ζ) :
    X ≤ P * P * ζ * a * b := by
  have hc2 : 0 ≤ c⁻¹ ^ 2 := by positivity
  set A := P * Ψ + c⁻¹ ^ 2 * I with hA
  have hA0 : 0 ≤ A := by positivity
  have hsv : √(X₂ + c⁻¹ ^ 2 * I * a ^ 2) ≤ √A * a := by
    calc √(X₂ + c⁻¹ ^ 2 * I * a ^ 2) ≤ √(A * a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = √A * a := by rw [Real.sqrt_mul hA0, Real.sqrt_sq ha]
  have hsw : √(X₃ + c⁻¹ ^ 2 * I * b ^ 2) ≤ √A * b := by
    calc √(X₃ + c⁻¹ ^ 2 * I * b ^ 2) ≤ √(A * b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = √A * b := by rw [Real.sqrt_mul hA0, Real.sqrt_sq hb]
  have hprod : √(X₂ + c⁻¹ ^ 2 * I * a ^ 2) * √(X₃ + c⁻¹ ^ 2 * I * b ^ 2) ≤ A * (a * b) := by
    calc _ ≤ (√A * a) * (√A * b) :=
          mul_le_mul hsv hsw (Real.sqrt_nonneg _) (by positivity)
      _ = (√A * √A) * (a * b) := by ring
      _ = A * (a * b) := by rw [Real.mul_self_sqrt hA0]
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have step1 : X ≤ (3 * P * Ψ + 4 * c⁻¹ ^ 2 * I) * (a * b) := by
    have e1 : c⁻¹ ^ 2 * Δ * (a * b) ≤ c⁻¹ ^ 2 * (2 * I) * (a * b) := by gcongr
    nlinarith
  have hs2 : 0 ≤ √(2 * C) := Real.sqrt_nonneg _
  have step2 : 3 * P * Ψ + 4 * c⁻¹ ^ 2 * I ≤ P * K₅ * B := by
    rw [hK₅]
    have e1 : 3 * P * Ψ ≤ 3 * P * ((√(2 * C) + 1) * B) := by gcongr
    have e2 : 4 * c⁻¹ ^ 2 * I ≤ 4 * c⁻¹ ^ 2 * (2 * C * B) := by gcongr
    have e3 : 8 * c⁻¹ ^ 2 * C * B ≤ P * (8 * c⁻¹ ^ 2 * C * B) :=
      le_mul_of_one_le_left (by positivity) hP
    nlinarith
  have hK₅0 : 0 ≤ K₅ := by rw [hK₅]; positivity
  have hP0 : 0 ≤ P := by linarith
  have step3 : P * K₅ * B ≤ P * P * ζ := by
    calc P * K₅ * B ≤ P * K₅ * (K₆ * ζ) := by gcongr
      _ = P * (K₅ * K₆) * ζ := by ring
      _ ≤ P * P * ζ := by gcongr
  calc X ≤ (3 * P * Ψ + 4 * c⁻¹ ^ 2 * I) * (a * b) := step1
    _ ≤ P * P * ζ * (a * b) := mul_le_mul_of_nonneg_right (step2.trans step3) hab
    _ = P * P * ζ * a * b := by ring

/-- `1/(Nη) ≤ (√2/c)^{1/2} (Im m/(Nη))^{1/2}` from `N η Im m ≥ c/√2`. -/
private lemma outside_arith_psi {n η c I : ℝ} (hn : 0 < n) (hη : 0 < η) (hc : 0 < c)
    (h : c / √2 ≤ n * η * I) : 1 / (n * η) ≤ √(√2 / c) * √(I / (n * η)) := by
  have hnη : 0 < n * η := mul_pos hn hη
  have h2 : 0 < √2 := by positivity
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / (n * η))]
  refine Real.sqrt_le_sqrt ?_
  have hI : 0 ≤ I := by
    have : 0 < n * η * I := lt_of_lt_of_le (by positivity) h
    exact (pos_of_mul_pos_right this hnη.le).le
  rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = √2 / c * (c / √2) := by field_simp
    _ ≤ √2 / c * (n * η * I) := by gcongr
    _ = √2 / c * (I / (n * η)) * (n * η) ^ 2 := by field_simp

/-- Four probabilities at most `N^{−D−1}` sum to at most `N^{−D}` once `N ≥ 4`. -/
private lemma outside_four_le {N : ℕ} {D : ℝ} (hN : (4 : ℝ) ≤ N) {a b c d : ℝ≥0∞}
    (ha : a ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hb : b ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hc : c ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hd : d ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1)))) :
    a + b + c + d ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hn0 : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (-(D + 1)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hn0.le _
  calc a + b + c + d ≤ ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x +
        ENNReal.ofReal x := by gcongr
    _ = ENNReal.ofReal (x + x + x + x) := by
        rw [ENNReal.ofReal_add (by positivity) hx0, ENNReal.ofReal_add (by positivity) hx0,
          ENNReal.ofReal_add hx0 hx0]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : x * N = (N : ℝ) ^ (-D) := by
          rw [hx, show -D = -(D + 1) + 1 by ring, Real.rpow_add_one hn0.ne']
        have : x + x + x + x = 4 * x := by ring
        rw [this, ← e]
        exact mul_le_mul_of_nonneg_right hN hx0 |>.trans_eq (mul_comm _ _) |>.trans_eq' rfl

/-- A union bound for four events. -/
private lemma outside_union4 {Ω : Type*} [MeasureSpace Ω] {B S₁ S₂ S₃ S₄ : Set Ω}
    (h : B ⊆ S₁ ∪ S₂ ∪ S₃ ∪ S₄) : ℙ B ≤ ℙ S₁ + ℙ S₂ + ℙ S₃ + ℙ S₄ :=
  (measure_mono h).trans ((measure_union_le _ _).trans (by
    gcongr
    exact (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)))

/-- Theorem 3.7 (`thm:G_outside`) at fixed `N`, under (T_diag), with every edge with `a_k ≥ τ/2`
regular at `τ/2`: (G_outside) for `E ∈ [τ, τ⁻¹]`, `0 < η ≤ τ⁻¹`, `dist(E, supp ϱ) ≥ N^{−2/3+τ}`. -/
theorem G_outside (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      ∀ z : ℂ, z.re ∈ Set.Icc τ τ⁻¹ → 0 < z.im → z.im ≤ τ⁻¹ →
        (N : ℝ) ^ (-2 / 3 + τ) ≤ Metric.infDist z.re (varrho N (specOf Sig)).support →
        ODomMatAt N ε D (fun ω => lawMat Sig (X ω) z)
          (fun _ => √((mFun N (specOf Sig) z).im / (N * z.im))) := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X hm => absurd hm.tau_le_one hτ1⟩
  -- parameters, fixed before `N₀`
  set τ₀ := min (τ / 4) (1 / 6) with hτ₀def
  have hτ₀ : 0 < τ₀ := lt_min (by positivity) (by norm_num)
  have hτ₀4 : τ₀ ≤ τ / 4 := min_le_left _ _
  have hτ₀6 : τ₀ ≤ 1 / 6 := min_le_right _ _
  set τ'' := min (edgeTau' τ₀) (τ / 4) with hτ''def
  have hτ'' : 0 < τ'' := lt_min (outside_edgeTau'_pos hτ₀) (by positivity)
  set cim := imAsympLower τ with hcimdef
  set Cim := imAsympUpper τ with hCimdef
  have hcim : 0 < cim := outside_imAsympLower_pos hτ
  have hCim : 0 ≤ Cim := by
    rw [hCimdef]; unfold imAsympUpper; exact le_trans (by positivity) (le_max_right _ _)
  set cx := min (oneXmConst (edgeMz τ₀) (mBoundConst τ₀))
    (oneXmConst (outMz τ₀ τ'') (mBoundConst τ₀)) with hcxdef
  have hCm : 0 < mBoundConst τ₀ := by unfold mBoundConst genPropConst; positivity
  have hcx : 0 < cx := by
    refine lt_min ?_ ?_
    · have : 0 < edgeMz τ₀ := by
        unfold edgeMz; exact lt_min (by positivity) (div_pos (outside_edgeTau'_pos hτ₀) hCm)
      unfold oneXmConst; positivity
    · have : 0 < outMz τ₀ τ'' := by unfold outMz outcr outImLower; positivity
      unfold oneXmConst; positivity
  have hcx2 : cx ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  set c := cx / 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by linarith
  set Kc := (8 * τ⁻¹ * Cim / cx) ^ 2 with hKc
  set K₆ := (√(cim / √2))⁻¹ with hK₆
  set K₅ := 3 * (√(2 * Cim) + 1) + 8 * c⁻¹ ^ 2 * Cim with hK₅
  set K₇ := 1 + √(√2 / cim) with hK₇
  set K := max (K₅ * K₆) K₇ with hK
  obtain ⟨Ng, hg⟩ := gap_edgeWin τ C (τ / 2) (D + 1) hτ (by positivity) (by linarith)
  obtain ⟨Ne, he⟩ := edge_law τ₀ τ'' C (ε / 2) (D + 1) hτ₀ hτ'' (min_le_left _ _)
    (by positivity)
  obtain ⟨No, ho⟩ := outside_law τ₀ τ'' C (ε / 2) (D + 1) hτ₀ hτ'' (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (((outside_eventually Kc K hτ hτ1 hτ₀ hτ₀6 hε).and (Filter.eventually_ge_atTop Ng)).and
      ((Filter.eventually_ge_atTop Ne).and (Filter.eventually_ge_atTop No)))
  refine ⟨N₀, fun N hN Ω _ _ M Sig X hm hreg z hzre hzim hzτ hzd => ?_⟩
  obtain ⟨⟨⟨T1, T2, T3, T4, T5, T6, T7, T8⟩, hNg⟩, hNe, hNo⟩ := hN₀ N hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  set σ := specOf Sig with hσdef
  have hDτ : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hD₀ : DensityAssumptions τ₀ N σ := hDτ.mono hτ₀ (by linarith)
  have hσle : ∀ i, σ i ≤ τ⁻¹ := hDτ.bound_Sigma
  obtain ⟨E, η, rfl⟩ : ∃ E η : ℝ, z = ↑E + ↑η * Complex.I :=
    ⟨z.re, z.im, (Complex.re_add_im z).symm⟩
  have hre : (↑E + ↑η * Complex.I : ℂ).re = E := by simp
  have him : (↑E + ↑η * Complex.I : ℂ).im = η := by simp
  rw [hre] at hzre hzd
  rw [him] at hzim hzτ ⊢
  set d := Metric.infDist E (varrho N σ).support with hd
  obtain ⟨hEs, hκm, hκ0, hηt0, hNηt, hηtκ, hηtτ, hηtd⟩ := outside_geom σ hDτ hzre hzd T3 T4
  set κ := kappa N σ E with hκ
  set ηt := √(√κ / N) with hηt
  set η₁ := (N : ℝ) ^ (-1 + τ) with hη₁
  have hη₁d : η₁ ≤ d := (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans hzd
  have hη₁κ : η₁ ≤ κ := T5.trans hκm
  obtain ⟨hLB, hUB⟩ := outside_im_bounds σ hDτ hreg hτ1 hzre hEs hη₁d
  have hηtlow : (N : ℝ) ^ (-1 + τ₀) ≤ ηt := by
    rw [hηt, Real.le_sqrt (Real.rpow_nonneg hn0.le _)]
    · exact T6.trans (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hκm) hn0.le)
    · positivity
  have hτinv : τ⁻¹ ≤ τ₀⁻¹ := inv_anti₀ hτ₀ (by linarith)
  have hE₀ : E ∈ Set.Icc τ₀ τ₀⁻¹ := ⟨by linarith [hzre.1], hzre.2.trans hτinv⟩
  have hm₀ : IsModel τ₀ C M N Sig X := hm.mono hτ₀ (by linarith)
  -- the laws at `τ₀` on the vertical line above `η̃`
  have hlaw : ∀ y, ηt ≤ y → y ≤ τ⁻¹ →
      ODomMatAt N (ε / 2) (D + 1) (fun ω => lawMat Sig (X ω) (↑E + ↑y * Complex.I))
        (fun _ => Psi N σ (↑E + ↑y * Complex.I)) ∧
      ∀ i, cx ≤ ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑y * Complex.I)‖ := by
    intro y hy1 hy2
    have hw := outside_mem_specDomain (N := N) hE₀ hτ₀ (hηtlow.trans hy1) (hy2.trans hτinv)
      (hηt0.trans_le hy1)
    have hcov := outside_cover σ (τ'' := τ'') hDτ hreg hzre hEs (by linarith)
      (min_le_right _ _) hw (by simp)
    refine ⟨?_, outside_onexm σ hD₀ hτ'' (min_le_left _ _) hcov⟩
    rcases hcov with hwo | ⟨l, hl, hwe⟩
    · exact (ho N hNo M Sig X hm₀).1 _ hwo
    · exact (he N hNe M Sig X l hm₀ hl).1 _ hwe
  have hP1 : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by positivity)
  have hPP : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hDD : ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  set ζ := √((mFun N σ (↑E + ↑η * Complex.I)).im / (N * η)) with hζ
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  rcases le_or_gt ηt η with hηge | hηlt
  · -- above `η̃`: the law at `z`
    obtain ⟨hL, -⟩ := hlaw η hηge hzτ
    have hhigh := outside_arith_high hn0 hηt0 hηge hNηt hηtκ hη₁κ hcim (hLB η hzim hzτ)
    have hpsi := outside_arith_psi hn0 hzim hcim hhigh
    have hΨ : Psi N σ (↑E + ↑η * Complex.I) ≤ K₇ * ζ := by
      unfold Psi
      rw [him, hK₇]
      linarith
    have hK7 : K₇ ≤ (N : ℝ) ^ (ε / 2) := (le_max_right _ _).trans T8
    intro v w
    unfold DomAt
    refine le_trans (measure_mono fun ω hω => ?_) ((hL v w).trans hDD)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt ?_ hω
    have hv := (Real.sqrt_nonneg _ : 0 ≤ testNorm v)
    have hw := (Real.sqrt_nonneg _ : 0 ≤ testNorm w)
    have hvw : 0 ≤ testNorm v * testNorm w := mul_nonneg hv hw
    calc (N : ℝ) ^ (ε / 2) * (Psi N σ (↑E + ↑η * Complex.I) * testNorm v * testNorm w)
        ≤ (N : ℝ) ^ (ε / 2) * (K₇ * ζ * testNorm v * testNorm w) := by gcongr
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * ζ * testNorm v * testNorm w) := by gcongr
      _ = (N : ℝ) ^ ε * (ζ * testNorm v * testNorm w) := by rw [hPP]; ring
  · -- below `η̃`: comparison with `z̃ = E + iη̃` on the event of Lemma 10.1
    have hηle : η ≤ ηt := hηlt.le
    have hτinv1 : 1 ≤ τ⁻¹ := one_le_inv₀ hτ |>.2 hτ1
    have hηtτ' : ηt ≤ τ⁻¹ := hηtτ.trans (by linarith)
    have hηtd' : ηt ≤ d := hηtd.trans (by linarith [hηt0])
    obtain ⟨hLt, hcxt⟩ := hlaw ηt le_rfl hηtτ'
    obtain ⟨hN0, -⟩ := outside_facts hDτ
    set It := (mFun N σ (↑E + ↑ηt * Complex.I)).im with hItdef
    set B := 1 / ((N : ℝ) * ηt) with hBdef
    have hB0 : 0 < B := by positivity
    have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
    have hBκ : ηt / √κ = B := by rw [← hNηt, hBdef]; field_simp
    have hIt : It ≤ 2 * Cim * B := by
      have := hUB ηt hηt0 hηtd' hηtτ' hκ0
      rw [hBκ] at this
      exact this
    have hIt0 : 0 ≤ It := (mFun_spec N σ hDτ.nonneg (by simpa using hηt0)).1.le
    have hΔ := outside_mFun_diff_le σ hDτ.nonneg hN0 hzim hηle hηtd'
    have hΨt : Psi N σ (↑E + ↑ηt * Complex.I) ≤ (√(2 * Cim) + 1) * B := by
      unfold Psi
      have hzt : (↑E + ↑ηt * Complex.I : ℂ).im = ηt := by simp
      rw [hzt, ← hItdef, ← hBdef]
      have h1 : It / ((N : ℝ) * ηt) ≤ 2 * Cim * B ^ 2 := by
        rw [div_eq_mul_one_div, ← hBdef, sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hIt hB0.le
      have h2 : √(It / ((N : ℝ) * ηt)) ≤ √(2 * Cim) * B := by
        calc √(It / ((N : ℝ) * ηt)) ≤ √(2 * Cim * B ^ 2) := Real.sqrt_le_sqrt h1
          _ = √(2 * Cim) * B := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0.le]
      linarith
    have hBζ : B ≤ K₆ * ζ := by
      have hlow := outside_arith_low hn0 hηt0 hzim (hηle.trans (hηtκ.trans (by linarith)))
        hNηt hη₁κ hcim (hLB η hzim hzτ)
      rw [← hBdef] at hlow
      have hs : 0 < √(cim / √2) := Real.sqrt_pos.2 (by positivity)
      rw [hK₆, ← div_eq_inv_mul, le_div_iff₀ hs]
      linarith
    have hK56 : K₅ * K₆ ≤ (N : ℝ) ^ (ε / 2) := (le_max_left _ _).trans T8
    -- `|1 + σ_i m(z)| ≥ c_x/2`
    have hBsmall : τ⁻¹ * (4 * Cim * B) ≤ cx / 2 := by
      have hB2 : B ^ 2 * ((N : ℝ) * √κ) = 1 := by rw [← hNηt, hBdef]; field_simp
      have hKc' : Kc ≤ (N : ℝ) * √κ := T7.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hκm) hn0.le)
      have hsq : (8 * τ⁻¹ * Cim / cx * B) ^ 2 ≤ 1 := by
        rw [mul_pow, ← hKc, ← hB2, mul_comm (B ^ 2)]
        exact mul_le_mul_of_nonneg_right hKc' (by positivity)
      have h1 : 8 * τ⁻¹ * Cim / cx * B ≤ 1 :=
        (pow_le_one_iff_of_nonneg (by positivity) two_ne_zero).1 hsq
      have e : τ⁻¹ * (4 * Cim * B) = (8 * τ⁻¹ * Cim / cx * B) * (cx / 2) := by
        field_simp; ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) h1
    have hcz : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑η * Complex.I)‖ := by
      intro i
      have h1 := hcxt i
      have h2 : ‖(1 : ℂ) + σ i * mFun N σ (↑E + ↑ηt * Complex.I)‖ ≤
          ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑η * Complex.I)‖ +
            ‖(σ i : ℂ) * (mFun N σ (↑E + ↑η * Complex.I) - mFun N σ (↑E + ↑ηt * Complex.I))‖ := by
        have e : (1 : ℂ) + σ i * mFun N σ (↑E + ↑ηt * Complex.I) =
            (1 + (σ i : ℂ) * mFun N σ (↑E + ↑η * Complex.I)) -
              (σ i : ℂ) * (mFun N σ (↑E + ↑η * Complex.I) - mFun N σ (↑E + ↑ηt * Complex.I)) := by
          ring
        rw [e]
        exact norm_sub_le _ _
      have h3 : ‖(σ i : ℂ) * (mFun N σ (↑E + ↑η * Complex.I) -
          mFun N σ (↑E + ↑ηt * Complex.I))‖ ≤ τ⁻¹ * (4 * Cim * B) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hDτ.nonneg i)]
        exact mul_le_mul (hσle i) (hΔ.trans (by linarith)) (norm_nonneg _) (by positivity)
      rw [hcdef]
      linarith
    have hczt : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ (↑E + ↑ηt * Complex.I)‖ :=
      fun i => (by linarith : c ≤ cx).trans (hcxt i)
    have hG := hg N hNg M Sig X hm hreg
    unfold HighProbAt at hG
    intro v w
    have hA₁ := hLt v w
    have hA₂ := hLt v v
    have hA₃ := hLt w w
    unfold DomAt at hA₁ hA₂ hA₃ ⊢
    refine le_trans (outside_union4 ?_) (outside_four_le T1 hG hA₁ hA₂ hA₃)
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq,
      not_lt] at hn hω
    obtain ⟨⟨⟨hωG, h₁⟩, h₂⟩, h₃⟩ := hn
    -- every eigenvalue is at distance `≥ η̃` from `E`
    have hgapω : ∀ j, ηt ≤ |specOf (QN Sig (X ω)) j - E| := by
      intro j
      set l := specOf (QN Sig (X ω)) j with hl
      by_cases hl3 : 3 * τ / 4 ≤ l
      · have h1 := hωG j (Or.inl (Set.mem_Ici.2 hl3))
        have h2 := Metric.infDist_le_infDist_add_dist (x := E) (y := l)
          (s := (varrho N σ).support)
        rw [Real.dist_eq, abs_sub_comm] at h2
        have h3 : 2 * (N : ℝ) ^ (-2 / 3 + τ / 2) ≤ d := T2.trans hzd
        linarith
      · rw [not_le] at hl3
        rw [abs_sub_comm, abs_of_pos (by linarith [hzre.1])]
        linarith [hzre.1]
    have hdet := outside_det hm.sigma.posDef (X ω) hzim hηle hgapω hc0 hc1 hcz hczt v w
    have hv : 0 ≤ testNorm v := Real.sqrt_nonneg _
    have hw : 0 ≤ testNorm w := Real.sqrt_nonneg _
    have hΨt0 : 0 ≤ Psi N σ (↑E + ↑ηt * Complex.I) := by
      unfold Psi
      have : (↑E + ↑ηt * Complex.I : ℂ).im = ηt := by simp
      rw [this]
      positivity
    have hfin := outside_arith_collect hv hw hc0 hIt0 hCim hB0.le hdet h₁ h₂ h₃ hΨt hIt hΔ hP1
      hK₅ hBζ hK56 hΨt0 hζ0
    rw [hPP] at hω
    linarith

example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 10) gaussMoment M N Sig (gaussX M N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → 1 / 10 / 2 ≤ edgeVal N (specOf Sig) k →
      RegularEdge (1 / 10 / 2) N (specOf Sig) k) →
    ∀ z : ℂ, z.re ∈ Set.Icc (1 / 10) (1 / 10)⁻¹ → 0 < z.im → z.im ≤ (1 / 10)⁻¹ →
      (N : ℝ) ^ (-2 / 3 + 1 / 10 : ℝ) ≤ Metric.infDist z.re (varrho N (specOf Sig)).support →
      ODomMatAt N 1 1 (fun ω => lawMat Sig (gaussX M N ω) z)
        (fun _ => √((mFun N (specOf Sig) z).im / (N * z.im))) := by
  obtain ⟨N₀, h⟩ := G_outside (1 / 10) gaussMoment 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm he z h1 h2 h3 h4 => h N hN M Sig (gaussX M N) hm he z h1 h2 h3 h4⟩

/-! ### Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1` (`φ = 1/2`); `supp ϱ ⊆ [0, 12]` by Lemma 2.5 at
`τ = 1/2`, so `E = 20` is at distance `≥ 8` from `supp ϱ`. -/

/-- `supp ϱ ⊆ [0, 12]` for `M = 1`, `N = 2`, `σ = 1`, so `dist(20, supp ϱ) ≥ 1`. -/
private lemma outside_mp_dist :
    (1 : ℝ) ≤ Metric.infDist 20 (varrho 2 (fun _ : Fin 1 => (1 : ℝ))).support := by
  set σ : Fin 1 → ℝ := fun _ => 1
  have hσ : ∀ i, 0 ≤ σ i := fun _ => zero_le_one
  have hS : (posVals σ).Nonempty := ⟨1, by
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨0, rfl⟩, one_pos⟩⟩
  have := isProbabilityMeasure_varrho 2 σ hσ two_pos
  have hp := (card_innerCrit 2 σ hσ two_pos hS).2
  have ha := edgeVal_mem_Icc 2 σ hσ two_pos hS (τ := 1 / 2) (by norm_num)
    (by norm_num [phiRatio]) (by norm_num [phiRatio])
    (fun _ => by norm_num [σ]) (k := 1) le_rfl (by omega)
  have hsub : (varrho 2 σ).support ⊆ Set.Icc 0 (edgeVal 2 σ 1) := by
    refine Measure.support_subset_of_isClosed isClosed_Icc ?_
    rw [mem_ae_iff]
    exact varrho_compl_Icc_edgeVal 2 σ hσ two_pos hS
  have hne : (varrho 2 σ).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  rw [Metric.le_infDist hne]
  intro y hy
  have h1 := (hsub hy).2
  have h2 := ha.2
  rw [Real.dist_eq, abs_of_pos (by norm_num at h2 ⊢; linarith)]
  norm_num at h2 ⊢
  linarith

/-- `im_mFun_ratio` at `M = 1`, `N = 2`, `σ = 1`, `E = 20`, `η₁ = 1`, `η = 1/2`. -/
example : (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (↑(20 : ℝ) + ↑(1 : ℝ) * Complex.I)).im / 1 ≤
      (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (↑(20 : ℝ) + ↑(1 / 2 : ℝ) * Complex.I)).im / (1 / 2) ∧
    (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (↑(20 : ℝ) + ↑(1 / 2 : ℝ) * Complex.I)).im / (1 / 2) ≤
      2 * ((mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (↑(20 : ℝ) + ↑(1 : ℝ) * Complex.I)).im / 1) :=
  im_mFun_ratio _ (fun _ => zero_le_one) two_pos (by norm_num) (by norm_num) outside_mp_dist

/-- `resolvent_compare` at `K = 2`, `λ = (0, 3)`, `a = (1, 1)`, `b = (1, −1)`, `E = 1`,
`η = 1/2`, `η' = 1`. -/
example : ‖∑ k, (((![(0 : ℝ), 3] k : ℂ) - (↑(1 : ℝ) + ↑(1 / 2 : ℝ) * Complex.I))⁻¹ -
        ((![(0 : ℝ), 3] k : ℂ) - (↑(1 : ℝ) + ↑(1 : ℝ) * Complex.I))⁻¹) *
        ((![(1 : ℝ), 1] k * ![(1 : ℝ), -1] k : ℝ) : ℂ)‖ ≤
      2 * √(∑ k, ![(1 : ℝ), 1] k ^ 2 *
        (((![(0 : ℝ), 3] k : ℂ) - (↑(1 : ℝ) + ↑(1 : ℝ) * Complex.I))⁻¹).im) *
        √(∑ k, ![(1 : ℝ), -1] k ^ 2 *
          (((![(0 : ℝ), 3] k : ℂ) - (↑(1 : ℝ) + ↑(1 : ℝ) * Complex.I))⁻¹).im) :=
  resolvent_compare _ _ _ (by norm_num) (by norm_num) (by intro k; fin_cases k <;> norm_num)

end Anisotropic

#print axioms Anisotropic.im_mFun_ratio
#print axioms Anisotropic.resolvent_compare
#print axioms Anisotropic.G_outside
