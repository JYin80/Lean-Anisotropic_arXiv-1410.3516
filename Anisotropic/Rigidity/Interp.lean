module

public import Anisotropic.Density.Varrho
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Gaussian.Invariance
public import Anisotropic.Gaussian.RotationLaw
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Probability.NormBound.Main
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.Gap
public import Anisotropic.Rigidity.MinMax

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 10.3: the interpolation `X(t)`, its model, the norm continuity of `Q(t)` and the count transfer -/

/-- The interpolation `X(t) = √t X₁ + √(1 − t) X₀` of Lemma 10.3 on `Ω × Ω^Gauss`. -/
def interpX {Ω : Type*} (X : Ω → Matrix (Fin M) (Fin N) ℝ) (t : ℝ) :
    Ω × GaussSpace M N → Matrix (Fin M) (Fin N) ℝ :=
  fun ω => √t • X ω.1 + √(1 - t) • gaussX M N ω.2

/-- The moment constants `2^p max(C_p, E|g|^p)` of the entries of `X(t)`. -/
def interpMoment (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  2 ^ p * max (C p) (gaussMoment p)

private lemma interp_iIndepFun_pair {Ω₁ Ω₂ ι : Type*} [MeasureSpace Ω₁] [MeasureSpace Ω₂]
    [IsProbabilityMeasure (ℙ : Measure Ω₁)] [IsProbabilityMeasure (ℙ : Measure Ω₂)] [Fintype ι]
    {f : ι → Ω₁ → ℝ} {g : ι → Ω₂ → ℝ} (hfm : ∀ i, Measurable (f i))
    (hgm : ∀ i, Measurable (g i)) (hf : iIndepFun f ℙ) (hg : iIndepFun g ℙ) :
    iIndepFun (fun i (ω : Ω₁ × Ω₂) => (f i ω.1, g i ω.2)) ℙ := by
  have hpm : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => (f i ω.1, g i ω.2) := fun i =>
    ((hfm i).comp measurable_fst).prodMk ((hgm i).comp measurable_snd)
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hpm i).aemeasurable]
  have hF := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hfm i).aemeasurable).1 hf
  have hG := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hgm i).aemeasurable).1 hg
  have hmF : Measurable fun ω i => f i ω := measurable_pi_iff.2 hfm
  have hmG : Measurable fun ω i => g i ω := measurable_pi_iff.2 hgm
  have e1 : (fun (ω : Ω₁ × Ω₂) (i : ι) => (f i ω.1, g i ω.2)) =
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm ∘
        Prod.map (fun ω i => f i ω) (fun ω i => g i ω) := rfl
  rw [e1, ← Measure.map_map (MeasurableEquiv.measurable _) (hmF.prodMap hmG),
    Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hmF hmG, hF, hG,
    ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι _ _).symm _).map_eq]
  congr 1
  funext i
  exact Measure.map_prod_map _ _ (hfm i) (hgm i)

private lemma interp_apply {Ω : Type*} (X : Ω → Matrix (Fin M) (Fin N) ℝ) (t : ℝ)
    (ω : Ω × GaussSpace M N) (i : Fin M) (μ : Fin N) :
    interpX X t ω i μ = √t * X ω.1 i μ + √(1 - t) * ω.2 (i, μ) := by
  simp [interpX, gaussX]

/-- Integrability of `|√N f|^p` gives integrability of `f^p`. -/
private lemma interp_integrable_pow {α : Type*} [MeasurableSpace α] {μ : Measure α} (hN : 1 ≤ N)
    {f : α → ℝ} (hf : Measurable f) {p : ℕ} (h : Integrable (fun x => |√(N : ℝ) * f x| ^ p) μ) :
    Integrable (fun x => f x ^ p) μ := by
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine (h.const_mul ((√(N : ℝ))⁻¹ ^ p)).mono' (hf.pow_const p).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

private lemma interp_integral_fst {Ω₁ Ω₂ : Type*} [MeasureSpace Ω₁] [MeasureSpace Ω₂]
    [IsProbabilityMeasure (ℙ : Measure Ω₁)] [IsProbabilityMeasure (ℙ : Measure Ω₂)] (f : Ω₁ → ℝ) :
    ∫ ω : Ω₁ × Ω₂, f ω.1 = ∫ x, f x := by
  rw [Measure.volume_eq_prod, integral_fun_fst]
  simp

private lemma interp_integral_snd {Ω₁ Ω₂ : Type*} [MeasureSpace Ω₁] [MeasureSpace Ω₂]
    [IsProbabilityMeasure (ℙ : Measure Ω₁)] [IsProbabilityMeasure (ℙ : Measure Ω₂)] (f : Ω₂ → ℝ) :
    ∫ ω : Ω₁ × Ω₂, f ω.2 = ∫ x, f x := by
  rw [Measure.volume_eq_prod, integral_fun_snd]
  simp

/-- `|a u + b v|^p ≤ 2^{p-1}(|u|^p + |v|^p)` for `a, b ∈ [0, 1]`. -/
private lemma interp_pow_le {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (u v : ℝ) (p : ℕ) : |a * u + b * v| ^ p ≤ 2 ^ (p - 1) * (|u| ^ p + |v| ^ p) := by
  have h1 : |a * u + b * v| ≤ |u| + |v| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha₀, abs_of_nonneg hb₀]
    have := mul_le_of_le_one_left (abs_nonneg u) ha₁
    have := mul_le_of_le_one_left (abs_nonneg v) hb₁
    linarith
  exact (pow_le_pow_left₀ (abs_nonneg _) h1 p).trans
    (add_pow_le (abs_nonneg u) (abs_nonneg v) p)

/-- Assumption 2.1 holds for `X(t)`, uniformly in `t ∈ [0, 1]`. -/
theorem isModel_interpX {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} {C : ℕ → ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) (hN : 1 ≤ N) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsModel τ (interpMoment C) M N Sig (interpX X t) := by
  have hX := hm.entries
  have hG := (gaussX_isGaussianEnsemble M N).entryAssumption hN
  set a := √t with ha
  set b := √(1 - t) with hb
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have hb₀ : 0 ≤ b := Real.sqrt_nonneg _
  have ha₁ : a ≤ 1 := Real.sqrt_le_one.2 ht₁
  have hb₁ : b ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have ha2 : a ^ 2 = t := Real.sq_sqrt ht₀
  have hb2 : b ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hap : ∀ ω i μ, interpX X t ω i μ = a * X ω.1 i μ + b * ω.2 (i, μ) := fun ω i μ =>
    interp_apply X t ω i μ
  have hxm : ∀ i μ, Measurable fun ω : Ω × GaussSpace M N => X ω.1 i μ := fun i μ =>
    (hX.measurable i μ).comp measurable_fst
  have hgm' : ∀ i μ, Measurable fun ω : GaussSpace M N => ω (i, μ) := fun i μ =>
    measurable_pi_apply (i, μ)
  have hgm : ∀ i μ, Measurable fun ω : Ω × GaussSpace M N => ω.2 (i, μ) := fun i μ =>
    (hgm' i μ).comp measurable_snd
  have hm_ent : ∀ i μ, Measurable fun ω => interpX X t ω i μ := fun i μ => by
    simp_rw [hap]
    exact ((hxm i μ).const_mul a).add ((hgm i μ).const_mul b)
  -- integrability of the powers of the two entries
  have hxi : ∀ (p : ℕ) i μ, Integrable (fun ω => X ω i μ ^ p) := fun p i μ =>
    interp_integrable_pow hN (hX.measurable i μ) (hX.integrable_moment p i μ)
  have hgi : ∀ (p : ℕ) i μ, Integrable (fun ω : GaussSpace M N => ω (i, μ) ^ p) := fun p i μ =>
    interp_integrable_pow hN (hgm' i μ) (hG.integrable_moment p i μ)
  have hxi' : ∀ (p : ℕ) i μ, Integrable (fun ω : Ω × GaussSpace M N => X ω.1 i μ ^ p) :=
    fun p i μ => by
      rw [Measure.volume_eq_prod]; exact (hxi p i μ).comp_fst _
  have hgi' : ∀ (p : ℕ) i μ, Integrable (fun ω : Ω × GaussSpace M N => ω.2 (i, μ) ^ p) :=
    fun p i μ => by
      rw [Measure.volume_eq_prod]; exact (hgi p i μ).comp_snd _
  have hxa' : ∀ (p : ℕ) i μ,
      Integrable (fun ω : Ω × GaussSpace M N => |√(N : ℝ) * X ω.1 i μ| ^ p) := fun p i μ => by
    rw [Measure.volume_eq_prod]; exact (hX.integrable_moment p i μ).comp_fst _
  have hga' : ∀ (p : ℕ) i μ,
      Integrable (fun ω : Ω × GaussSpace M N => |√(N : ℝ) * ω.2 (i, μ)| ^ p) := fun p i μ => by
    rw [Measure.volume_eq_prod]; exact (hG.integrable_moment p i μ).comp_snd _
  have hpt : ∀ (p : ℕ) i μ (ω : Ω × GaussSpace M N),
      |√(N : ℝ) * interpX X t ω i μ| ^ p ≤
        2 ^ (p - 1) * (|√(N : ℝ) * X ω.1 i μ| ^ p + |√(N : ℝ) * ω.2 (i, μ)| ^ p) := by
    intro p i μ ω
    rw [hap, show √(N : ℝ) * (a * X ω.1 i μ + b * ω.2 (i, μ)) =
      a * (√(N : ℝ) * X ω.1 i μ) + b * (√(N : ℝ) * ω.2 (i, μ)) by ring]
    exact interp_pow_le ha₀ ha₁ hb₀ hb₁ _ _ p
  have hmi : ∀ (p : ℕ) i μ,
      Integrable (fun ω : Ω × GaussSpace M N => |√(N : ℝ) * interpX X t ω i μ| ^ p) := by
    intro p i μ
    refine (((hxa' p i μ).add (hga' p i μ)).const_mul (2 ^ (p - 1))).mono'
      ((((hm_ent i μ).const_mul _).abs).pow_const p).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt p i μ ω
  refine ⟨hm.ratio_ge, hm.ratio_le, ⟨hm_ent, ?_, ?_, ?_, hmi, ?_⟩, hm.sigma⟩
  · -- independence
    have hpair := interp_iIndepFun_pair (Ω₁ := Ω) (Ω₂ := GaussSpace M N)
      (f := fun (p : Fin M × Fin N) ω => X ω p.1 p.2) (g := fun p ω => gaussX M N ω p.1 p.2)
      (fun p => hX.measurable p.1 p.2) (fun p => hgm' p.1 p.2) hX.indep hG.indep
    have hc := hpair.comp (fun _ (z : ℝ × ℝ) => a * z.1 + b * z.2)
      (fun _ => (measurable_fst.const_mul a).add (measurable_snd.const_mul b))
    have e : (fun (p : Fin M × Fin N) (ω : Ω × GaussSpace M N) => interpX X t ω p.1 p.2) =
        fun p => (fun z : ℝ × ℝ => a * z.1 + b * z.2) ∘
          fun ω : Ω × GaussSpace M N => (X ω.1 p.1 p.2, gaussX M N ω.2 p.1 p.2) := by
      funext p ω
      simp only [Function.comp_apply, hap, gaussX]
    rw [e]
    exact hc
  · -- mean
    intro i μ
    simp_rw [hap]
    rw [integral_add (((hxi' 1 i μ).const_mul a).congr (ae_of_all _ fun ω => by simp))
      (((hgi' 1 i μ).const_mul b).congr (ae_of_all _ fun ω => by simp)),
      integral_const_mul, integral_const_mul, interp_integral_fst (fun ω => X ω i μ),
      interp_integral_snd (fun ω : GaussSpace M N => ω (i, μ)), hX.mean i μ]
    have := hG.mean i μ
    simp only [gaussX] at this
    rw [this]; ring
  · -- variance
    intro i μ
    simp_rw [hap]
    have e : ∀ ω : Ω × GaussSpace M N, (a * X ω.1 i μ + b * ω.2 (i, μ)) ^ 2 =
        a ^ 2 * X ω.1 i μ ^ 2 + b ^ 2 * ω.2 (i, μ) ^ 2 +
          2 * a * b * (X ω.1 i μ * ω.2 (i, μ)) := fun ω => by ring
    simp_rw [e]
    have hx1 : Integrable fun ω => X ω i μ := by simpa using hxi 1 i μ
    have hg1 : Integrable fun ω : GaussSpace M N => ω (i, μ) := by simpa using hgi 1 i μ
    have hcross : Integrable fun ω : Ω × GaussSpace M N => X ω.1 i μ * ω.2 (i, μ) := by
      rw [Measure.volume_eq_prod]
      exact hx1.mul_prod hg1
    have i1 : Integrable fun ω : Ω × GaussSpace M N => a ^ 2 * X ω.1 i μ ^ 2 :=
      (hxi' 2 i μ).const_mul _
    have i2 : Integrable fun ω : Ω × GaussSpace M N => b ^ 2 * ω.2 (i, μ) ^ 2 :=
      (hgi' 2 i μ).const_mul _
    have i12 : Integrable fun ω : Ω × GaussSpace M N =>
        a ^ 2 * X ω.1 i μ ^ 2 + b ^ 2 * ω.2 (i, μ) ^ 2 := i1.add i2
    rw [integral_add i12 (hcross.const_mul _), integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      interp_integral_fst (fun ω => X ω i μ ^ 2),
      interp_integral_snd (fun ω : GaussSpace M N => ω (i, μ) ^ 2), hX.var i μ]
    have hv := hG.var i μ
    simp only [gaussX] at hv
    have hc : ∫ ω : Ω × GaussSpace M N, X ω.1 i μ * ω.2 (i, μ) = 0 := by
      rw [Measure.volume_eq_prod, integral_prod_mul (fun ω => X ω i μ)
        (fun ω : GaussSpace M N => ω (i, μ)), hX.mean i μ, zero_mul]
    rw [hv, hc, ha2, hb2]; ring
  · -- moments
    intro p i μ
    have hp0 : 1 ≤ gaussMoment 0 := by simp [gaussMoment]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp only [pow_zero, integral_const, smul_eq_mul, mul_one, interpMoment, one_mul,
        probReal_univ]
      exact hp0.trans (le_max_right _ _)
    · have hs : Integrable fun ω : Ω × GaussSpace M N =>
          |√(N : ℝ) * X ω.1 i μ| ^ p + |√(N : ℝ) * ω.2 (i, μ)| ^ p := (hxa' p i μ).add (hga' p i μ)
      refine (integral_mono (hmi p i μ) (hs.const_mul _) (hpt p i μ)).trans ?_
      rw [integral_const_mul, integral_add (hxa' p i μ) (hga' p i μ),
        interp_integral_fst (fun ω => |√(N : ℝ) * X ω i μ| ^ p),
        interp_integral_snd (fun ω : GaussSpace M N => |√(N : ℝ) * ω (i, μ)| ^ p)]
      have h1 := (hX.moment p i μ).trans (le_max_left (C p) (gaussMoment p))
      have h2 := hG.moment p i μ
      simp only [gaussX] at h2
      have h2 := h2.trans (le_max_right (C p) (gaussMoment p))
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [interpMoment, Nat.add_sub_cancel]
      rw [pow_succ (2 : ℝ) q]
      have h2q : (0 : ℝ) ≤ 2 ^ q := by positivity
      nlinarith

private lemma interp_norm_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

private lemma interp_norm_le_sqrt {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) {C₀ : ℝ} (h : ‖Aᵀ * A‖ ≤ C₀) : ‖A‖ ≤ √C₀ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self] at h
  exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg A])

private lemma interp_abs_sqrt_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |√u - √v| ≤ √|u - v| := by
  have hp := Real.sqrt_nonneg u
  have hq := Real.sqrt_nonneg v
  have e : u - v = (√u - √v) * (√u + √v) := by
    rw [show (√u - √v) * (√u + √v) = √u ^ 2 - √v ^ 2 by ring, Real.sq_sqrt hu, Real.sq_sqrt hv]
  refine Real.le_sqrt_of_sq_le ?_
  calc |√u - √v| ^ 2 = |√u - √v| * |√u - √v| := sq _
    _ ≤ |√u - √v| * (√u + √v) :=
        mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
    _ = |u - v| := by rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √u + √v)]

private lemma interp_sqrt_add_le {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : √t + √(1 - t) ≤ √2 := by
  refine Real.le_sqrt_of_sq_le ?_
  have h1 := Real.sq_sqrt ht₀
  have h2 := Real.sq_sqrt (sub_nonneg.2 ht₁)
  nlinarith [sq_nonneg (√t - √(1 - t))]

/-- (cont_lambda_t) in norm form: `‖Q(t) − Q(s)‖ ≤ 4√2 s₀ C₀ √|t − s|` for
`X(t) = √t X₁ + √(1−t) X₀` with `‖Σ‖ ≤ s₀` and `‖X₁ᵀX₁‖, ‖X₀ᵀX₀‖ ≤ C₀`. -/
theorem QN_interp_lip {Sig : Matrix (Fin M) (Fin M) ℝ} (X₁ X₀ : Matrix (Fin M) (Fin N) ℝ)
    {C₀ s₀ : ℝ} (hSig : ‖Sig‖ ≤ s₀) (h₁ : ‖X₁ᵀ * X₁‖ ≤ C₀) (h₀ : ‖X₀ᵀ * X₀‖ ≤ C₀) {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖QN Sig (√t • X₁ + √(1 - t) • X₀) - QN Sig (√s • X₁ + √(1 - s) • X₀)‖ ≤
      4 * √2 * s₀ * C₀ * √|t - s| := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans h₁
  have hs₀ : 0 ≤ s₀ := (norm_nonneg _).trans hSig
  have n₁ := interp_norm_le_sqrt X₁ h₁
  have n₀ := interp_norm_le_sqrt X₀ h₀
  set Xt := √t • X₁ + √(1 - t) • X₀ with hXt
  set Xs := √s • X₁ + √(1 - s) • X₀ with hXs
  have hr := Real.sqrt_nonneg C₀
  have hd1 := interp_abs_sqrt_sub_le ht.1 hs.1
  have hd0 := interp_abs_sqrt_sub_le (sub_nonneg.2 ht.2) (sub_nonneg.2 hs.2)
  rw [show (1 - t) - (1 - s) = -(t - s) by ring, abs_neg] at hd0
  have hdiff : ‖Xt - Xs‖ ≤ 2 * √|t - s| * √C₀ := by
    have e : Xt - Xs = (√t - √s) • X₁ + (√(1 - t) - √(1 - s)) • X₀ := by
      rw [hXt, hXs, sub_smul, sub_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have a1 := mul_le_mul hd1 n₁ (norm_nonneg _) (Real.sqrt_nonneg _)
    have a0 := mul_le_mul hd0 n₀ (norm_nonneg _) (Real.sqrt_nonneg _)
    exact (add_le_add a1 a0).trans (le_of_eq (by ring))
  have hnorm : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖√u • X₁ + √(1 - u) • X₀‖ ≤ √2 * √C₀ := by
    intro u hu
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have a1 := mul_le_mul_of_nonneg_left n₁ (Real.sqrt_nonneg u)
    have a0 := mul_le_mul_of_nonneg_left n₀ (Real.sqrt_nonneg (1 - u))
    have a2 := mul_le_mul_of_nonneg_right (interp_sqrt_add_le hu.1 hu.2) hr
    exact (add_le_add a1 a0).trans ((le_of_eq (by ring)).trans a2)
  have hnt := hnorm t ht
  have hns := hnorm s hs
  have e : QN Sig Xt - QN Sig Xs = Xtᵀ * Sig * (Xt - Xs) + (Xt - Xs)ᵀ * Sig * Xs := by
    simp only [QN, transpose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 : ‖Xtᵀ * Sig * (Xt - Xs)‖ ≤ ‖Xt‖ * s₀ * ‖Xt - Xs‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (l2_opNorm_mul _ _).trans ?_
    rw [interp_norm_transpose]
    exact mul_le_mul_of_nonneg_left hSig (norm_nonneg _)
  have b2 : ‖(Xt - Xs)ᵀ * Sig * Xs‖ ≤ ‖Xt - Xs‖ * s₀ * ‖Xs‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (l2_opNorm_mul _ _).trans ?_
    rw [interp_norm_transpose]
    exact mul_le_mul_of_nonneg_left hSig (norm_nonneg _)
  have hsq : √C₀ * √C₀ = C₀ := Real.mul_self_sqrt hC₀
  have hds := norm_nonneg (Xt - Xs)
  have k1 : ‖Xt‖ * s₀ * ‖Xt - Xs‖ ≤ (√2 * √C₀) * s₀ * (2 * √|t - s| * √C₀) := by
    gcongr
  have k2 : ‖Xt - Xs‖ * s₀ * ‖Xs‖ ≤ (2 * √|t - s| * √C₀) * s₀ * (√2 * √C₀) := by
    gcongr
  have : (√2 * √C₀) * s₀ * (2 * √|t - s| * √C₀) + (2 * √|t - s| * √C₀) * s₀ * (√2 * √C₀)
      = 4 * √2 * s₀ * C₀ * √|t - s| := by linear_combination (4 * √2 * s₀ * √|t - s|) * hsq
  linarith

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma interp_norm_sig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) : ‖Sig‖ ≤ τ⁻¹ := by
  have hH := hS.posDef.isHermitian
  set U := hH.eigenvectorUnitary with hU
  have hUm : (U : Matrix (Fin M) (Fin M) ℝ) ∈ unitaryGroup (Fin M) ℝ := U.2
  have hUn : ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    have h1 : ‖(U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ)‖ =
        ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ :=
      l2_opNorm_conjTranspose_mul_self _
    have h2 : (U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ) = 1 := by
      rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.1 hUm)
    have h3 : ‖(1 : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun _ => by simp
    rw [h2] at h1
    nlinarith [norm_nonneg (U : Matrix (Fin M) (Fin M) ℝ)]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  rw [hspec]
  have hD : ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin M) (Fin M) ℝ)‖ ≤ τ⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg (inv_pos.2 hτ).le |>.2 fun i => ?_
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
    rw [abs_of_pos (hS.posDef.eigenvalues_pos i)]
    exact hS.eigenvalues_le i
  have hUs : ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact hUn
  calc _ ≤ ‖(U : Matrix (Fin M) (Fin M) ℝ) * diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
        ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ := l2_opNorm_mul _ _
    _ ≤ (‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) :
          Matrix (Fin M) (Fin M) ℝ)‖) * ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * τ⁻¹) * 1 := by gcongr
    _ = τ⁻¹ := by ring

private lemma interp_QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := isHermitian_conjTranspose_mul_mul Xm hSig
  simpa [QN, conjTranspose_eq_transpose_of_trivial] using this

private lemma interpX_one {Ω : Type*} (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (ω : Ω × GaussSpace M N) : interpX X 1 ω = X ω.1 := by
  simp [interpX]

private lemma interpX_zero {Ω : Type*} (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (ω : Ω × GaussSpace M N) : interpX X 0 ω = gaussX M N ω.2 := by
  simp [interpX]

/-- `(K + 2) N^{-(D+2)} + N^{-(D+1)} ≤ N^{-D}` for `N ≥ max(K + 2, 2)`. -/
private lemma interp_union_bound {N K : ℕ} (D : ℝ) (hK : K + 2 ≤ N) (hN : 2 ≤ N) :
    (K + 2 : ℝ) * (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e1 : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-(D + 2)) * N := by
    rw [← Real.rpow_add_one hN0.ne']; ring_nf
  have e2 : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
    rw [← Real.rpow_add_one hN0.ne']; ring_nf
  have hx := Real.rpow_nonneg hN0.le (-(D + 2))
  have hK' : (K + 2 : ℝ) ≤ N := by exact_mod_cast hK
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hy := Real.rpow_nonneg hN0.le (-(D + 1))
  rw [e2]
  have : (K + 2 : ℝ) * (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-(D + 1)) := by
    rw [e1]; nlinarith
  nlinarith

/-- Lemma 10.3 (`lem:interp_Gauss`) for a threshold `θ` whose window `[θ − δ, θ + δ]` stays at
distance `≥ w` from `supp ϱ`: an exact count for `X^Gauss` gives the same count for `X`. -/
theorem interp_count (τ : ℝ) (C : ℕ → ℝ) (τW δ w D : ℝ) (hτ : 0 < τ) (hτW : 0 < τW)
    (hδ : 0 < δ) (hw : 0 < w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (θ : ℝ)
      (K : ℕ),
      IsModel τ C M N Sig X → τW ≤ θ - δ →
      (∀ E ∈ Set.Icc (θ - δ) (θ + δ), w ≤ Metric.infDist E (varrho N (specOf Sig)).support) →
      HighProbAt N (D + 1) {ω | eigCount (QN Sig (gaussX M N ω)) θ = K} →
      HighProbAt N D {ω | eigCount (QN Sig (X ω)) θ = K} := by
  by_cases hτ1 : 1 < τ
  · exact ⟨0, fun N _ Ω _ _ M Sig X θ K hm => absurd hm.tau_le_one (not_le.2 hτ1)⟩
  replace hτ1 : τ ≤ 1 := not_lt.1 hτ1
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  obtain ⟨Nn, hNn⟩ := hC₀ (interpMoment C) (D + 2)
  obtain ⟨Ng, hNg⟩ := gap_outside τ (interpMoment C) w τW (D + 2) hτ hw hτW
  set Cc : ℝ := 4 * √2 * τ⁻¹ * C₀ with hCc
  set K₃ : ℕ := ⌈(Cc / δ) ^ 2⌉₊ + 1 with hK₃
  refine ⟨max (max Nn Ng) (K₃ + 2), fun N hN Ω _ _ M Sig X θ K hm hθ hwin hgauss => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hNn', hNg'⟩, hNK⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hK₃0 : (0 : ℝ) < K₃ := by positivity
  have hH : Sig.IsHermitian := hm.sigma.posDef.isHermitian
  have hSn : ‖Sig‖ ≤ τ⁻¹ := interp_norm_sig_le hτ hm.sigma
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rwa [div_le_iff₀ hN0] at this
  -- the lattice `t_j = j / K₃`
  set tj : ℕ → ℝ := fun j => (j : ℝ) / K₃ with htj
  have htj0 : ∀ j, 0 ≤ tj j := fun j => by positivity
  have htj1 : ∀ j ≤ K₃, tj j ≤ 1 := fun j hj => by
    simp only [htj]
    rw [div_le_one hK₃0]; exact_mod_cast hj
  -- the events on `Ω × GaussSpace M N`
  set P := Ω × GaussSpace M N
  set Gj : ℕ → Set P := fun j => {ω | ∀ i, τW ≤ specOf (QN Sig (interpX X (tj j) ω)) i →
    Metric.infDist (specOf (QN Sig (interpX X (tj j) ω)) i) (varrho N (specOf Sig)).support < w}
    with hGj
  set B₁ : Set P := {ω | ‖(interpX X 1 ω)ᵀ * interpX X 1 ω‖ ≤ C₀} with hB₁
  set B₀ : Set P := {ω | ‖(interpX X 0 ω)ᵀ * interpX X 0 ω‖ ≤ C₀} with hB₀
  set SG : Set (GaussSpace M N) := {ω | eigCount (QN Sig (gaussX M N ω)) θ = K} with hSG
  set SX : Set Ω := {ω | eigCount (QN Sig (X ω)) θ = K} with hSX
  have hGjP : ∀ j ≤ K₃, (ℙ : Measure P) (Gj j)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
    fun j hj => hNg N hNg' M Sig (interpX X (tj j)) (isModel_interpX hm hN1 (htj0 j) (htj1 j hj))
  have hB₁P : (ℙ : Measure P) B₁ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
    hNn N hNn' M (interpX X 1) (isModel_interpX hm hN1 zero_le_one le_rfl).entries hMN
  have hB₀P : (ℙ : Measure P) B₀ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
    hNn N hNn' M (interpX X 0) (isModel_interpX hm hN1 le_rfl zero_le_one).entries hMN
  have hSGP : (ℙ : Measure P) (Set.univ ×ˢ SGᶜ) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_univ, one_mul]
    exact hgauss
  -- the step bound
  have hstep : Cc * √(1 / (K₃ : ℝ)) < δ := by
    rcases le_or_gt Cc 0 with h | h
    · exact (mul_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg _)).trans_lt hδ
    · have hK : (Cc / δ) ^ 2 < K₃ := by
        simp only [hK₃]; push_cast
        exact (Nat.le_ceil _).trans_lt (lt_add_one _)
      refine lt_of_pow_lt_pow_left₀ 2 hδ.le ?_
      rw [mul_pow, Real.sq_sqrt (by positivity), div_pow, div_lt_iff₀ (by positivity)] at *
      rw [← div_eq_mul_one_div, div_lt_iff₀ hK₃0]
      nlinarith
  -- the inclusion
  have hsub : SXᶜ ×ˢ (Set.univ : Set (GaussSpace M N)) ⊆
      (⋃ j ∈ Finset.range K₃, (Gj j)ᶜ) ∪ B₁ᶜ ∪ B₀ᶜ ∪ Set.univ ×ˢ SGᶜ := by
    rintro ω ⟨hω, -⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, Finset.mem_range,
      Set.mem_prod, Set.mem_univ, true_and, not_or, not_exists, not_not] at hc
    obtain ⟨⟨⟨hG, h1⟩, h0⟩, hg⟩ := hc
    apply hω
    have h1' : ‖(X ω.1)ᵀ * X ω.1‖ ≤ C₀ := by rw [← interpX_one X ω]; exact h1
    have h0' : ‖(gaussX M N ω.2)ᵀ * gaussX M N ω.2‖ ≤ C₀ := by rw [← interpX_zero X ω]; exact h0
    have hlat := eigCount_lattice (fun j => QN Sig (interpX X (tj j) ω))
      (fun j => interp_QN_isHermitian hH _) (fun _ => θ) (δ := δ) K₃ ?_ ?_
    · have eK : tj K₃ = 1 := by simp only [htj]; exact div_self hK₃0.ne'
      have e0 : tj 0 = 0 := by simp [htj]
      rw [eK, e0, interpX_one, interpX_zero] at hlat
      change eigCount (QN Sig (X ω.1)) θ = K
      rw [hlat]; exact hg
    · intro j hj
      rw [sub_self, abs_zero, add_zero]
      have hl := QN_interp_lip (Sig := Sig) (X ω.1) (gaussX M N ω.2) hSn h1' h0'
        (t := tj (j + 1)) (s := tj j) ⟨htj0 _, htj1 _ hj⟩ ⟨htj0 _, htj1 _ hj.le⟩
      have ed : |tj (j + 1) - tj j| = 1 / (K₃ : ℝ) := by
        simp only [htj]; push_cast
        rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
      rw [ed] at hl
      exact lt_of_le_of_lt hl hstep
    · intro j hj i hi
      have h := hG j hj i (hθ.trans hi.1)
      have := hwin _ hi
      linarith
  have hx := Real.rpow_nonneg hN0.le (-(D + 2))
  have hy := Real.rpow_nonneg hN0.le (-(D + 1))
  have hU : (ℙ : Measure P) (⋃ j ∈ Finset.range K₃, (Gj j)ᶜ) ≤
      K₃ * ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hGjP j (Finset.mem_range.1 hj).le).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change ℙ SXᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))
  calc ℙ SXᶜ = (ℙ : Measure P) (SXᶜ ×ˢ Set.univ) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, measure_univ, mul_one]
    _ ≤ (ℙ : Measure P) ((⋃ j ∈ Finset.range K₃, (Gj j)ᶜ) ∪ B₁ᶜ ∪ B₀ᶜ ∪ Set.univ ×ˢ SGᶜ) :=
        measure_mono hsub
    _ ≤ (ℙ : Measure P) (⋃ j ∈ Finset.range K₃, (Gj j)ᶜ) + ℙ B₁ᶜ + ℙ B₀ᶜ +
          ℙ (Set.univ ×ˢ SGᶜ) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ K₃ * ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) +
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := by
        gcongr
    _ = ENNReal.ofReal ((K₃ + 2 : ℝ) * (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add (by positivity) hx, ← ENNReal.ofReal_add (by positivity) hx,
          ← ENNReal.ofReal_add (by positivity) hy]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal (interp_union_bound D hNK hN2)

end Anisotropic

#print axioms Anisotropic.interpX
#print axioms Anisotropic.interpMoment
#print axioms Anisotropic.isModel_interpX
#print axioms Anisotropic.QN_interp_lip
#print axioms Anisotropic.interp_count
