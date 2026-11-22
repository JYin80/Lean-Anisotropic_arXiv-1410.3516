module

public import Anisotropic.MainDefs
public import Anisotropic.Probability.NormBound.Main
public import Anisotropic.Probability.Geometry.SphereNet

@[expose] public section

/-!
# Gaussian ensembles and the lower bound `c ≤ E₁₁` of Lemma 10.4

A random `K × N` matrix with independent `N(0, 1/N)` entries, the Gaussian case of the model of
Section 2.1. Contents:
* such a matrix satisfies the entry conditions of Assumption 2.1, with `C_p` the absolute moments
  of the standard Gaussian;
* the small-ball bound `P(|Xᵀu|² ≤ a) ≤ (e a)^{N/2}` for a fixed unit vector `u`, by Chernoff's
  bound: the coordinates of `Xᵀu` are independent `N(0, 1/N)` variables and
  `E e^{-tY²} = (1 + 2t/N)^{-1/2}` for `Y ~ N(0, 1/N)`;
* the lower bound of Lemma 10.4 (`lem:Gaussian counting`): for a Gaussian `d × N` block with
  `d ≤ (1-c) N`, `|Xᵀu|² ≥ c' |u|²` for all `u` with high probability. The proof takes a net of
  the unit sphere, applies the small-ball bound at each net point, and passes from the net to the
  sphere with the bound `‖XᵀX‖ ≤ C₀` of Lemma 4.8.
* a concrete Gaussian ensemble on the product space `Fin K × Fin N → ℝ`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- Independent `N(0, 1/N)` entries. -/
structure IsGaussianEnsemble {Ω : Type*} [MeasureSpace Ω] {K N : ℕ}
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) : Prop where
  measurable : ∀ i μ, Measurable fun ω => X ω i μ
  indep : iIndepFun (fun (p : Fin K × Fin N) ω => X ω p.1 p.2) ℙ
  law : ∀ i μ, (ℙ : Measure Ω).map (fun ω => X ω i μ) = gaussianReal 0 (N : ℝ≥0)⁻¹

/-- Absolute moments of the standard Gaussian. -/
def gaussMoment (m : ℕ) : ℝ := ∫ x, |x| ^ m ∂(gaussianReal 0 1)

section R04

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Each entry of a Gaussian ensemble has law `N(0, 1/N)`. -/
private lemma gaussianLower_hasLaw {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (i : Fin K) (μ : Fin N) :
    HasLaw (fun ω => X ω i μ) (gaussianReal 0 (N : ℝ≥0)⁻¹) ℙ :=
  ⟨(hX.measurable i μ).aemeasurable, hX.law i μ⟩

/-- A Gaussian ensemble satisfies the entry conditions with `C = gaussMoment`. -/
theorem IsGaussianEnsemble.entryAssumption {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hN : 1 ≤ N) : EntryAssumption gaussMoment X := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hscale : ∀ i μ, HasLaw (fun ω => Real.sqrt N * X ω i μ) (gaussianReal 0 1) ℙ := by
    intro i μ
    have h := gaussianReal_const_mul (gaussianLower_hasLaw hX i μ) (Real.sqrt N)
    convert h using 2
    · simp
    · ext
      simp [Real.sq_sqrt (Nat.cast_nonneg N), hN0]
  refine ⟨hX.measurable, hX.indep, fun i μ => ?_, fun i μ => ?_, fun p i μ => ?_, fun p i μ => ?_⟩
  · rw [(gaussianLower_hasLaw hX i μ).integral_eq, integral_id_gaussianReal]
  · have h := (gaussianLower_hasLaw hX i μ).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h]
    have hv := variance_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)⁻¹)
    rw [variance_of_integral_eq_zero (by fun_prop) (by simp)] at hv
    simp only [id] at hv
    rw [hv]
    simp
  · have hint : Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 1) := by
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · simpa [Real.norm_eq_abs] using
          (memLp_id_gaussianReal (μ := 0) (v := 1) (p : ℝ≥0)).integrable_norm_pow
            (by omega)
    exact (hscale i μ).integrable_comp (f := fun x : ℝ => |x| ^ p) hint
  · have h := (hscale i μ).integral_comp (f := fun x : ℝ => |x| ^ p) (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h, gaussMoment]

/-- `E e^{-t Z²} = (1 + 2 t v)^{-1/2}` for `Z ~ N(0, v)`, `v > 0`, `t ≥ 0`. -/
private lemma gaussianLower_integral_exp {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, Real.exp (-t * x ^ 2) ∂(gaussianReal 0 v) = Real.sqrt (1 / (1 + 2 * t * v)) := by
  have hv' : (0 : ℝ) < v := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  have h : ∀ x : ℝ, gaussianPDFReal 0 v x • Real.exp (-t * x ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(1 / (2 * v) + t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_inv,
    ← Real.sqrt_mul (inv_nonneg.2 (by positivity))]
  congr 1
  field_simp

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- A linear combination `∑_{i ∈ s} u_i f_i` of independent `N(0, v)` variables has law
`N(0, v ∑_{i ∈ s} u_i²)`. -/
private lemma gaussianLower_hasLaw_sum {ι : Type*} {f : ι → Ω → ℝ} {v : ℝ≥0}
    (hind : iIndepFun f ℙ) (hmeas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, HasLaw (f i) (gaussianReal 0 v) ℙ) (u : ι → ℝ) (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, u i * f i ω)
      (gaussianReal 0 ((∑ i ∈ s, u i ^ 2).toNNReal * v)) ℙ := by
  classical
  have hind' : iIndepFun (fun i ω => u i * f i ω) ℙ :=
    hind.comp (fun i x => u i * x) fun i => measurable_const_mul (u i)
  have hmeas' : ∀ i, Measurable fun ω => u i * f i ω := fun i => (hmeas i).const_mul (u i)
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨aemeasurable_const, ?_⟩
    have := hind.isProbabilityMeasure
    simp [gaussianReal_zero_var]
  | insert j s hj ih =>
    have hY := gaussianReal_const_mul (hlaw j) (u j)
    have hindep : IndepFun (fun ω => u j * f j ω) (fun ω => ∑ i ∈ s, u i * f i ω) ℙ := by
      have h := (hind'.indepFun_finsetSum_of_notMem hmeas' hj).symm
      convert h using 1
      ext ω
      simp
    have h := gaussianReal_add_gaussianReal_of_indepFun hindep hY ih
    refine ⟨(Finset.measurable_sum _ fun i _ => hmeas' i).aemeasurable, ?_⟩
    have hfun : (fun ω => ∑ i ∈ insert j s, u i * f i ω) =
        (fun ω => u j * f j ω) + fun ω => ∑ i ∈ s, u i * f i ω := by
      ext ω
      simp [Finset.sum_insert hj]
    rw [hfun, h]
    congr 1
    · simp
    · ext
      have h1 : (0 : ℝ) ≤ ∑ i ∈ s, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h2 : (0 : ℝ) ≤ u j ^ 2 + ∑ i ∈ s, u i ^ 2 := by positivity
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Finset.sum_insert hj,
        Real.coe_toNNReal _ h1, Real.coe_toNNReal _ h2]
      ring

/-- The columns `(X_{iμ})_i`, `μ ∈ Fin N`, of a Gaussian ensemble are independent. -/
private lemma gaussianLower_iIndepFun_cols {d N : ℕ} {X : Ω → Matrix (Fin d) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) :
    iIndepFun (fun (μ : Fin N) ω => fun i : Fin d => X ω i μ) ℙ := by
  set g : Measure ℝ := gaussianReal 0 (N : ℝ≥0)⁻¹
  have h1 : iIndepFun (fun (q : Fin N × Fin d) ω => X ω q.2 q.1) ℙ :=
    hX.indep.precomp (g := Prod.swap) Prod.swap_injective
  have hm : Measurable fun ω (q : Fin N × Fin d) => X ω q.2 q.1 :=
    measurable_pi_iff.2 fun q => hX.measurable q.2 q.1
  have h2 : HasLaw (fun ω (q : Fin N × Fin d) => X ω q.2 q.1) (Measure.infinitePi fun _ => g) ℙ :=
    h1.hasLaw_infinitePi (fun q => gaussianLower_hasLaw hX q.2 q.1) hm.aemeasurable
  have h3 : HasLaw (fun ω (μ : Fin N) (i : Fin d) => X ω i μ)
      (Measure.infinitePi fun _ : Fin N => Measure.infinitePi fun _ : Fin d => g) ℙ :=
    HasLaw.comp (Y := MeasurableEquiv.curry (Fin N) (Fin d) ℝ)
      ⟨(MeasurableEquiv.measurable _).aemeasurable, Measure.infinitePi_map_curry fun _ _ => g⟩ h2
  have h4 : ∀ μ : Fin N, HasLaw (fun ω (i : Fin d) => X ω i μ) (Measure.infinitePi fun _ => g) ℙ :=
    fun μ => HasLaw.comp ⟨(measurable_pi_apply μ).aemeasurable, Measure.infinitePi_map_eval _ μ⟩ h3
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi h4 h3.aemeasurable).2 h3

/-- `x^{N/2} = (√x)^N` for `x ≥ 0`. -/
private lemma gaussianLower_rpow_half {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    x ^ ((N : ℝ) / 2) = Real.sqrt x ^ N := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  ring_nf

/-- Small ball for a fixed unit vector: `P(|Xᵀu|² ≤ a) ≤ (e a)^{N/2}`. -/
theorem measure_normSq_le {d N : ℕ} {X : Ω → Matrix (Fin d) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hN : 1 ≤ N) (u : Fin d → ℝ) (hu : u ⬝ᵥ u = 1) {a : ℝ}
    (ha : 0 < a) :
    ℙ {ω | (X ω)ᵀ *ᵥ u ⬝ᵥ (X ω)ᵀ *ᵥ u ≤ a} ≤
      ENNReal.ofReal ((Real.exp 1 * a) ^ ((N : ℝ) / 2)) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set v : ℝ≥0 := (N : ℝ≥0)⁻¹ with hv
  have hv0 : v ≠ 0 := by
    rw [hv]
    exact inv_ne_zero (by exact_mod_cast (by omega : N ≠ 0))
  have hvN : (v : ℝ) = 1 / N := by rw [hv]; simp
  set Y : Fin N → Ω → ℝ := fun μ ω => ∑ i, u i * X ω i μ with hY
  have hYm : ∀ μ, Measurable (Y μ) := fun μ =>
    Finset.measurable_sum _ fun i _ => (hX.measurable i μ).const_mul _
  have hYlaw : ∀ μ, HasLaw (Y μ) (gaussianReal 0 v) ℙ := by
    intro μ
    have hinj : Function.Injective fun i : Fin d => (i, μ) := fun i j h => (Prod.mk.inj h).1
    have h := gaussianLower_hasLaw_sum (f := fun i ω => X ω i μ)
      (hX.indep.precomp (g := fun i : Fin d => (i, μ)) hinj) (fun i => hX.measurable i μ)
      (fun i => gaussianLower_hasLaw hX i μ) u Finset.univ
    have hsum : (∑ i, u i ^ 2).toNNReal = 1 := by
      have : ∑ i, u i ^ 2 = u ⬝ᵥ u := by simp [dotProduct, sq]
      rw [this, hu, Real.toNNReal_one]
    rw [hsum, one_mul] at h
    exact h
  have hZind : iIndepFun (fun μ ω => Y μ ω ^ 2) ℙ :=
    (gaussianLower_iIndepFun_cols hX).comp (fun _ x => (∑ i, u i * x i) ^ 2)
      fun _ => by fun_prop
  set S : Ω → ℝ := ∑ μ, fun ω => Y μ ω ^ 2 with hS
  have hSapp : ∀ ω, S ω = ∑ μ, Y μ ω ^ 2 := fun ω => by simp [hS]
  have hset : {ω | (X ω)ᵀ *ᵥ u ⬝ᵥ (X ω)ᵀ *ᵥ u ≤ a} = {ω | S ω ≤ a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hSapp, hY, dotProduct, mulVec, transpose_apply, sq]
    simp_rw [mul_comm (u _)]
  set t : ℝ := N / (2 * a) with ht
  have ht0 : 0 ≤ t := by positivity
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => by
    rw [hSapp]; exact Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hSm : Measurable S := by
    rw [show S = fun ω => ∑ μ, Y μ ω ^ 2 from funext hSapp]
    exact Finset.measurable_sum _ fun μ _ => (hYm μ).pow_const 2
  have hint : Integrable (fun ω => Real.exp (-t * S ω)) ℙ := by
    refine Integrable.of_bound (hSm.const_mul _).exp.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := hS0 ω
    nlinarith
  have hch := measure_le_le_exp_mul_mgf (μ := ℙ) (X := S) a (t := -t) (by linarith) hint
  rw [hS, hZind.mgf_sum (fun μ => (hYm μ).pow_const 2)] at hch
  have hfac : ∀ μ, mgf (fun ω => Y μ ω ^ 2) ℙ (-t) = Real.sqrt (a / (1 + a)) := by
    intro μ
    have h := (hYlaw μ).integral_comp (f := fun x => Real.exp (-t * x ^ 2)) (by fun_prop)
    simp only [Function.comp_def] at h
    rw [mgf, h, gaussianLower_integral_exp hv0 ht0, hvN, ht]
    congr 1
    field_simp
    ring
  simp only [hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin, neg_neg] at hch
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
  rw [gaussianLower_rpow_half (by positivity), show t * a = (N : ℝ) * (1 / 2) by
    rw [ht]; field_simp, Real.exp_nat_mul, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ N
  rw [Real.exp_half 1, ← Real.sqrt_mul (Real.exp_pos 1).le]
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (div_le_self ha.le (by linarith)) (Real.exp_pos 1).le)

/-- The squared Euclidean norm of `x` read in `EuclideanSpace ℝ (Fin n)` is `x ⬝ᵥ x`. -/
private lemma gaussianLower_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Net-to-sphere step: if `‖AᵀA‖ ≤ C₁` and `|Aᵀw|² > s²` on an `η`-net `T` of the unit sphere
with `η = s/(2√C₁)`, then `|Aᵀu|² ≥ (s²/4) |u|²` for every `u`. -/
private lemma gaussianLower_net {d N : ℕ} (A : Matrix (Fin d) (Fin N) ℝ) {s C₁ : ℝ}
    (hs : 0 < s) (hC : 0 < C₁) (hA : ‖Aᵀ * A‖ ≤ C₁) (T : Finset (Fin d → ℝ))
    (hT : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 →
      ∃ w ∈ T, (u - w) ⬝ᵥ (u - w) ≤ (s / (2 * Real.sqrt C₁)) ^ 2)
    (hgood : ∀ w ∈ T, s ^ 2 < Aᵀ *ᵥ w ⬝ᵥ Aᵀ *ᵥ w) (u : Fin d → ℝ) :
    s ^ 2 / 4 * (u ⬝ᵥ u) ≤ Aᵀ *ᵥ u ⬝ᵥ Aᵀ *ᵥ u := by
  set e : ∀ {n : ℕ}, (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 x
  have hsC : 0 < Real.sqrt C₁ := Real.sqrt_pos.2 hC
  -- `‖Aᵀ‖ ≤ √C₁`
  have hAt : ‖Aᵀ‖ ≤ Real.sqrt C₁ := by
    have h1 : ‖Aᵀ‖ = ‖A‖ := by
      simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose A
    have h2 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
      simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose_mul_self A
    rw [h1]
    rw [h2] at hA
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hop : ∀ x : Fin d → ℝ, ‖e (Aᵀ *ᵥ x)‖ ≤ ‖Aᵀ‖ * ‖e x‖ := fun x =>
    l2_opNorm_mulVec Aᵀ (e x)
  -- unit vectors
  have hunit : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 → s ^ 2 / 4 ≤ Aᵀ *ᵥ u ⬝ᵥ Aᵀ *ᵥ u := by
    intro u hu
    obtain ⟨w, hw, huw⟩ := hT u hu
    have hnw : s < ‖e (Aᵀ *ᵥ w)‖ := by
      have h := hgood w hw
      rw [← gaussianLower_norm_sq] at h
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h
    have hnd : ‖e (u - w)‖ ≤ s / (2 * Real.sqrt C₁) := by
      rw [← gaussianLower_norm_sq] at huw
      exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) huw
    have hsplit : e (Aᵀ *ᵥ w) = e (Aᵀ *ᵥ u) - e (Aᵀ *ᵥ (u - w)) := by
      rw [mulVec_sub]
      simp [e]
    have htri : ‖e (Aᵀ *ᵥ w)‖ ≤ ‖e (Aᵀ *ᵥ u)‖ + ‖e (Aᵀ *ᵥ (u - w))‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    have hdiff : ‖e (Aᵀ *ᵥ (u - w))‖ ≤ s / 2 := by
      calc ‖e (Aᵀ *ᵥ (u - w))‖ ≤ ‖Aᵀ‖ * ‖e (u - w)‖ := hop _
        _ ≤ Real.sqrt C₁ * (s / (2 * Real.sqrt C₁)) :=
          mul_le_mul hAt hnd (norm_nonneg _) hsC.le
        _ = s / 2 := by field_simp
    have hge : s / 2 ≤ ‖e (Aᵀ *ᵥ u)‖ := by linarith
    rw [← gaussianLower_norm_sq]
    nlinarith
  -- general vectors by homogeneity
  have hnn : 0 ≤ u ⬝ᵥ u := by rw [← gaussianLower_norm_sq]; positivity
  rcases hnn.lt_or_eq with hpos | hzero
  · set ρ : ℝ := Real.sqrt (u ⬝ᵥ u) with hρ
    have hρpos : 0 < ρ := Real.sqrt_pos.2 hpos
    have hρsq : ρ ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hpos.le
    have h1 : (ρ⁻¹ • u) ⬝ᵥ (ρ⁻¹ • u) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, ← hρsq, smul_eq_mul, smul_eq_mul]
      field_simp
    have h2 := hunit _ h1
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h2
    rw [← hρsq]
    have h3 : s ^ 2 / 4 ≤ (Aᵀ *ᵥ u ⬝ᵥ Aᵀ *ᵥ u) / ρ ^ 2 := by
      calc s ^ 2 / 4 ≤ ρ⁻¹ * (ρ⁻¹ * (Aᵀ *ᵥ u ⬝ᵥ Aᵀ *ᵥ u)) := h2
        _ = (Aᵀ *ᵥ u ⬝ᵥ Aᵀ *ᵥ u) / ρ ^ 2 := by field_simp
    rwa [le_div_iff₀ (by positivity)] at h3
  · rw [← hzero, mul_zero, ← gaussianLower_norm_sq]
    positivity

/-- `2 N^D ≤ 2^N` for all large `N`. -/
private lemma gaussianLower_two_pow (D : ℝ) : ∃ N₁ : ℕ, ∀ N ≥ N₁, 2 * (N : ℝ) ^ D ≤ 2 ^ N := by
  set k : ℕ := ⌈D⌉₊
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k one_lt_two).eventually
    (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 h
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have h1 : (N : ℝ) ^ D ≤ (N : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (Nat.le_ceil D)
  have h2 := hN₁ N (le_of_max_le_left hN)
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

/-- Lemma 10.4's lower bound: for a Gaussian `d × N` block with `d ≤ (1-c) N`,
`λ_min(X₁ X₁ᵀ) ≥ c'` with high probability. -/
theorem lambdaMin_ge {c : ℝ} (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (d : ℕ) (X : Ω → Matrix (Fin d) (Fin N) ℝ), IsGaussianEnsemble X →
      (d : ℝ) ≤ (1 - c) * N →
      HighProbAt N D {ω | ∀ u : Fin d → ℝ, c' * (u ⬝ᵥ u) ≤ (X ω)ᵀ *ᵥ u ⬝ᵥ (X ω)ᵀ *ᵥ u} := by
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le (τ := 1) one_pos le_rfl
  set C₁ : ℝ := max C₀ 1 with hC₁def
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁ : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  have hsC₁ : 1 ≤ Real.sqrt C₁ := Real.one_le_sqrt.2 hC₁1
  set r : ℝ := 6 * Real.sqrt C₁ with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hse : 1 ≤ Real.sqrt (Real.exp 1) :=
    Real.one_le_sqrt.2 (Real.one_le_exp zero_le_one)
  set q : ℝ := 2 * r * Real.sqrt (Real.exp 1) with hq
  have hq1 : 1 < q := by
    rw [hq]; nlinarith
  set s : ℝ := q ^ (-(1 / c)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by linarith) _
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by simp [hc])
  have hsc : s ^ c = q⁻¹ := by
    rw [hs, ← Real.rpow_mul (by linarith), show -(1 / c) * c = -1 by field_simp,
      Real.rpow_neg_one]
  set η : ℝ := s / (2 * Real.sqrt C₁) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]
    linarith
  refine ⟨s ^ 2 / 4, by positivity, fun D => ?_⟩
  obtain ⟨N₂, hN₂⟩ := hC₀ gaussMoment (D + 1)
  obtain ⟨N₁, hN₁⟩ := gaussianLower_two_pow D
  refine ⟨max (max N₂ N₁) 2, fun N hN => ?_⟩
  intro Ω _ _ d X hX hd
  have hNN₂ : N₂ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hdNr : (d : ℝ) ≤ N := by nlinarith
  have hdN : d ≤ N := by exact_mod_cast hdNr
  have hB := hN₂ N hNN₂ d X (hX.entryAssumption (by omega)) (by simpa using hdNr)
  obtain ⟨T, hTu, hTcard, hTnet⟩ := exists_sphere_net d hη0 hη1
  set U : Set Ω := ⋃ w ∈ T, {ω | (X ω)ᵀ *ᵥ w ⬝ᵥ (X ω)ᵀ *ᵥ w ≤ s ^ 2} with hU
  have hsub : {ω | ∀ u : Fin d → ℝ, s ^ 2 / 4 * (u ⬝ᵥ u) ≤ (X ω)ᵀ *ᵥ u ⬝ᵥ (X ω)ᵀ *ᵥ u}ᶜ ⊆
      U ∪ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ := by
    intro ω hω
    by_contra hcon
    simp only [hU, Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq,
      not_or, not_exists, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hω (gaussianLower_net (X ω) hs0 hC₁ ((not_lt.1 h2).trans (le_max_left _ _)) T hTnet
      fun w hw => h1 w hw)
  -- the net union bound
  have hreal : (T.card : ℝ) * (Real.exp 1 * s ^ 2) ^ ((N : ℝ) / 2) ≤ (1 / 2) ^ N := by
    rw [gaussianLower_rpow_half (by positivity), Real.sqrt_mul (Real.exp_pos 1).le,
      Real.sqrt_sq hs0.le]
    have h3η : 3 / η = r / s := by
      rw [hη, hr]; field_simp; ring
    have hcard : (T.card : ℝ) ≤ (r / s) ^ d := h3η ▸ hTcard
    have hNd : c * N ≤ ((N - d : ℕ) : ℝ) := by
      rw [Nat.cast_sub hdN]; nlinarith
    have hpow : s ^ (N - d) ≤ q⁻¹ ^ N := by
      rw [← hsc, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      exact Real.rpow_le_rpow_of_exponent_ge hs0 hs1.le (by linarith)
    have hsplit : (r / s) ^ d * (Real.sqrt (Real.exp 1) * s) ^ N =
        r ^ d * Real.sqrt (Real.exp 1) ^ N * s ^ (N - d) := by
      have : s ^ N = s ^ (N - d) * s ^ d := by rw [← pow_add, Nat.sub_add_cancel hdN]
      rw [div_pow, show (Real.sqrt (Real.exp 1) * s) ^ N = Real.sqrt (Real.exp 1) ^ N * s ^ N
        from mul_pow _ _ _, this]
      field_simp
    calc (T.card : ℝ) * (Real.sqrt (Real.exp 1) * s) ^ N
        ≤ (r / s) ^ d * (Real.sqrt (Real.exp 1) * s) ^ N := by gcongr
      _ = r ^ d * Real.sqrt (Real.exp 1) ^ N * s ^ (N - d) := hsplit
      _ ≤ r ^ N * Real.sqrt (Real.exp 1) ^ N * q⁻¹ ^ N := by
          gcongr
      _ = (1 / 2) ^ N := by
          rw [← mul_pow, ← mul_pow, hq]
          congr 1
          field_simp
  have hnet : ℙ U ≤ ENNReal.ofReal ((1 / 2) ^ N) := by
    calc ℙ U ≤ ∑ w ∈ T, ℙ {ω | (X ω)ᵀ *ᵥ w ⬝ᵥ (X ω)ᵀ *ᵥ w ≤ s ^ 2} :=
          measure_biUnion_finset_le T _
      _ ≤ ∑ w ∈ T, ENNReal.ofReal ((Real.exp 1 * s ^ 2) ^ ((N : ℝ) / 2)) :=
          Finset.sum_le_sum fun w hw =>
            measure_normSq_le hX (by omega) w (hTu w hw) (by positivity)
      _ = ENNReal.ofReal (T.card * (Real.exp 1 * s ^ 2) ^ ((N : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((1 / 2) ^ N) := ENNReal.ofReal_le_ofReal hreal
  -- the final probability bound
  have hfin : (1 / 2 : ℝ) ^ N + (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
    have hNpos : (0 : ℝ) < N := by linarith
    have hND : 0 < (N : ℝ) ^ D := Real.rpow_pos_of_pos hNpos D
    have h1 : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) / N := by
      rw [neg_add, Real.rpow_add hNpos, Real.rpow_neg_one, div_eq_mul_inv]
    have h2 : (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) / 2 := by
      rw [Real.rpow_neg hNpos.le, _root_.one_div_pow]
      have := hN₁ N hNN₁
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      field_simp
      linarith
    have h3 : (N : ℝ) ^ (-D) / N ≤ (N : ℝ) ^ (-D) / 2 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) two_pos hNr
    linarith
  unfold HighProbAt at hB ⊢
  calc ℙ {ω | ∀ u : Fin d → ℝ, s ^ 2 / 4 * (u ⬝ᵥ u) ≤ (X ω)ᵀ *ᵥ u ⬝ᵥ (X ω)ᵀ *ᵥ u}ᶜ
      ≤ ℙ (U ∪ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ) := measure_mono hsub
    _ ≤ ℙ U + ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((1 / 2) ^ N) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hnet hB
    _ = ENNReal.ofReal ((1 / 2) ^ N + (N : ℝ) ^ (-(D + 1))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hfin

end R04

/-! ## A concrete Gaussian ensemble -/


instance (K N : ℕ) : IsProbabilityMeasure (ℙ : Measure (GaussSpace K N)) :=
  inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹))

/-- The coordinate matrix on `GaussSpace K N` has independent `N(0, 1/N)` entries. -/
theorem gaussX_isGaussianEnsemble (K N : ℕ) : IsGaussianEnsemble (gaussX K N) where
  measurable i μ := measurable_pi_apply (X := fun _ : Fin K × Fin N => ℝ) (i, μ)
  indep := iIndepFun_pi (μ := fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹)
    (X := fun _ x => x) fun _ => aemeasurable_id
  law i μ := (measurePreserving_eval (fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹)
    (i, μ)).map_eq

/-- The entry conditions for the Gaussian `1 × 2` matrix (entries `N(0, 1/2)`). -/
example : EntryAssumption gaussMoment (gaussX 1 2) :=
  (gaussX_isGaussianEnsemble 1 2).entryAssumption (by norm_num)

/-- The small-ball bound for the Gaussian `1 × 2` matrix, `u = (1)`, `a = 1/10`. -/
example : ℙ {ω | (gaussX 1 2 ω)ᵀ *ᵥ (fun _ => 1) ⬝ᵥ (gaussX 1 2 ω)ᵀ *ᵥ (fun _ => 1) ≤ 1 / 10}
    ≤ ENNReal.ofReal ((Real.exp 1 * (1 / 10)) ^ (((2 : ℕ) : ℝ) / 2)) :=
  measure_normSq_le (gaussX_isGaussianEnsemble 1 2) (by norm_num) (fun _ => 1)
    (by norm_num [dotProduct]) (by norm_num)

/-- The lower bound at `c = 1/2`, `D = 2`, for the Gaussian `1 × N` matrices (`1 ≤ N/2`). -/
example : ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    HighProbAt N 2 {ω : GaussSpace 1 N | ∀ u : Fin 1 → ℝ,
      c' * (u ⬝ᵥ u) ≤ (gaussX 1 N ω)ᵀ *ᵥ u ⬝ᵥ (gaussX 1 N ω)ᵀ *ᵥ u} := by
  obtain ⟨c', hc', h⟩ := lambdaMin_ge (c := 1 / 2) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h 2
  refine ⟨c', hc', max N₀ 2, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  exact hN₀ N (le_of_max_le_left hN) 1 (gaussX 1 N) (gaussX_isGaussianEnsemble 1 N)
    (by push_cast; linarith)

end Anisotropic

#print axioms Anisotropic.IsGaussianEnsemble
#print axioms Anisotropic.gaussMoment
#print axioms Anisotropic.IsGaussianEnsemble.entryAssumption
#print axioms Anisotropic.measure_normSq_le
#print axioms Anisotropic.lambdaMin_ge
#print axioms Anisotropic.GaussSpace
#print axioms Anisotropic.gaussX
#print axioms Anisotropic.gaussX_isGaussianEnsemble
