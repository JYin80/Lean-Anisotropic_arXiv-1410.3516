module

public import Anisotropic.Framework.Domination
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Wigner.Model

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Orthogonal invariance of the GOE and its class bounds -/

/-! ## The law of the GOE

The upper-triangular entries of a GOE matrix are independent centred Gaussians with variances
`goeVar N`, and the matrix is the symmetric matrix with these upper entries. With
`⟨X, Y⟩ = (N/2) tr(XY)` on symmetric matrices, the scaled coordinates form an orthonormal basis,
so the law of the GOE is the image of the standard Gaussian of the Euclidean space of upper
entries, and `X ↦ O X Oᵀ` corresponds to a linear isometry of that space. -/

/-- The upper-triangular entries of a matrix. -/
private def goeUp {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) : UpperIdx N → ℝ :=
  fun p => X p.1.1 p.1.2

/-- The symmetric matrix with upper-triangular entries `y`. -/
private def goeSym {N : ℕ} (y : UpperIdx N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => y ⟨(min i j, max i j), min_le_max⟩

/-- The standard deviation `√(goeVar N p)` of the GOE entry at `p`. -/
private def goeSd {N : ℕ} (p : UpperIdx N) : ℝ := Real.sqrt (goeVar N p.1)

/-- The joint law of the upper-triangular GOE entries. -/
private def goeUpLaw (N : ℕ) : Measure (UpperIdx N → ℝ) :=
  Measure.pi fun p : UpperIdx N => gaussianReal 0 (goeVar N p.1)

/-- The scaling `v ↦ (√(goeVar N p) v_p)_p` from the Euclidean space of upper entries. -/
private def goeScale {N : ℕ} (v : EuclideanSpace ℝ (UpperIdx N)) : UpperIdx N → ℝ :=
  fun p => goeSd p * v.ofLp p

private lemma goe_measurable_up {N : ℕ} : Measurable (goeUp (N := N)) :=
  measurable_pi_iff.2 fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)

private lemma goe_measurable_sym {N : ℕ} : Measurable (goeSym (N := N)) :=
  Matrix.measurable_iff.2 fun _ _ => measurable_pi_apply _

private lemma goe_measurable_scale {N : ℕ} : Measurable (goeScale (N := N)) := by
  refine measurable_pi_iff.2 fun p => ?_
  exact (by fun_prop :
    Measurable fun v : EuclideanSpace ℝ (UpperIdx N) => v.ofLp p).const_mul _

private lemma goe_measurable_conj {N : ℕ} (O : Matrix (Fin N) (Fin N) ℝ) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => O * X * Oᵀ := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (Finset.measurable_sum _ fun l _ =>
    (measurable_id.eval_matrix (i := l) (j := k)).const_mul _).mul_const _

private lemma goe_sym_up {N : ℕ} {X : Matrix (Fin N) (Fin N) ℝ} (hX : Xᵀ = X) :
    goeSym (goeUp X) = X := by
  ext i j
  simp only [goeSym, goeUp]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact congrFun (congrFun hX i) j

private lemma goe_up_sym {N : ℕ} (y : UpperIdx N → ℝ) : goeUp (goeSym y) = y := by
  funext p
  simp only [goeUp, goeSym, min_eq_left p.2, max_eq_right p.2]

private lemma goe_sym_transpose {N : ℕ} (y : UpperIdx N → ℝ) : (goeSym y)ᵀ = goeSym y := by
  ext i j
  simp [goeSym, min_comm, max_comm]

private lemma goe_sd_pos {N : ℕ} (p : UpperIdx N) : 0 < goeSd p := by
  have hN : (0 : ℝ≥0) < N := by exact_mod_cast p.1.1.pos
  unfold goeSd goeVar
  apply Real.sqrt_pos.2
  split_ifs <;> positivity

/-- Each entry of a GOE matrix is a centred Gaussian with variance `goeVar N (i, j)`. -/
private lemma goe_hasLaw {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) (i j : Fin N) :
    HasLaw (fun ω => W ω i j) (gaussianReal 0 (goeVar N (i, j))) ℙ := by
  refine ⟨(hW.measurable i j).aemeasurable, ?_⟩
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hW.law_off i j h]
    simp [goeVar, h.ne]
  · rw [hW.law_diag i]
    simp [goeVar]
  · have e : (fun ω => W ω i j) = fun ω => W ω j i := by
      funext ω
      exact (congrFun (congrFun (hW.symm ω) i) j).symm
    rw [e, hW.law_off j i h]
    simp [goeVar, h.ne']

/-- A GOE matrix is the symmetric matrix of its upper entries, whose law is `goeUpLaw N`. -/
private lemma goe_map_eq {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) :
    (ℙ : Measure Ω).map W = (goeUpLaw N).map goeSym := by
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hup : (ℙ : Measure Ω).map (goeUp ∘ W) = goeUpLaw N := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun p : UpperIdx N => (hW.measurable p.1.1 p.1.2).aemeasurable)).1 hW.indep
    rw [show goeUp ∘ W = fun ω (p : UpperIdx N) => W ω p.1.1 p.1.2 from rfl, h, goeUpLaw]
    congr 1
    funext p
    exact (goe_hasLaw hW p.1.1 p.1.2).map_eq
  calc (ℙ : Measure Ω).map W = (ℙ : Measure Ω).map (goeSym ∘ goeUp ∘ W) := by
        congr 1
        funext ω
        exact (goe_sym_up (hW.symm ω)).symm
    _ = _ := by rw [← Measure.map_map goe_measurable_sym (goe_measurable_up.comp hWm), hup]

/-- `goeUpLaw N` is the image of the standard Gaussian under `goeScale`. -/
private lemma goe_upLaw_eq (N : ℕ) :
    goeUpLaw N = (stdGaussian (EuclideanSpace ℝ (UpperIdx N))).map goeScale := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map goe_measurable_scale (PiLp.continuous_toLp 2 _).measurable]
  have h1 : goeScale ∘ WithLp.toLp 2 =
      fun x (p : UpperIdx N) => (fun y : ℝ => goeSd p * y) (x p) := rfl
  rw [h1, Measure.pi_map_pi fun _ => (measurable_const_mul _).aemeasurable, goeUpLaw]
  congr 1
  funext p
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp [goeSd, Real.sq_sqrt (NNReal.coe_nonneg _)]

/-- `∑_{i,j} Y_ij² = ∑_{i ≤ j} w_ij Y_ij²` for symmetric `Y`, with `w = 1` on the diagonal and
`w = 2` off it. -/
private lemma goe_sum_sq_weighted {N : ℕ} {Y : Matrix (Fin N) (Fin N) ℝ} (hY : Yᵀ = Y) :
    ∑ p : UpperIdx N, (if p.1.1 = p.1.2 then (1 : ℝ) else 2) * Y p.1.1 p.1.2 ^ 2 =
      ∑ i, ∑ j, Y i j ^ 2 := by
  set g : Fin N × Fin N → ℝ := fun x => (if x.1 = x.2 then (1 : ℝ) else 2) * Y x.1 x.2 ^ 2
  have h1 : ∑ p : UpperIdx N, (if p.1.1 = p.1.2 then (1 : ℝ) else 2) * Y p.1.1 p.1.2 ^ 2 =
      ∑ x ∈ Finset.univ.filter (fun x : Fin N × Fin N => x.1 ≤ x.2), g x :=
    (Finset.sum_subtype _ (by simp) g).symm
  have hsw : ∑ i : Fin N, ∑ j : Fin N, (if i < j then Y i j ^ 2 else 0) =
      ∑ i : Fin N, ∑ j : Fin N, (if j < i then Y i j ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Y j i = Y i j := congrFun (congrFun hY i) j
    rw [this]
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  calc ∑ i : Fin N, ∑ j : Fin N, (if i ≤ j then g (i, j) else 0)
      = ∑ i : Fin N, ∑ j : Fin N,
          ((if i ≤ j then Y i j ^ 2 else 0) + (if i < j then Y i j ^ 2 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [g]
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h.le, h, h.ne]
          ring
        · simp
        · simp [not_le.2 h, not_lt.2 h.le]
    _ = ∑ i : Fin N, ∑ j : Fin N, (if i ≤ j then Y i j ^ 2 else 0) +
          ∑ i : Fin N, ∑ j : Fin N, (if j < i then Y i j ^ 2 else 0) := by
        rw [← hsw, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = ∑ i, ∑ j, Y i j ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : i ≤ j
        · simp [h, not_lt.2 h]
        · simp [h, not_le.1 h]

/-- `∑_{i ≤ j} Y_ij² / goeVar N (i, j) = (N/2) ∑_{i,j} Y_ij²` for symmetric `Y`. -/
private lemma goe_sum_sq_up {N : ℕ} {Y : Matrix (Fin N) (Fin N) ℝ} (hY : Yᵀ = Y) :
    ∑ p : UpperIdx N, (goeUp Y p / goeSd p) ^ 2 = (N : ℝ) / 2 * ∑ i, ∑ j, Y i j ^ 2 := by
  rw [← goe_sum_sq_weighted hY, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast p.1.1.pos
  rw [div_pow, goeSd, Real.sq_sqrt (NNReal.coe_nonneg _)]
  simp only [goeVar, goeUp]
  split_ifs <;> push_cast <;> field_simp

/-- `∑_{i,j} (O X Oᵀ)_ij² = ∑_{i,j} X_ij²` for orthogonal `O`. -/
private lemma goe_sum_sq_conj {N : ℕ} {O : Matrix (Fin N) (Fin N) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin N) ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ∑ i, ∑ j, (O * X * Oᵀ) i j ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  have key : ∀ B : Matrix (Fin N) (Fin N) ℝ, ∑ i, ∑ j, B i j ^ 2 = (B * Bᵀ).trace := by
    intro B
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have hO' : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).1 hO
  rw [key, key]
  calc (O * X * Oᵀ * (O * X * Oᵀ)ᵀ).trace = (O * (X * Xᵀ * Oᵀ)).trace := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Oᵀ O, hO', Matrix.one_mul]
    _ = (X * Xᵀ * (Oᵀ * O)).trace := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = (X * Xᵀ).trace := by rw [hO', Matrix.mul_one]

private lemma goe_scale_add {N : ℕ} (v w : EuclideanSpace ℝ (UpperIdx N)) :
    goeSym (goeScale (v + w)) = goeSym (goeScale v) + goeSym (goeScale w) := by
  ext i j
  simp [goeSym, goeScale, mul_add]

private lemma goe_scale_smul {N : ℕ} (c : ℝ) (v : EuclideanSpace ℝ (UpperIdx N)) :
    goeSym (goeScale (c • v)) = c • goeSym (goeScale v) := by
  ext i j
  simp only [goeSym, goeScale, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- `X ↦ O X Oᵀ` in the scaled coordinates of the upper entries. -/
private def goeRotLin {N : ℕ} (O : Matrix (Fin N) (Fin N) ℝ) :
    EuclideanSpace ℝ (UpperIdx N) →ₗ[ℝ] EuclideanSpace ℝ (UpperIdx N) where
  toFun v := WithLp.toLp 2 fun p => goeUp (O * goeSym (goeScale v) * Oᵀ) p / goeSd p
  map_add' v w := by
    ext p
    simp only [goe_scale_add, Matrix.mul_add, Matrix.add_mul, goeUp, PiLp.add_apply,
      Matrix.add_apply, add_div]
  map_smul' c v := by
    ext p
    simp only [goe_scale_smul, Matrix.mul_smul, Matrix.smul_mul, goeUp, PiLp.smul_apply,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]

private lemma goe_conj_symm {N : ℕ} (O : Matrix (Fin N) (Fin N) ℝ)
    {X : Matrix (Fin N) (Fin N) ℝ} (hX : Xᵀ = X) : (O * X * Oᵀ)ᵀ = O * X * Oᵀ := by
  simp [Matrix.transpose_mul, hX, Matrix.mul_assoc]

/-- `X ↦ O X Oᵀ` in the scaled coordinates, as a linear isometry for orthogonal `O`. -/
private def goeRotIso {N : ℕ} {O : Matrix (Fin N) (Fin N) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    EuclideanSpace ℝ (UpperIdx N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (UpperIdx N) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := goeRotLin O
      norm_map' := fun v => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
          EuclideanSpace.real_norm_sq_eq]
        change ∑ p : UpperIdx N, (goeUp (O * goeSym (goeScale v) * Oᵀ) p / goeSd p) ^ 2 = _
        rw [goe_sum_sq_up (goe_conj_symm O (goe_sym_transpose _)), goe_sum_sq_conj hO,
          ← goe_sum_sq_up (goe_sym_transpose _), goe_up_sym]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [goeScale]
        rw [mul_div_cancel_left₀ _ (goe_sd_pos p).ne'] } rfl

/-- The isometry intertwines `X ↦ O X Oᵀ` with the scaled coordinates. -/
private lemma goe_conj_eq {N : ℕ} {O : Matrix (Fin N) (Fin N) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin N) ℝ) (v : EuclideanSpace ℝ (UpperIdx N)) :
    O * goeSym (goeScale v) * Oᵀ = goeSym (goeScale (goeRotIso hO v)) := by
  have h : goeScale (goeRotIso hO v) = goeUp (O * goeSym (goeScale v) * Oᵀ) := by
    funext p
    change goeSd p * (goeUp (O * goeSym (goeScale v) * Oᵀ) p / goeSd p) = _
    rw [mul_div_cancel₀ _ (goe_sd_pos p).ne']
  rw [h, goe_sym_up (goe_conj_symm O (goe_sym_transpose _))]

/-- Orthogonal invariance of the GOE: `O W Oᵀ` has the law of `W` (proof: the standard Gaussian
on `(Sym_N, ⟨X, Y⟩ = (N/2) tr XY)` and `stdGaussian_map`). -/
theorem IsGOE.map_conj {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) {O : Matrix (Fin N) (Fin N) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    (ℙ : Measure Ω).map (fun ω => O * W ω * Oᵀ) = (ℙ : Measure Ω).map W := by
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hc := goe_measurable_conj O
  have hL : Measurable (goeSym ∘ goeScale (N := N)) :=
    goe_measurable_sym.comp goe_measurable_scale
  have hcomm : (fun X : Matrix (Fin N) (Fin N) ℝ => O * X * Oᵀ) ∘ (goeSym ∘ goeScale) =
      (goeSym ∘ goeScale) ∘ goeRotIso hO := by
    funext v
    exact goe_conj_eq hO v
  rw [show (fun ω => O * W ω * Oᵀ) = (fun X : Matrix (Fin N) (Fin N) ℝ => O * X * Oᵀ) ∘ W
      from rfl, ← Measure.map_map hc hWm, goe_map_eq hW, goe_upLaw_eq,
    Measure.map_map goe_measurable_sym goe_measurable_scale, Measure.map_map hc hL, hcomm,
    ← Measure.map_map hL (goeRotIso hO).continuous.measurable, stdGaussian_map]

/-- The moment function of the class: `max(C_p, 2^{p/2} E|g|^p)` (the GOE diagonal entry is
`√(2/N) g`). -/
def momMaxW (C : ℕ → ℝ) (p : ℕ) : ℝ := max (C p) ((2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p)

/-! ## Moments of centred Gaussians -/

/-- `∫ x² d N(0, v) = v`. -/
private lemma goe_integral_sq {Ω : Type*} [MeasureSpace Ω] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) ℙ) : ∫ ω, X ω ^ 2 = v := by
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  simp only [Function.comp_def] at h
  rw [h]
  have hv := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp)] at hv
  simpa using hv

/-- `|a x|^p` is integrable for `N(0, v)`. -/
private lemma goe_integrable_abs_pow {v : ℝ≥0} (a : ℝ) (p : ℕ) :
    Integrable (fun x : ℝ => |a * x| ^ p) (gaussianReal 0 v) := by
  have hint : Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · simpa [Real.norm_eq_abs] using
        (memLp_id_gaussianReal (μ := 0) (v := v) (p : ℝ≥0)).integrable_norm_pow (by omega)
  simp_rw [abs_mul, mul_pow]
  exact hint.const_mul _

/-- `∫ |a x|^p d N(0, v) = |a|^p (√v)^p E|g|^p`. -/
private lemma goe_integral_abs_pow {v : ℝ≥0} (a : ℝ) (p : ℕ) :
    ∫ x, |a * x| ^ p ∂(gaussianReal 0 v) = |a| ^ p * Real.sqrt v ^ p * gaussMoment p := by
  have h : gaussianReal 0 v = (gaussianReal 0 1).map (fun y => Real.sqrt v * y) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg _)]
  rw [h, integral_map (measurable_const_mul _).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => |a * x| ^ p).aestronglyMeasurable]
  simp_rw [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ))]
  rw [integral_const_mul, integral_const_mul, gaussMoment]
  ring

/-- The GOE belongs to the class with moments `2^{p/2} E|g|^p`. -/
theorem IsGOE.classEntries {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) :
    WigClassEntries (fun p => (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p) N W := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlaw := goe_hasLaw hW
  have hdiag : ∀ i : Fin N, (goeVar N (i, i) : ℝ) = 2 / N := fun i => by
    simp [goeVar, div_eq_mul_inv]
  have hoff : ∀ i j : Fin N, i ≠ j → (goeVar N (i, j) : ℝ) = 1 / N := fun i j hij => by
    simp [goeVar, hij]
  have hgm : ∀ p : ℕ, 0 ≤ gaussMoment p := fun p =>
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) p
  have hmom : ∀ (p : ℕ) (i j : Fin N), ∫ ω, |Real.sqrt N * W ω i j| ^ p =
      Real.sqrt (N * goeVar N (i, j)) ^ p * gaussMoment p := by
    intro p i j
    have h := (hlaw i j).integral_comp (f := fun x : ℝ => |Real.sqrt N * x| ^ p) (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h, goe_integral_abs_pow, abs_of_nonneg (Real.sqrt_nonneg _), ← mul_pow,
      ← Real.sqrt_mul hN0.le]
  refine ⟨hW.measurable, hW.symm, hW.indep, fun i j => ?_, fun i j hij => ?_, fun i => ?_,
    fun i => ?_, fun p i j => ?_, fun p i j => ?_⟩
  · rw [(hlaw i j).integral_eq, integral_id_gaussianReal]
  · rw [goe_integral_sq (hlaw i j), hoff i j hij]
  · rw [goe_integral_sq (hlaw i i), hdiag i]
    gcongr
    norm_num
  · rw [goe_integral_sq (hlaw i i), hdiag i]
  · exact (hlaw i j).integrable_comp (f := fun x : ℝ => |Real.sqrt N * x| ^ p)
      (goe_integrable_abs_pow _ p)
  · rw [hmom]
    by_cases hij : i = j
    · subst hij
      have h2 : (N : ℝ) * (goeVar N (i, i) : ℝ) = 2 := by
        rw [hdiag i]
        field_simp
      rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      apply le_of_eq
      congr 2
      ring
    · have h1 : (N : ℝ) * (goeVar N (i, j) : ℝ) = 1 := by
        rw [hoff i j hij]
        field_simp
      rw [h1, Real.sqrt_one, one_pow, one_mul]
      exact le_mul_of_one_le_left (hgm p) (Real.one_le_rpow (by norm_num) (by positivity))

/-! ## Instances -/

/-- The GOE at `N = 3` lies in the class with moments `2^{p/2} E|g|^p`. -/
example : WigClassEntries (fun p => (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p) 3 (goeW 3) :=
  (isGOE_goeW 3).classEntries (by norm_num)

end Anisotropic
