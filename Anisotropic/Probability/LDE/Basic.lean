module

public import Anisotropic.Framework.DominationMoment

@[expose] public section

/-!
# Large deviation estimates: assumptions, constants and adapters

The hypotheses of the large deviation estimates on one row or column of the matrix `X`
of Section 2.1: independent real entries `x_i` satisfying the entry conditions of
Assumption 2.1 (cond on entries of X) and (moments of X-1), the centred-moment hypotheses
on `√N x_i` and `N x_i² - 1`, the constants and bounds of the linear, off-diagonal and
diagonal estimates, and the adapters from `EntryAssumption`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-! ## Large deviation estimates -/

section LDE

variable {Ω : Type*} [MeasureSpace Ω]

/-- One row or column of `X` (Section 2.1): independent real `x_i` with (cond on entries of X)
and (moments of X-1). -/
structure RowAssumption (C : ℕ → ℝ) (N : ℕ) {ι : Type*} (x : ι → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (x i)
  indep : iIndepFun x ℙ
  mean : ∀ i, ∫ ω, x i ω = 0
  var : ∀ i, ∫ ω, x i ω ^ 2 = 1 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i, Integrable fun ω => |Real.sqrt N * x i ω| ^ p
  moment : ∀ (p : ℕ) i, ∫ ω, |Real.sqrt N * x i ω| ^ p ≤ C p

/-- Independent centred `y_i` with absolute moments `E|y_i|^p ≤ C_p` (no normalisation). -/
structure CentredMoments (C : ℕ → ℝ) {ι : Type*} (y : ι → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (y i)
  indep : iIndepFun y ℙ
  mean : ∀ i, ∫ ω, y i ω = 0
  integrable_moment : ∀ (p : ℕ) i, Integrable fun ω => |y i ω| ^ p
  moment : ∀ (p : ℕ) i, ∫ ω, |y i ω| ^ p ≤ C p

end LDE

/-- `1 + ∑_{m ≤ n} |C_m|`, an upper bound for `max(1, C_0, …, C_n)`. -/
def momHat (C : ℕ → ℝ) (n : ℕ) : ℝ := 1 + ∑ m ∈ Finset.range (n + 1), |C m|

/-- The constant of the linear `2p`-th moment bound: `(2p)^{2p} · momHat C (2p) ^ p`. -/
def ldeLinConst (C : ℕ → ℝ) (p : ℕ) : ℝ := ((2 * p : ℕ) : ℝ) ^ (2 * p) * momHat C (2 * p) ^ p

/-- The constant of the off-diagonal `2p`-th moment bound: `(4p)^{4p} · momHat C (2p) ^ {2p}`. -/
def ldeOffConst (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  ((4 * p : ℕ) : ℝ) ^ (4 * p) * momHat C (2 * p) ^ (2 * p)

/-- The moment sequence of `y² - 1`: `E|y² - 1|^m ≤ 2^m (|C_{2m}| + 1)`. -/
def diagMoments (C : ℕ → ℝ) (m : ℕ) : ℝ := 2 ^ m * (|C (2 * m)| + 1)

/-- The bound `(∑_i |a_i|²/N)^{1/2}` of the linear estimate. -/
def ldeLinBound {ι : Type*} [Fintype ι] (N : ℕ) (a : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖a i‖ ^ 2 / N)

/-- The bound `(∑_{i≠j} |A_ij|²)^{1/2}/N` of the off-diagonal estimate. -/
def ldeOffBound {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (A : ι → ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2) / N

/-- The bound `(∑_i |a_i|²)^{1/2}/N` of the diagonal estimate. -/
def ldeDiagBound {ι : Type*} [Fintype ι] (N : ℕ) (a : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖a i‖ ^ 2) / N

/-- Pointwise bound `|y² - 1|^p ≤ 2^p (|y|^{2p} + 1)`. -/
private lemma abs_sq_sub_one_pow_le (y : ℝ) (p : ℕ) :
    |y ^ 2 - 1| ^ p ≤ 2 ^ p * (|y| ^ (2 * p) + 1) := by
  have h2 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hy : |y| ^ (2 * p) = (y ^ 2) ^ p := by
    rw [pow_mul, sq_abs]
  rw [hy]
  have hp : 0 ≤ (y ^ 2) ^ p := by positivity
  rcases le_total (y ^ 2) 1 with h | h
  · have hb : |y ^ 2 - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
    have : |y ^ 2 - 1| ^ p ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
    nlinarith
  · have hb : |y ^ 2 - 1| ≤ y ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
    have : |y ^ 2 - 1| ^ p ≤ (y ^ 2) ^ p := pow_le_pow_left₀ (abs_nonneg _) hb p
    nlinarith

section LDEpins

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Adapter: column `μ` of a matrix satisfying the entry conditions. -/
theorem EntryAssumption.col {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (μ : Fin N) :
    RowAssumption C N (fun (i : Fin K) ω => X ω i μ) where
  measurable i := hX.measurable i μ
  indep := hX.indep.precomp (g := fun i : Fin K => (i, μ))
    fun i j h => by simpa using congrArg Prod.fst h
  mean i := hX.mean i μ
  var i := hX.var i μ
  integrable_moment p i := hX.integrable_moment p i μ
  moment p i := hX.moment p i μ

/-- Adapter: row `i` of a matrix satisfying the entry conditions. -/
theorem EntryAssumption.row {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (i : Fin K) :
    RowAssumption C N (fun (μ : Fin N) ω => X ω i μ) where
  measurable μ := hX.measurable i μ
  indep := hX.indep.precomp (g := fun μ : Fin N => (i, μ))
    fun a b h => by simpa using congrArg Prod.snd h
  mean μ := hX.mean i μ
  var μ := hX.var i μ
  integrable_moment p μ := hX.integrable_moment p i μ
  moment p μ := hX.moment p i μ

/-- Adapter: all entries of the matrix as one family. -/
theorem EntryAssumption.all {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) :
    RowAssumption C N (fun (p : Fin K × Fin N) ω => X ω p.1 p.2) where
  measurable p := hX.measurable p.1 p.2
  indep := hX.indep
  mean p := hX.mean p.1 p.2
  var p := hX.var p.1 p.2
  integrable_moment k p := hX.integrable_moment k p.1 p.2
  moment k p := hX.moment k p.1 p.2

/-- `y_i = √N x_i` has centred moments `C`. -/
theorem RowAssumption.centredMoments {C : ℕ → ℝ} {N : ℕ} {ι : Type*} {x : ι → Ω → ℝ}
    (hx : RowAssumption C N x) :
    CentredMoments C (fun i ω => Real.sqrt N * x i ω) where
  measurable i := measurable_const.mul (hx.measurable i)
  indep := hx.indep.comp (fun _ t => Real.sqrt N * t)
    fun _ => measurable_const.mul measurable_id
  mean i := by
    rw [integral_const_mul, hx.mean i, mul_zero]
  integrable_moment := hx.integrable_moment
  moment := hx.moment

/-- `w_i = N x_i² - 1` has centred moments `diagMoments C`. -/
theorem RowAssumption.centredMoments_sq {C : ℕ → ℝ} {N : ℕ} {ι : Type*} {x : ι → Ω → ℝ}
    (hx : RowAssumption C N x) (hN : 1 ≤ N) :
    CentredMoments (diagMoments C) (fun i ω => (N : ℝ) * x i ω ^ 2 - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : ∀ i ω, (N : ℝ) * x i ω ^ 2 - 1 = (Real.sqrt N * x i ω) ^ 2 - 1 := by
    intro i ω
    rw [mul_pow, Real.sq_sqrt hNpos.le]
  have hint : ∀ i, Integrable fun ω => (N : ℝ) * x i ω ^ 2 := by
    intro i
    have := hx.integrable_moment 2 i
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [mul_pow, sq_abs, Real.sq_sqrt hNpos.le]
  have hmeas : ∀ i, Measurable fun ω => (N : ℝ) * x i ω ^ 2 - 1 := fun i =>
    ((measurable_const.mul ((hx.measurable i).pow_const 2))).sub_const 1
  refine
    { measurable := hmeas
      indep := hx.indep.comp (fun _ t => (N : ℝ) * t ^ 2 - 1)
        fun _ => ((measurable_const.mul (measurable_id.pow_const 2))).sub_const 1
      mean := ?_
      integrable_moment := ?_
      moment := ?_ }
  · intro i
    rw [integral_sub (hint i) (integrable_const _), integral_const_mul, hx.var i]
    simp [hNpos.ne']
  · intro p i
    have hI := hx.integrable_moment (2 * p) i
    have hb : Integrable fun ω => (2 : ℝ) ^ p * (|Real.sqrt N * x i ω| ^ (2 * p) + 1) :=
      (hI.add (integrable_const _)).const_mul _
    refine hb.mono' ((hmeas i).abs.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hw i ω]
    exact abs_sq_sub_one_pow_le _ p
  · intro p i
    have hI := hx.integrable_moment (2 * p) i
    have hb : Integrable fun ω => (2 : ℝ) ^ p * (|Real.sqrt N * x i ω| ^ (2 * p) + 1) :=
      (hI.add (integrable_const _)).const_mul _
    have hint' : Integrable fun ω => |(N : ℝ) * x i ω ^ 2 - 1| ^ p :=
      hb.mono' ((hmeas i).abs.pow_const p).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hw i ω]
          exact abs_sq_sub_one_pow_le _ p)
    calc ∫ ω, |(N : ℝ) * x i ω ^ 2 - 1| ^ p
        ≤ ∫ ω, (2 : ℝ) ^ p * (|Real.sqrt N * x i ω| ^ (2 * p) + 1) :=
          integral_mono hint' hb fun ω => by
            simp only
            rw [hw i ω]
            exact abs_sq_sub_one_pow_le _ p
      _ = (2 : ℝ) ^ p * (∫ ω, |Real.sqrt N * x i ω| ^ (2 * p) + 1) := by
          rw [integral_const_mul]
      _ = (2 : ℝ) ^ p * ((∫ ω, |Real.sqrt N * x i ω| ^ (2 * p)) + 1) := by
          rw [integral_add hI (integrable_const _)]
          simp
      _ ≤ (2 : ℝ) ^ p * (C (2 * p) + 1) := by
          gcongr
          exact hx.moment (2 * p) i
      _ ≤ diagMoments C p := by
          unfold diagMoments
          gcongr
          exact le_abs_self _

end LDEpins

/-! ## Instance (Rademacher model, `N = 2`) -/

/-- The bound of the linear estimate at `a = (1,1)`, `N = 2` is `1`. -/
example : ldeLinBound 2 (fun _ : Fin 2 => (1 : ℂ)) = 1 := by
  simp [ldeLinBound]

end Anisotropic
