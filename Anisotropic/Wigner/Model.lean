import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The Wigner model, the class of entry laws, the GOE on a product space, and the instances (Rademacher entries, the matrix `A = (4N)⁻¹𝟙𝟙ᵀ`) -/

section Model

variable {Ω : Type*} [MeasureSpace Ω]

/-- The upper-triangular index set `{(i, j) : i ≤ j}`. -/
abbrev UpperIdx (N : ℕ) : Type := {p : Fin N × Fin N // p.1 ≤ p.2}

/-- The entry conditions of §12.1 for a Wigner matrix `W`: symmetric, measurable entries,
independent upper-triangular entries satisfying (cond on entries of X) and (moments of X-1). -/
structure WignerEntries (C : ℕ → ℝ) (N : ℕ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  measurable : ∀ i j, Measurable fun ω => W ω i j
  symm : ∀ ω, (W ω)ᵀ = W ω
  indep : iIndepFun (fun (p : UpperIdx N) (ω : Ω) => W ω p.1.1 p.1.2) ℙ
  mean : ∀ i j, ∫ ω, W ω i j = 0
  var : ∀ i j, ∫ ω, W ω i j ^ 2 = 1 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i j, Integrable fun ω => |Real.sqrt N * W ω i j| ^ p
  moment : ∀ (p : ℕ) i j, ∫ ω, |Real.sqrt N * W ω i j| ^ p ≤ C p

/-- The class used by the comparison: as `WignerEntries`, except that the diagonal variance
lies in `[1/N, 2/N]`. It contains `W`, the GOE and every interpolation between them. -/
structure WigClassEntries (C : ℕ → ℝ) (N : ℕ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  measurable : ∀ i j, Measurable fun ω => W ω i j
  symm : ∀ ω, (W ω)ᵀ = W ω
  indep : iIndepFun (fun (p : UpperIdx N) (ω : Ω) => W ω p.1.1 p.1.2) ℙ
  mean : ∀ i j, ∫ ω, W ω i j = 0
  var_off : ∀ i j, i ≠ j → ∫ ω, W ω i j ^ 2 = 1 / (N : ℝ)
  var_diag_ge : ∀ i, 1 / (N : ℝ) ≤ ∫ ω, W ω i i ^ 2
  var_diag_le : ∀ i, ∫ ω, W ω i i ^ 2 ≤ 2 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i j, Integrable fun ω => |Real.sqrt N * W ω i j| ^ p
  moment : ∀ (p : ℕ) i j, ∫ ω, |Real.sqrt N * W ω i j| ^ p ≤ C p

/-- The deformed Wigner model of §12.1: the entry conditions on `W`, and a deterministic real
symmetric `A` with `‖A‖ ≤ τ⁻¹`. -/
structure WignerModel (τ : ℝ) (C : ℕ → ℝ) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  entries : WignerEntries C N W
  symmA : A.IsHermitian
  normA : ‖A‖ ≤ τ⁻¹

/-- The GOE `W^Gauss` of §12.1: symmetric, independent upper-triangular entries, off-diagonal
entries `N(0, 1/N)`, diagonal entries `N(0, 2/N)`. -/
structure IsGOE {N : ℕ} (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  measurable : ∀ i j, Measurable fun ω => W ω i j
  symm : ∀ ω, (W ω)ᵀ = W ω
  indep : iIndepFun (fun (p : UpperIdx N) (ω : Ω) => W ω p.1.1 p.1.2) ℙ
  law_off : ∀ i j, i < j → (ℙ : Measure Ω).map (fun ω => W ω i j) = gaussianReal 0 (N : ℝ≥0)⁻¹
  law_diag : ∀ i, (ℙ : Measure Ω).map (fun ω => W ω i i) = gaussianReal 0 (2 * (N : ℝ≥0)⁻¹)

theorem WignerEntries.toClass {C : ℕ → ℝ} {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (h : WignerEntries C N W) : WigClassEntries C N W where
  measurable := h.measurable
  symm := h.symm
  indep := h.indep
  mean := h.mean
  var_off := fun i j _ => h.var i j
  var_diag_ge := fun i => (h.var i i).ge
  var_diag_le := fun i => by
    rw [h.var i i]
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith [show 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring]
  integrable_moment := h.integrable_moment
  moment := h.moment

end Model

/-- The variance of the GOE entry at `(i, j)`: `2/N` on the diagonal, `1/N` off it. -/
def goeVar (N : ℕ) (p : Fin N × Fin N) : ℝ≥0 :=
  if p.1 = p.2 then 2 * (N : ℝ≥0)⁻¹ else (N : ℝ≥0)⁻¹

/-- The sample space of the GOE (coordinates below the diagonal are unused). -/
def GOESpace (N : ℕ) : Type := Fin N × Fin N → ℝ

instance (N : ℕ) : MeasurableSpace (GOESpace N) := MeasurableSpace.pi

instance (N : ℕ) : MeasureSpace (GOESpace N) :=
  ⟨Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)⟩

instance (N : ℕ) : IsProbabilityMeasure (ℙ : Measure (GOESpace N)) :=
  inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)))

/-- The GOE matrix `W_{ij} = ω (min(i,j), max(i,j))` on `GOESpace N`. -/
def goeW (N : ℕ) : GOESpace N → Matrix (Fin N) (Fin N) ℝ := fun ω i j => ω (min i j, max i j)

theorem isGOE_goeW (N : ℕ) : IsGOE (goeW N) where
  measurable i j := measurable_pi_apply (X := fun _ : Fin N × Fin N => ℝ) (min i j, max i j)
  symm ω := by
    ext i j
    simp [goeW, min_comm, max_comm]
  indep := by
    have h := iIndepFun_pi (μ := fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p))
      (X := fun _ x => x) fun _ => aemeasurable_id
    have h2 : iIndepFun (fun (p : UpperIdx N) (ω : GOESpace N) => ω p.1) ℙ :=
      h.precomp (g := fun p : UpperIdx N => p.1) Subtype.val_injective
    convert h2 using 1
    funext p ω
    simp [goeW, min_eq_left p.2, max_eq_right p.2]
  law_off i j hij := by
    have e : (fun ω : GOESpace N => goeW N ω i j) = fun ω => ω (i, j) := by
      funext ω
      simp [goeW, min_eq_left hij.le, max_eq_right hij.le]
    rw [e]
    have := (measurePreserving_eval
      (fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)) (i, j)).map_eq
    rw [show (fun ω : GOESpace N => ω (i, j)) = Function.eval (i, j) from rfl]
    change (Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)).map _ = _
    rw [this]
    simp [goeVar, hij.ne]
  law_diag i := by
    have e : (fun ω : GOESpace N => goeW N ω i i) = fun ω => ω (i, i) := by
      funext ω
      simp [goeW]
    rw [e]
    have := (measurePreserving_eval
      (fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)) (i, i)).map_eq
    rw [show (fun ω : GOESpace N => ω (i, i)) = Function.eval (i, i) from rfl]
    change (Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)).map _ = _
    rw [this]
    simp [goeVar]

/-- The Rademacher Wigner matrix `W_{ij} = ±N^{-1/2}` (independent fair signs, `i ≤ j`). -/
def wigRad (N : ℕ) : SignSpace (Fin N × Fin N) → Matrix (Fin N) (Fin N) ℝ :=
  fun ω i j => signVal (ω (min i j, max i j)) / Real.sqrt N

theorem wigRad_moment_eq {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (i j : Fin N) :
    (fun ω => |Real.sqrt N * wigRad N ω i j| ^ p) = fun _ => (1 : ℝ) := by
  funext ω
  have h : Real.sqrt N ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  simp only [wigRad, mul_div_cancel₀ _ h, abs_signVal, one_pow]

theorem wignerEntries_wigRad {N : ℕ} (hN : 1 ≤ N) :
    WignerEntries (fun _ => 1) N (wigRad N) where
  measurable i j := measurable_eval_sign (min i j, max i j) fun b => signVal b / Real.sqrt N
  symm ω := by
    ext i j
    simp [wigRad, min_comm, max_comm]
  indep := by
    have h := iIndepFun_pi (μ := fun _ : Fin N × Fin N => coinMeasure)
      (X := fun _ b => signVal b / Real.sqrt N) fun _ => Measurable.of_discrete.aemeasurable
    have h2 : iIndepFun (fun (p : UpperIdx N) (ω : SignSpace (Fin N × Fin N)) =>
        signVal (ω p.1) / Real.sqrt N) ℙ :=
      h.precomp (g := fun p : UpperIdx N => p.1) Subtype.val_injective
    convert h2 using 1
    funext p ω
    simp [wigRad, min_eq_left p.2, max_eq_right p.2]
  mean i j := by
    rw [show (fun ω => wigRad N ω i j) =
        fun ω => signVal (ω (min i j, max i j)) / Real.sqrt N from rfl,
      integral_eval_sign (min i j, max i j) fun b => signVal b / Real.sqrt N]
    simp [signVal]
    ring
  var i j := by
    rw [show (fun ω => wigRad N ω i j ^ 2) =
        fun ω => (signVal (ω (min i j, max i j)) / Real.sqrt N) ^ 2 from rfl,
      integral_eval_sign (min i j, max i j) fun b => (signVal b / Real.sqrt N) ^ 2]
    simp [signVal, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  integrable_moment p i j := by
    rw [wigRad_moment_eq hN]
    exact integrable_const _
  moment p i j := by
    rw [wigRad_moment_eq hN]
    simp

/-- The Rademacher entries have vanishing third moments ((a) of Theorem 12.2). -/
theorem wigRad_third (N : ℕ) (i j : Fin N) : ∫ ω, wigRad N ω i j ^ 3 = 0 := by
  rw [show (fun ω => wigRad N ω i j ^ 3) =
      fun ω => (signVal (ω (min i j, max i j)) / Real.sqrt N) ^ 3 from rfl,
    integral_eval_sign (min i j, max i j) fun b => (signVal b / Real.sqrt N) ^ 3]
  simp [signVal, div_pow]
  ring

/-- The non-diagonal deformation `A = (4N)⁻¹ 𝟙𝟙ᵀ` (eigenvalues `1/4` and `0`). -/
def aEx (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun _ _ => 1 / (4 * N)

theorem aEx_isHermitian (N : ℕ) : (aEx N).IsHermitian := by
  ext i j
  simp [aEx]

theorem aEx_sq {N : ℕ} (hN : 1 ≤ N) : (aEx N)ᴴ * aEx N = (1 / 4 : ℝ) • aEx N := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  ext i k
  simp only [aEx, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.smul_apply,
    smul_eq_mul]
  field_simp

theorem norm_aEx_le {N : ℕ} (hN : 1 ≤ N) : ‖aEx N‖ ≤ 1 / 4 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (aEx N)
  rw [aEx_sq hN] at h
  have h2 : ‖(1 / 4 : ℝ) • aEx N‖ ≤ ‖(1 / 4 : ℝ)‖ * ‖aEx N‖ := norm_smul_le _ _
  rw [h] at h2
  have h0 := norm_nonneg (aEx N)
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h2
  nlinarith

/-- The deformed Wigner model `(wigRad N, aEx N)` with `τ = 1/2`, `C_p = 1`. -/
theorem wignerModel_rad {N : ℕ} (hN : 1 ≤ N) :
    WignerModel (1 / 2) (fun _ => 1) N (aEx N) (wigRad N) where
  entries := wignerEntries_wigRad hN
  symmA := aEx_isHermitian N
  normA := (norm_aEx_le hN).trans (by norm_num)

/-- The model instance at `N = 2` (a non-diagonal `A`, Rademacher entries). -/
example : WignerModel (1 / 2) (fun _ => 1) 2 (aEx 2) (wigRad 2) := wignerModel_rad (by norm_num)

/-- The GOE instance at `N = 3`. -/
example : IsGOE (goeW 3) := isGOE_goeW 3

/-- The Rademacher entries at `N = 2` satisfy the entry conditions. -/
example : WignerEntries (fun _ => 1) 2 (wigRad 2) := wignerEntries_wigRad (by norm_num)

/-- The Rademacher entries at `N = 2` lie in the class of entry laws. -/
example : WigClassEntries (fun _ => 1) 2 (wigRad 2) :=
  (wignerEntries_wigRad (by norm_num)).toClass

/-- Every `p`-th absolute moment of the rescaled Rademacher entries is `1`, at `N = 2`. -/
example (p : ℕ) :
    (fun ω => |Real.sqrt (2 : ℕ) * wigRad 2 ω 0 1| ^ p) = fun _ => (1 : ℝ) :=
  wigRad_moment_eq (by norm_num) p 0 1

/-- The identity `AᴴA = A / 4` at `N = 2`. -/
example : (aEx 2)ᴴ * aEx 2 = (1 / 4 : ℝ) • aEx 2 := aEx_sq (by norm_num)

/-- The norm bound for `A` at `N = 2`. -/
example : ‖aEx 2‖ ≤ 1 / 4 := norm_aEx_le (by norm_num)

end Anisotropic
