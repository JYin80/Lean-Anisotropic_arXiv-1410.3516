module

public import Anisotropic.MainDefs
public import Anisotropic.Framework.Model
public import Anisotropic.Density.GenProp

@[expose] public section

/-!
# The diagonal model and the eigenvalues of `diag(σ)`

Assumption 2.1 under (T_diag) (Section 2.1) for `Σ = diag(σ)`, stated in terms of the
diagonal entries `σ`, and its equivalence with `IsModel` for `diagonal σ`. The eigenvalue
function `specOf` of a real symmetric matrix; the eigenvalues of `diag(σ)` are `σ` up to a
permutation, and `m` of (def_m) is invariant under permutations of `σ`, so the ordering
`σ_1 ≥ ⋯ ≥ σ_M` of (def_D_Sigma) does not affect `m`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Elementary facts on permutations and root multisets -/

/-- Precomposing `σ` with a permutation does not change the number of indices `i` with
`σ_i ∈ I`. -/
private lemma ncard_comp_perm (σ : Fin M → ℝ) (e : Equiv.Perm (Fin M)) (I : Set ℝ) :
    ({i | (σ ∘ e) i ∈ I}.ncard : ℝ) = ({i | σ i ∈ I}.ncard : ℝ) := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact congrArg _ (Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl))

/-- `π(s) = M⁻¹ #{i : σ_i ∈ s}` for a measurable set `s`, with `π` of (def_pi). -/
private lemma empMeasure_apply_card (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- The root multiset of `∏_i (X - f_i)` is the multiset of values of `f`. -/
private lemma roots_prod_X_sub_C_univ {K : ℕ} (f : Fin K → ℝ) :
    (∏ i, (Polynomial.X - Polynomial.C (f i))).roots = Finset.univ.val.map f := by
  rw [Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun i => Polynomial.X - Polynomial.C (f i))
      = (Finset.univ.val.map f).map fun a => Polynomial.X - Polynomial.C a by
        rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- Two functions on `Fin K` with the same multiset of values differ by a permutation. -/
private lemma exists_perm_of_map_eq {K : ℕ} {f g : Fin K → ℝ}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : Equiv.Perm (Fin K), f = g ∘ e := by
  have hc : ∀ v, Fintype.card {i // f i = v} = Fintype.card {i // g i = v} := by
    intro v
    have hv := congrArg (Multiset.count v) h
    simp only [Multiset.count_map] at hv
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using hv
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun v => Fintype.equivOfCardEq (hc v)).trans
      (Equiv.sigmaFiberEquiv g)), ?_⟩
  funext i
  exact ((Fintype.equivOfCardEq (hc (f i))) ⟨i, rfl⟩).2.symm

/-! ## The diagonal model -/

section Model

variable {Ω : Type*} [MeasureSpace Ω]

/-- Assumption 2.1 under (T_diag) for `Σ = diag(σ)`, stated in terms of `σ`: (phi_bounded),
the entry conditions, `σ_i > 0`, (bound_Sigma) and (Sigma_gap) as a count. -/
structure DiagModel (τ : ℝ) (C : ℕ → ℝ) (M N : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) : Prop where
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  entries : EntryAssumption C X
  pos : ∀ i, 0 < σ i
  le : ∀ i, σ i ≤ τ⁻¹
  gap : ({i | σ i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M

end Model

theorem specOf_eq {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (h : A.IsHermitian) :
    specOf A = h.eigenvalues := dite_eq_left h

/-- The eigenvalues of `diag(σ)` are `σ` up to a permutation. -/
theorem exists_perm_specOf_diagonal {K : ℕ} (σ : Fin K → ℝ) :
    ∃ e : Equiv.Perm (Fin K), specOf (diagonal σ) = σ ∘ e := by
  have hH : (diagonal σ).IsHermitian := isHermitian_diagonal σ
  rw [specOf_eq hH]
  apply exists_perm_of_map_eq
  have h1 := hH.roots_charpoly_eq_eigenvalues
  rw [charpoly_diagonal, roots_prod_X_sub_C_univ] at h1
  rw [h1]
  simp

section Model

variable {Ω : Type*} [MeasureSpace Ω]

/-- `DiagModel` is Assumption 2.1 for `Σ = diag(σ)`. -/
theorem diagModel_iff {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} :
    DiagModel τ C M N σ X ↔ IsModel τ C M N (diagonal σ) X := by
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal σ
  have hev : ∀ hP : (diagonal σ).PosDef, hP.isHermitian.eigenvalues = σ ∘ e :=
    fun hP => (specOf_eq hP.isHermitian).symm.trans he
  constructor
  · intro h
    have hP : (diagonal σ).PosDef := posDef_diagonal_iff.mpr h.pos
    refine ⟨h.ratio_ge, h.ratio_le, h.entries, ⟨hP, fun i => ?_, ?_⟩⟩
    · rw [hev hP]
      exact h.le (e i)
    · rw [hev hP, ncard_comp_perm]
      exact h.gap
  · intro h
    have hP := h.sigma.posDef
    refine ⟨h.ratio_ge, h.ratio_le, h.entries, posDef_diagonal_iff.mp hP, fun j => ?_, ?_⟩
    · have hj := h.sigma.eigenvalues_le (e.symm j)
      rw [hev hP] at hj
      simpa using hj
    · have hg := h.sigma.gap
      rw [hev hP, ncard_comp_perm] at hg
      exact hg

theorem DiagModel.densityAssumptions {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hτ : 0 < τ) (h : DiagModel τ C M N σ X) :
    DensityAssumptions τ N σ := by
  have hM : (0 : ℝ) < M := by
    rcases (Nat.cast_nonneg M : (0 : ℝ) ≤ M).lt_or_eq with hM | hM
    · exact hM
    · have h0 := h.ratio_ge
      rw [← hM, zero_div] at h0
      linarith
  refine ⟨hτ, fun i => (h.pos i).le, h.ratio_ge, h.ratio_le, h.le, ?_⟩
  rw [empMeasure_apply_card σ measurableSet_Icc, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [inv_mul_le_iff₀ hM]
  refine le_trans (le_of_eq ?_) (h.gap.trans_eq (mul_comm _ _))
  rw [← Set.ncard_coe_finset]
  congr 2
  ext i
  simp

end Model

/-- `f` of (def_fx) is a symmetric function of `σ`. -/
private lemma fC_comp_perm (N : ℕ) (σ : Fin M → ℝ) (e : Equiv.Perm (Fin M)) :
    fC N (σ ∘ e) = fC N σ := by
  funext w
  simp only [fC, Function.comp]
  congr 1
  exact Equiv.sum_comp e fun i => (σ i : ℂ) / (N * (1 + σ i * w))

theorem mFun_comp_perm (N : ℕ) (σ : Fin M → ℝ) (e : Equiv.Perm (Fin M)) (z : ℂ) :
    mFun N (σ ∘ e) z = mFun N σ z := by
  unfold mFun
  rw [fC_comp_perm]

theorem mFun_specOf_diagonal (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) :
    mFun N (specOf (diagonal σ)) z = mFun N σ z := by
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal σ
  rw [he, mFun_comp_perm]

/-! ## The Rademacher instance `M = N = 2`, `σ ≡ 1`, `τ = 1/2` -/

example : specOf (diagonal fun _ : Fin 2 => (1 : ℝ))
    = (isHermitian_diagonal fun _ : Fin 2 => (1 : ℝ)).eigenvalues :=
  specOf_eq (isHermitian_diagonal _)

/-- `σ = (1, 3)`, whose eigenvalue function is `(3, 1)`: `m(2i)` agrees for both orderings. -/
example : mFun 2 (specOf (diagonal ![(1 : ℝ), 3])) (2 * Complex.I)
    = mFun 2 ![(1 : ℝ), 3] (2 * Complex.I) :=
  mFun_specOf_diagonal 2 _ _

end Anisotropic
