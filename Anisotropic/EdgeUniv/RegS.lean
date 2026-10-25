import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.EdgeTaylor
import Anisotropic.EdgeUniv.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.GeneralT.Edges
import Anisotropic.GeneralT.Masses
import Anisotropic.GeneralT.Spectra

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Transfer of a regular edge and its data along `Ŝ + κP₀` as `κ ↓ 0` -/

/-! ## The spectrum of `Ŝ + κ P₀` and its distance to `Ŝ` (§11.1) -/

/-- The eigenvalue multiset of `regS κ S = Ŝ + κ P₀` (for `S` symmetric) is the image of that of
`S` under `x ↦ x` for `x > 0` and `x ↦ κ` otherwise. -/
theorem regS_spectrum {K : ℕ} (κ : ℝ) {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.IsHermitian) :
    Finset.univ.val.map (specOf (regS κ S)) =
      Finset.univ.val.map (fun j => if 0 < specOf S j then specOf S j else κ) := by
  have hR : (regS κ S).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ S)
  have h1 := hR.roots_charpoly_eq_eigenvalues
  have h2 : (regS κ S).charpoly = ∏ i, (Polynomial.X - Polynomial.C
      (if 0 < hS.eigenvalues i then hS.eigenvalues i else κ)) :=
    hS.charpoly_cfc_eq _
  rw [h2, Polynomial.roots_prod] at h1
  · rw [specOf_eq hR, specOf_eq hS]
    simp only [Polynomial.roots_X_sub_C] at h1
    simpa [Function.comp_def, RCLike.ofReal_real_eq_id] using h1.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- `‖(Ŝ + κ P₀) − Ŝ‖ ≤ κ` in the operator norm, for `Ŝ` positive semidefinite and `κ ≥ 0`
(§11.1). -/
theorem regS_norm_sub_le {K : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) {S : Matrix (Fin K) (Fin K) ℝ}
    (hS : S.PosSemidef) : ‖regS κ S - S‖ ≤ κ := by
  have hH := hS.isHermitian
  have h1 : regS κ S = hH.cfc (fun x : ℝ => if 0 < x then x else κ) := by
    unfold regS; exact hH.cfc_eq _
  have h2 : S = hH.cfc id := by
    conv_lhs => rw [← cfc_id ℝ S hH.isSelfAdjoint]
    exact hH.cfc_eq _
  set U := hH.eigenvectorUnitary
  have h3 : regS κ S - S = (U : Matrix (Fin K) (Fin K) ℝ) *
      diagonal (fun i => (if 0 < hH.eigenvalues i then hH.eigenvalues i else κ) -
        hH.eigenvalues i) * star (U : Matrix (Fin K) (Fin K) ℝ) := by
    have e : regS κ S - S = hH.cfc (fun x : ℝ => if 0 < x then x else κ) - hH.cfc id := by
      rw [← h1, ← h2]
    rw [e]
    simp only [IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← sub_mul, ← mul_sub,
      diagonal_sub]
    rfl
  rw [h3, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.2),
    CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hκ).mpr fun i => ?_
  have hnn := hS.eigenvalues_nonneg i
  split_ifs with hp
  · simpa using hκ
  · have h0 : hH.eigenvalues i = 0 := le_antisymm (not_lt.mp hp) hnn
    rw [h0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hκ]

/-- `regS_spectrum` at `S = diag(1, 0)`, `κ = 1/2`: the spectrum of `regS κ S = diag(1, 1/2)` is
the image of `{1, 0}`. -/
example : Finset.univ.val.map (specOf (regS (1 / 2) (diagonal ![(1 : ℝ), 0]))) =
    Finset.univ.val.map (fun j => if 0 < specOf (diagonal ![(1 : ℝ), 0]) j then
      specOf (diagonal ![(1 : ℝ), 0]) j else 1 / 2) :=
  regS_spectrum (1 / 2) (isHermitian_diagonal _)

/-- `regS_norm_sub_le` at `S = diag(1, 0)`, `κ = 1/2`: here `regS κ S − S = diag(0, 1/2)`, so the
bound is attained. -/
example : ‖regS (1 / 2) (diagonal ![(1 : ℝ), 0]) - diagonal ![(1 : ℝ), 0]‖ ≤ 1 / 2 :=
  regS_norm_sub_le (by norm_num) (PosSemidef.diagonal (fun i => by fin_cases i <;> norm_num))

/-! ## Helpers: the spectrum of `Ŝ + κ P₀` and its function `f_κ` -/

private lemma rgs_TT_isHermitian {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    (Tᵀ * T).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian

private lemma rgs_specOf_TT_nonneg {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    ∀ j, 0 ≤ specOf (Tᵀ * T) j := by
  have hP : (Tᵀ * T).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  intro j
  rw [specOf_eq hP.isHermitian]
  exact hP.eigenvalues_nonneg j

private lemma rgs_regS_pos {K : ℕ} {κ : ℝ} (hκ : 0 < κ) (T : Matrix (Fin M) (Fin K) ℝ) :
    ∀ i, 0 < specOf (regS κ (Tᵀ * T)) i := by
  have hP := regS_posDef hκ T
  intro i
  rw [specOf_eq hP.isHermitian]
  exact hP.eigenvalues_pos i

private lemma rgs_card_zero {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    (Finset.univ.filter fun j => specOf (Tᵀ * T) j = 0).card = K - T.rank := by
  have hS := rgs_TT_isHermitian T
  have h1 := hS.rank_eq_card_non_zero_eigs
  rw [Matrix.rank_transpose_mul_self, Fintype.card_subtype] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K)))
    (fun j => specOf (Tᵀ * T) j = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (Finset.univ.filter fun j => hS.eigenvalues j ≠ 0).card =
      (Finset.univ.filter fun j => ¬ specOf (Tᵀ * T) j = 0).card := by
    rw [specOf_eq hS]
  omega

/-- Sums of a function vanishing at `0` over two spectra with the same nonzero values agree. -/
private lemma rgs_nzEq_sum_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    {E : Type*} [AddCommMonoid E] (g : ℝ → E) (hg : g 0 = 0) :
    ∑ i, g (σ i) = ∑ j, g (σ' j) := by
  set S : Finset ℝ := Finset.univ.image σ ∪ Finset.univ.image σ' with hS
  have key : ∀ {L : ℕ} (τ : Fin L → ℝ), Finset.univ.image τ ⊆ S →
      ∑ i, g (τ i) = ∑ s ∈ S, (Finset.univ.filter fun i => τ i = s).card • g s := by
    intro L τ hτ
    rw [Finset.sum_comp, Finset.sum_subset hτ]
    intro s _ hs
    have : (Finset.univ.filter fun i => τ i = s) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro rfl
      exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp [this]
  rw [key σ Finset.subset_union_left, key σ' Finset.subset_union_right]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = 0
  · simp [hs, hg]
  · rw [h s hs]

/-- `Σ_i g(σ_κ,i) = Σ_i g(σ_i) + (K − rank T) g(κ)` for `g(0) = 0`. -/
private lemma rgs_sum_regS {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ)
    {E : Type*} [AddCommMonoid E] (g : ℝ → E) (hg : g 0 = 0) :
    ∑ i, g (specOf (regS κ (Tᵀ * T)) i) = ∑ i, g (specOf (T * Tᵀ) i) + (K - T.rank) • g κ := by
  have hS := rgs_TT_isHermitian T
  have hnn := rgs_specOf_TT_nonneg T
  have e1 : ∑ i, g (specOf (regS κ (Tᵀ * T)) i) =
      ∑ j, g (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) := by
    have h := congrArg (fun m => (m.map g).sum) (regS_spectrum κ hS)
    simpa [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def] using h
  have e2 : ∀ j, g (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) =
      g (specOf (Tᵀ * T) j) + if specOf (Tᵀ * T) j = 0 then g κ else 0 := by
    intro j
    by_cases h : 0 < specOf (Tᵀ * T) j
    · simp [h, h.ne']
    · have h0 : specOf (Tᵀ * T) j = 0 := le_antisymm (not_lt.mp h) (hnn j)
      simp [h0, hg]
  have e3 : ∑ j, g (specOf (Tᵀ * T) j) = ∑ i, g (specOf (T * Tᵀ) i) :=
    (rgs_nzEq_sum_eq (nzEq_specOf_mul_transpose T) g hg).symm
  rw [e1]
  simp_rw [e2]
  rw [Finset.sum_add_distrib, e3, ← Finset.sum_filter, Finset.sum_const, rgs_card_zero]

/-- `f_κ = f + c κ / (N (1 + κ x))` on `ℝ`, `c = K − rank T`. -/
private lemma rgs_fR_regS {K : ℕ} (N : ℕ) (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) (x : ℝ) :
    fR N (specOf (regS κ (Tᵀ * T))) x = fR N (specOf (T * Tᵀ)) x +
      ((K - T.rank : ℕ) : ℝ) * (κ / (N * (1 + κ * x))) := by
  unfold fR
  rw [rgs_sum_regS κ T (fun s : ℝ => s / (N * (1 + s * x))) (by simp), nsmul_eq_mul]
  ring

/-- `f_κ' = f' − c κ² / (N (1 + κ x)²)` on `ℝ`. -/
private lemma rgs_fR1_regS {K : ℕ} (N : ℕ) (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) (x : ℝ) :
    fR1 N (specOf (regS κ (Tᵀ * T))) x = fR1 N (specOf (T * Tᵀ)) x -
      ((K - T.rank : ℕ) : ℝ) * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) := by
  unfold fR1
  rw [rgs_sum_regS κ T (fun s : ℝ => s ^ 2 / (N * (1 + s * x) ^ 2)) (by simp), nsmul_eq_mul]
  ring

/-- `f_κ'' = f'' + 2 c κ³ / (N (1 + κ x)³)` on `ℝ`. -/
private lemma rgs_fR2_regS {K : ℕ} (N : ℕ) (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) (x : ℝ) :
    fR2 N (specOf (regS κ (Tᵀ * T))) x = fR2 N (specOf (T * Tᵀ)) x +
      2 * (((K - T.rank : ℕ) : ℝ) * (κ ^ 3 / (N * (1 + κ * x) ^ 3))) := by
  unfold fR2
  rw [rgs_sum_regS κ T (fun s : ℝ => s ^ 3 / (N * (1 + s * x) ^ 3)) (by simp), nsmul_eq_mul]
  ring

/-- Every eigenvalue of `Ŝ + κ P₀` is an eigenvalue of `T Tᵀ` or equals `κ`. -/
private lemma rgs_regS_eig {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) (i : Fin K) :
    (∃ l, specOf (regS κ (Tᵀ * T)) i = specOf (T * Tᵀ) l) ∨
      specOf (regS κ (Tᵀ * T)) i = κ := by
  have hS := rgs_TT_isHermitian T
  have hmem : specOf (regS κ (Tᵀ * T)) i ∈ Finset.univ.val.map
      (fun j => if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) := by
    rw [← regS_spectrum κ hS]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  split_ifs at hj with hpos
  · left
    have hc := nzEq_specOf_mul_transpose T (specOf (Tᵀ * T) j) hpos.ne'
    have hne : (Finset.univ.filter fun l => specOf (T * Tᵀ) l = specOf (Tᵀ * T) j).Nonempty := by
      rw [← Finset.card_pos, hc]
      exact Finset.card_pos.mpr ⟨j, by simp⟩
    obtain ⟨l, hl⟩ := hne
    exact ⟨l, by rw [← hj]; exact ((Finset.mem_filter.mp hl).2).symm⟩
  · right
    exact hj.symm

/-- Every positive eigenvalue of `T Tᵀ` is an eigenvalue of `Ŝ + κ P₀`. -/
private lemma rgs_regS_of_pos {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) {l : Fin M}
    (hl : 0 < specOf (T * Tᵀ) l) : ∃ i, specOf (regS κ (Tᵀ * T)) i = specOf (T * Tᵀ) l := by
  have hS := rgs_TT_isHermitian T
  have hc := nzEq_specOf_mul_transpose T (specOf (T * Tᵀ) l) hl.ne'
  have hne : (Finset.univ.filter fun j => specOf (Tᵀ * T) j = specOf (T * Tᵀ) l).Nonempty := by
    rw [← Finset.card_pos, ← hc]
    exact Finset.card_pos.mpr ⟨l, by simp⟩
  obtain ⟨j, hj⟩ := hne
  have hj' : specOf (Tᵀ * T) j = specOf (T * Tᵀ) l := (Finset.mem_filter.mp hj).2
  have hmem : (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) ∈
      Finset.univ.val.map (specOf (regS κ (Tᵀ * T))) := by
    rw [regS_spectrum κ hS]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
  refine ⟨i, ?_⟩
  rw [hi, hj']
  simp [hl]

/-! ## Critical points of `f` and their indices -/

private lemma rgs_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma rgs_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma rgs_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

private lemma rgs_mem_posVals (σ : Fin M → ℝ) {i : Fin M} (hi : 0 < σ i) : σ i ∈ posVals σ := by
  simp [posVals, hi]

/-- For `σ ≥ 0` and `g 0 = 0`, `Σ_i g(σ_i) = Σ_{s} #{i | σ_i = s} g(s)` over the positive values. -/
private lemma rgs_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑ i, g (σ i) =
      ∑ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) * g s := by
  have h1 : ∑ i, g (σ i) = ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i), g (σ i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0, hg]; simp
    · simp [hpos]
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i => 0 < σ i), σ i ∈ posVals σ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [posVals, hi]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs0 : 0 < s := (Finset.mem_filter.mp hs).2
  have hset : (Finset.univ.filter (fun i => 0 < σ i)).filter (fun i => σ i = s) =
      Finset.univ.filter (fun i => σ i = s) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hs0, h⟩
  rw [hset, Finset.sum_congr rfl (g := fun _ => g s)
      (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
    Finset.sum_const, nsmul_eq_mul]

private lemma rgs_fR1_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (x : ℝ) :
    fR1 N σ x = (x ^ 2)⁻¹ - ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2 := by
  rw [fR1, rgs_sum_group σ hσ (fun a => a ^ 2 / ((N : ℝ) * (1 + a * x) ^ 2)) (by simp)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [weight, div_eq_mul_inv, mul_inv]
  ring

/-- `f'(1/y) = -y² F'(y)` off the poles. -/
private lemma rgs_fR1_inv (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy : y ≠ 0)
    (hys : ∀ s ∈ posVals σ, y + s ≠ 0) : fR1 N σ y⁻¹ = -(y ^ 2) * FChart1 N σ y := by
  rw [rgs_fR1_eq N σ hσ, FChart1, inv_pow, inv_inv]
  have : ∀ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * y⁻¹) ^ 2 =
      y ^ 2 * (weight N σ s * s ^ 2 / (y + s) ^ 2) := by
    intro s hs
    have h1 := hys s hs
    have h2 : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [h2]
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  ring

private lemma rgs_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- A finite critical point off the poles is a root of `Q`. -/
private lemma rgs_root_of_good (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ i, 1 + σ i * x ≠ 0) (hf : fR1 N σ x = 0) :
    x ∈ (critPoly N σ).roots := by
  rw [Polynomial.mem_roots (rgs_critPoly_ne_zero N σ), Polynomial.IsRoot.def,
    critPoly_eval N σ hσ hx hx', hf, mul_zero]

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma rgs_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := rgs_pos_of_mem σ hu
  have hP : ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 = 0 := by
    refine Finset.prod_eq_zero hu ?_
    field_simp
    ring
  have hsum : ∑ t ∈ posVals σ, weight N σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 =
      weight N σ u * u ^ 2 * ∏ s' ∈ (posVals σ).erase u, (1 + s' * (-u⁻¹)) ^ 2 := by
    refine Finset.sum_eq_single u (fun t ht htu => ?_) (fun h => absurd hu h)
    have hmem : u ∈ (posVals σ).erase t := Finset.mem_erase.mpr ⟨htu.symm, hu⟩
    rw [Finset.prod_eq_zero hmem (by field_simp; ring), mul_zero]
  have hev : (critPoly N σ).eval (-u⁻¹) = ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 -
      (-u⁻¹) ^ 2 * ∑ t ∈ posVals σ, weight N σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 := by
    simp only [critPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_finsetSum]
  rw [hev, hP, hsum, zero_sub, neg_ne_zero]
  refine mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr (inv_ne_zero hu0.ne')))
    (mul_ne_zero (mul_ne_zero (rgs_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

private lemma rgs_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, Polynomial.mem_roots (rgs_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := rgs_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact rgs_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (rgs_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

/-- The number of critical points in `(y, 0)` counted with multiplicity. -/
private def rgs_A (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma rgs_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
    ∀ (i : ℕ) (hi : i < L.length), (y < L[i] ↔ i < L.countP (fun x => decide (y < x)))
  | [], _, i, hi => by simp at hi
  | a :: L, hpw, i, hi => by
    rw [List.pairwise_cons] at hpw
    have hrest : ¬ y < a → L.countP (fun x => decide (y < x)) = 0 := by
      intro hya
      rw [List.countP_eq_zero]
      intro b hb
      have := hpw.1 b hb
      simp only [decide_eq_true_eq]
      intro hyb
      exact hya (lt_of_lt_of_le hyb this)
    rw [List.countP_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      by_cases hya : y < a
      · simp [hya]
      · simp [hya, hrest hya]
    | succ j =>
      simp only [List.getElem_cons_succ]
      have hj : j < L.length := by simpa using hi
      have ih := rgs_list_prefix y L hpw.2 j hj
      by_cases hya : y < a
      · simp only [hya, decide_true, ite_true]
        rw [ih]
        omega
      · simp only [hya, decide_false, Bool.false_eq_true, ite_false, add_zero]
        rw [hrest hya] at ih ⊢
        constructor
        · intro h
          exact absurd (ih.1 h) (Nat.not_lt_zero _)
        · intro h
          omega

private lemma rgs_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
    (m.sort (· ≤ ·)).reverse.getD i 0 ∈ m ∧
      ∀ y, (y < (m.sort (· ≤ ·)).reverse.getD i 0 ↔
        i < Multiset.card (m.filter (fun x => y < x))) := by
  have hlen : (m.sort (· ≤ ·)).reverse.length = Multiset.card m := by
    rw [List.length_reverse, Multiset.length_sort]
  have hi' : i < (m.sort (· ≤ ·)).reverse.length := hlen ▸ hi
  rw [List.getD_eq_getElem _ _ hi']
  have hpw : (m.sort (· ≤ ·)).reverse.Pairwise (fun a b => b ≤ a) :=
    List.pairwise_reverse.2 (Multiset.pairwise_sort _ _)
  refine ⟨?_, fun y => ?_⟩
  · have := List.getElem_mem hi'
    rwa [List.mem_reverse, Multiset.mem_sort] at this
  · rw [rgs_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

/-- `x_k ∈ 𝒞`, and `y < x_k` iff at least `k` critical points lie in `(y, 0)`. -/
private lemma rgs_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ rgs_A N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := rgs_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, rgs_A]
  omega

/-- `x` is a finite critical point of `f`, off `0` and off the poles. -/
private def rgs_Good (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : Prop :=
  x ≠ 0 ∧ (∀ i, 1 + σ i * x ≠ 0) ∧ fR1 N σ x = 0

private lemma rgs_nonpole_posVals (σ : Fin M → ℝ) {x : ℝ} (hx : ∀ i, 1 + σ i * x ≠ 0) :
    ∀ s ∈ posVals σ, 1 + s * x ≠ 0 := by
  intro s hs
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  rw [← hi]
  exact hx i

private lemma rgs_xCrit_last (N : ℕ) (σ : Fin M → ℝ) :
    xCrit N σ (2 * numBands N σ) = (yEdge N σ)⁻¹ := by
  unfold xCrit
  simp

private lemma rgs_edgeVal_last_zero (N : ℕ) (σ : Fin M → ℝ) (hy : yEdge N σ = 0) :
    edgeVal N σ (2 * numBands N σ) = 0 := by
  unfold edgeVal
  simp [hy, FChart]

/-- A point `1/y` with `y` in the chart of `I_0` is not in `I_1 ∪ ⋯ ∪ I_n`. -/
private lemma rgs_not_inInner_inv (σ : Fin M → ℝ) {y : ℝ} (hy : InChart σ y) :
    ¬ InInner σ y⁻¹ := by
  rintro ⟨hneg, s, hs, h1⟩
  have hy0 : y < 0 := inv_lt_zero.mp hneg
  have hy0' : y ≠ 0 := hy0.ne
  have h2 := hy s hs
  have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
  rw [e] at h1
  exact absurd h1 (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos h2.le hy0.le))

/-- `x_j` is a finite critical point off the poles when `x_j ≠ ∞`. -/
private lemma rgs_good_xCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 2 * numBands N σ)
    (hfin : ¬ (j = 2 * numBands N σ ∧ yEdge N σ = 0)) : rgs_Good N σ (xCrit N σ j) := by
  by_cases hlast : j = 2 * numBands N σ
  · have hy : yEdge N σ ≠ 0 := fun h => hfin ⟨hlast, h⟩
    obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
    rw [hlast, rgs_xCrit_last]
    refine ⟨inv_ne_zero hy, fun i => ?_, ?_⟩
    · rcases (hσ i).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have := hyC (σ i) (rgs_mem_posVals σ hpos)
        have e : 1 + σ i * (yEdge N σ)⁻¹ = (yEdge N σ + σ i) / yEdge N σ := by field_simp
        rw [e]
        exact div_ne_zero this.ne' hy
    · rw [rgs_fR1_inv N σ hσ hy (fun s hs => (hyC s hs).ne'), hyF, mul_zero]
  · have hlt : j < 2 * numBands N σ := lt_of_le_of_ne hj hlast
    obtain ⟨hmem, -⟩ := rgs_xCrit_spec N σ hσ hN hS hj1 hlt
    obtain ⟨hin, hnp, hf⟩ := rgs_mem_innerCrit N σ hσ hN hmem
    exact ⟨hin.1.ne, rgs_nonpole_all σ hσ hnp, hf⟩

/-- `#{c ∈ 𝒞 : y < c} ≥ #{c ∈ 𝒞 : x < c} + 1` for `y < x ∈ 𝒞`. -/
private lemma rgs_A_lt (N : ℕ) (σ : Fin M → ℝ) {x y : ℝ} (hx : x ∈ innerCrit N σ) (hy : y < x) :
    rgs_A N σ x + 1 ≤ rgs_A N σ y := by
  unfold rgs_A
  set m := innerCrit N σ
  have h1 : m.filter (fun c => x < c) =
      (m.filter (fun c => y < c)).filter (fun c => x < c) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr (fun c _ => ⟨fun h => ⟨h, hy.trans h⟩, fun h => h.1⟩)
  have h2 := Multiset.filter_add_not (fun c => x < c) (m.filter (fun c => y < c))
  have h3 : 0 < Multiset.card ((m.filter (fun c => y < c)).filter (fun c => ¬ x < c)) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨x, by simp [Multiset.mem_filter, hx, hy]⟩
  have h4 := congrArg Multiset.card h2
  rw [Multiset.card_add, ← h1] at h4
  omega

/-- Every finite critical point off the poles is some `x_j`, `x_j ≠ ∞`. -/
private lemma rgs_index_of_good (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : rgs_Good N σ x) :
    ∃ j, 1 ≤ j ∧ j ≤ 2 * numBands N σ ∧ ¬ (j = 2 * numBands N σ ∧ yEdge N σ = 0) ∧
      xCrit N σ j = x := by
  obtain ⟨hx0, hnp, hf⟩ := hx
  have hc := card_innerCrit N σ hσ hN hS
  have hnp' := rgs_nonpole_posVals σ hnp
  by_cases hin : InInner σ x
  · have hmem : x ∈ innerCrit N σ := by
      unfold innerCrit
      exact Multiset.mem_filter.mpr ⟨rgs_root_of_good N σ hσ hx0 hnp hf, hin⟩
    have hsplit : Multiset.card ((innerCrit N σ).filter (fun c => x < c)) +
        Multiset.card ((innerCrit N σ).filter (fun c => ¬ x < c)) =
          Multiset.card (innerCrit N σ) := by
      rw [← Multiset.card_add, Multiset.filter_add_not]
    have hpos : 0 < Multiset.card ((innerCrit N σ).filter (fun c => ¬ x < c)) :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨x, Multiset.mem_filter.mpr ⟨hmem, lt_irrefl x⟩⟩
    have hjlt : rgs_A N σ x + 1 < 2 * numBands N σ := by
      simp only [rgs_A]
      omega
    obtain ⟨-, hspec⟩ := rgs_xCrit_spec N σ hσ hN hS (k := rgs_A N σ x + 1) (by omega) hjlt
    refine ⟨rgs_A N σ x + 1, by omega, hjlt.le, fun h => by omega, le_antisymm ?_ ?_⟩
    · by_contra h
      have := (hspec x).1 (lt_of_not_ge h)
      omega
    · by_contra h
      have h' := lt_of_not_ge h
      have := rgs_A_lt N σ hmem h'
      exact lt_irrefl _ ((hspec _).2 this)
  · have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hchart : InChart σ x⁻¹ := by
      intro s hs
      have hs0 := rgs_pos_of_mem σ hs
      rcases lt_or_gt_of_ne hx0 with hneg | hposx
      · have h1 : 1 + s * x < 0 := by
          rcases lt_or_ge (1 + s * x) 0 with h | h
          · exact h
          · exact absurd ⟨hneg, s, hs, lt_of_le_of_ne h (Ne.symm (hnp' s hs))⟩ hin
        have e : x⁻¹ + s = (1 + s * x) / x := by field_simp
        rw [e]
        exact div_pos_of_neg_of_neg h1 hneg
      · positivity
    have hF : FChart1 N σ x⁻¹ = 0 := by
      have h := rgs_fR1_inv N σ hσ hy0 (fun s hs => (hchart s hs).ne')
      rw [inv_inv, hf] at h
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd (neg_eq_zero.mp h1) (pow_ne_zero 2 hy0)
      · exact h1
    have hyE : yEdge N σ = x⁻¹ := (existsUnique_yEdge N σ hσ hN hS).unique
      (yEdge_spec N σ hσ hN hS) ⟨hchart, hF⟩
    refine ⟨2 * numBands N σ, by omega, le_rfl, fun h => hy0 (hyE ▸ h.2), ?_⟩
    rw [rgs_xCrit_last, hyE, inv_inv]

/-- A point of `𝒞` below which no other point of `𝒞` lies, up to `x`. -/
private lemma rgs_exists_below (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) :
    ∃ y < x, rgs_A N σ y ≤ rgs_A N σ x + (innerCrit N σ).count x := by
  set m := innerCrit N σ with hm
  set F := m.toFinset.filter (fun c => c < x) with hF
  have key : ∀ y < x, (∀ c ∈ m, c < x → c ≤ y) →
      rgs_A N σ y ≤ rgs_A N σ x + m.count x := by
    intro y hyx hy
    have h1 : m.filter (fun c => y < c) = m.filter (fun c => x ≤ c) :=
      Multiset.filter_congr fun c hc => ⟨fun h => by
        by_contra h'
        exact absurd (hy c hc (lt_of_not_ge h')) (not_le.mpr h), fun h => lt_of_lt_of_le hyx h⟩
    have h2 := Multiset.filter_add_not (fun c => x < c) (m.filter (fun c => x ≤ c))
    rw [Multiset.filter_filter, Multiset.filter_filter] at h2
    have h3 : m.filter (fun c => x < c ∧ x ≤ c) = m.filter (fun c => x < c) :=
      Multiset.filter_congr fun c _ => ⟨fun h => h.1, fun h => ⟨h, h.le⟩⟩
    have h4 : m.filter (fun c => ¬ x < c ∧ x ≤ c) = m.filter (fun c => x = c) :=
      Multiset.filter_congr fun c _ => ⟨fun h => le_antisymm h.2 (not_lt.mp h.1),
        fun h => ⟨by rw [h]; exact lt_irrefl c, h.le⟩⟩
    rw [h3, h4] at h2
    simp only [rgs_A]
    rw [h1, ← h2, Multiset.card_add, Multiset.count_eq_card_filter_eq]
  by_cases hne : F.Nonempty
  · refine ⟨F.max' hne, ?_, key _ ?_ ?_⟩
    · exact (Finset.mem_filter.mp (F.max'_mem hne)).2
    · exact (Finset.mem_filter.mp (F.max'_mem hne)).2
    · intro c hc hcx
      exact F.le_max' c (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hc, hcx⟩)
  · refine ⟨x - 1, by linarith, key _ (by linarith) ?_⟩
    intro c hc hcx
    exact absurd ⟨c, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hc, hcx⟩⟩ hne

/-- Two distinct indices with the same finite critical point force `f'' = 0` there. -/
private lemma rgs_fR2_of_dup (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j j' : ℕ} (hj1 : 1 ≤ j) (hjj' : j < j')
    (hj' : j' ≤ 2 * numBands N σ) (hfin' : ¬ (j' = 2 * numBands N σ ∧ yEdge N σ = 0))
    (heq : xCrit N σ j = xCrit N σ j') : fR2 N σ (xCrit N σ j) = 0 := by
  have hjlt : j < 2 * numBands N σ := lt_of_lt_of_le hjj' hj'
  obtain ⟨hmem, hspec⟩ := rgs_xCrit_spec N σ hσ hN hS hj1 hjlt
  obtain ⟨hin, hnp, hf⟩ := rgs_mem_innerCrit N σ hσ hN hmem
  by_cases hlast : j' = 2 * numBands N σ
  · exfalso
    have hy : yEdge N σ ≠ 0 := fun h => hfin' ⟨hlast, h⟩
    rw [heq, hlast, rgs_xCrit_last] at hin
    exact rgs_not_inInner_inv σ (yEdge_spec N σ hσ hN hS).1 hin
  · have hj'lt : j' < 2 * numBands N σ := lt_of_le_of_ne hj' hlast
    obtain ⟨-, hspec'⟩ := rgs_xCrit_spec N σ hσ hN hS (by omega) hj'lt
    set x := xCrit N σ j with hx
    rw [← heq] at hspec'
    have hA : rgs_A N σ x < j := by
      by_contra h
      exact lt_irrefl x ((hspec x).2 (not_lt.mp h))
    obtain ⟨y, hyx, hy⟩ := rgs_exists_below N σ x
    have h1 := (hspec' y).1 hyx
    have hcnt := count_innerCrit N σ hσ hN hin hnp
    by_contra h2
    simp only [hf, h2, ↓reduceIte] at hcnt
    omega

/-- Lemma 2.5, `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma rgs_edgeVal_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
    exact (edgeVal_succ_le N σ hσ hN hS (k := i + d) (by omega) (by omega)).trans
      (ih (by omega) (by omega))

/-- With no positive value, there is no band. -/
private lemma rgs_posVals_nonempty (N : ℕ) (σ : Fin M → ℝ) (h : 1 ≤ numBands N σ) :
    (posVals σ).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hQ : critPoly N σ = 1 := by simp [critPoly, hne]
  have : numBands N σ = 0 := by simp [numBands, innerCrit, hQ]
  omega

/-! ## Assumption 2.1 at smaller parameters, and the counting function `n` -/

private lemma rgs_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
  refine ⟨hN, Nat.pos_of_ne_zero hM, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
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

private lemma rgs_empMeasure_toReal (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (empMeasure σ s).toReal = ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ) / M := by
  have h : empMeasure σ s =
      (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ hs, smul_eq_mul]
    congr 1
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Set.indicator]
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_inv_mul]

/-- Assumption 2.1 is monotone in its parameter. -/
private lemma rgs_da_mono {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') (hle : τ' ≤ τ) : DensityAssumptions τ' N σ := by
  refine ⟨hτ', h.nonneg, hle.trans h.phi_lower, h.phi_upper.trans (inv_anti₀ hτ' hle),
    fun i => (h.bound_Sigma i).trans (inv_anti₀ hτ' hle), ?_⟩
  have hg := h.Sigma_gap
  rw [rgs_empMeasure_toReal σ measurableSet_Icc] at hg ⊢
  refine le_trans ?_ (hg.trans (by linarith))
  gcongr

/-- Any `σ ≥ 0` with a positive entry satisfies Assumption 2.1 at some `τ > 0`. -/
private lemma rgs_da_exists {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {i₀ : Fin M} (hi₀ : 0 < σ i₀) : ∃ τ, DensityAssumptions τ N σ := by
  have hM : 0 < M := i₀.pos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S := ∑ i, σ i with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hσ i
  set τ : ℝ := min (min ((M : ℝ) / N) ((N : ℝ) / M))
    (min (1 / (S + 1)) (min (σ i₀ / 2) (1 / (M : ℝ)))) with hτdef
  have hτ : 0 < τ := by
    refine lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hτ1 : τ ≤ (M : ℝ) / N := (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ (N : ℝ) / M := (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ 1 / (S + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hτ4 : τ ≤ σ i₀ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ5 : τ ≤ 1 / (M : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨τ, hτ, hσ, hτ1, ?_, ?_, ?_⟩
  · unfold phiRatio
    calc (M : ℝ) / N = ((N : ℝ) / M)⁻¹ := by rw [inv_div]
      _ ≤ τ⁻¹ := inv_anti₀ hτ hτ2
  · intro i
    have h1 : σ i ≤ S := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    have h3 : S + 1 ≤ τ⁻¹ := by
      have := inv_anti₀ hτ hτ3
      rwa [one_div, inv_inv] at this
    linarith
  · rw [rgs_empMeasure_toReal σ measurableSet_Icc]
    have hMτ : (M : ℝ) * τ ≤ 1 := by
      rw [le_div_iff₀ hMr] at hτ5
      linarith
    rw [div_le_iff₀ hMr]
    refine le_trans ?_ (show (M : ℝ) - 1 ≤ (1 - τ) * M by nlinarith)
    rw [le_sub_iff_add_le]
    norm_cast
    refine Nat.succ_le_of_lt (lt_of_lt_of_eq (Finset.card_lt_card (Finset.filter_ssubset.mpr
      ⟨i₀, Finset.mem_univ _, fun h => ?_⟩)) (by simp))
    have := h.2
    linarith

private lemma rgs_nClass_anti {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    Antitone (nClass N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ici_subset_Ici.mpr hxy))) (Nat.cast_nonneg N)

/-- `ϱ((−∞, 0)) = 0`. -/
private lemma rgs_varrho_Iio (N : ℕ) (σ : Fin M → ℝ) : varrho N σ (Set.Iio 0) = 0 := by
  have h0 : (0 : ℝ) ∉ Set.Iio 0 := fun h => lt_irrefl (0 : ℝ) h
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have he : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro h
    exact h.le
  rw [he, Measure.restrict_empty, lintegral_zero_measure]

/-- `N ϱ((0, ∞)) = d_p` (Lemma A.1). -/
private lemma rgs_mass_pos {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    (N : ℝ) * (varrho N σ (Set.Ioi 0)).toReal = cumCount N σ (numBands N σ) := by
  obtain ⟨hN, -, hS⟩ := rgs_facts h
  have hσ := h.nonneg
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hp := (card_innerCrit N σ hσ hN hS).2
  have hc := (cumCount_spec h hp le_rfl).1
  rw [sum_bandCount N σ hσ hN hS] at hc
  have h0 := varrho_singleton_zero N σ hσ hN
  have hcompl : varrho N σ (Set.Ioi 0) = 1 - varrho N σ {0} := by
    have hu : ({0}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio,
        Set.mem_Ioi]
      exact ⟨fun h => lt_or_gt_of_ne h,
        fun h => by rcases h with h | h <;> [exact h.ne; exact h.ne']⟩
    have h1 : varrho N σ ({0}ᶜ : Set ℝ) = varrho N σ (Set.Ioi 0) := by
      rw [hu, measure_union (Set.disjoint_left.mpr fun x hx hx' =>
        lt_asymm (Set.mem_Iio.mp hx) (Set.mem_Ioi.mp hx')) measurableSet_Ioi,
        rgs_varrho_Iio N σ, zero_add]
    rw [← h1, prob_compl_eq_one_sub (measurableSet_singleton 0)]
  rw [hcompl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    mul_sub, mul_one, h0, hc]
  rcases le_total (N : ℝ) (Finset.univ.filter fun i => 0 < σ i).card with hle | hle
  · rw [max_eq_right (by linarith), min_eq_left hle]
    ring
  · rw [max_eq_left (by linarith), min_eq_right hle]
    ring

/-- `n(E) ≤ d_k` when `E > 0` lies in the gap below band `k` or below `a_{2k}`. -/
private lemma rgs_nClass_le {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk1 : 1 ≤ k) (hkp : k ≤ numBands N σ) {E : ℝ} (hE : 0 < E)
    (hcase : k = numBands N σ ∨ (k < numBands N σ ∧ edgeVal N σ (2 * k + 1) ≤ E) ∨
      (0 < edgeVal N σ (2 * k) ∧ edgeVal N σ (2 * k) ≤ E)) :
    nClass N σ E ≤ cumCount N σ k := by
  obtain ⟨hN, -, hS⟩ := rgs_facts h
  have hσ := h.nonneg
  have hanti := rgs_nClass_anti (N := N) hσ hN
  rcases hcase with hk | ⟨hk, hle⟩ | ⟨hpos, hle⟩
  · have := isProbabilityMeasure_varrho N σ hσ hN
    rw [hk, ← rgs_mass_pos h]
    unfold nClass
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun x hx => ?_)) (Nat.cast_nonneg N)
    exact lt_of_lt_of_le hE (Set.mem_Ici.mp hx)
  · have h1 := (nClass_edgeVal h (k := k + 1) (by omega) (by omega)).1
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega] at h1
    rw [← h1]
    exact hanti hle
  · have h2 := (nClass_edgeVal h hk1 hkp).2 hpos
    rw [← h2]
    exact hanti hle

/-! ## `f'` near `0`, near the poles and away from the critical points -/

private lemma rgs_contAt_fR (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) : ContinuousAt (fR N σ) x :=
  (hasDerivAt_fR N σ hx hx').continuousAt

private lemma rgs_contAt_fR1 (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) : ContinuousAt (fR1 N σ) x :=
  (hasDerivAt_fR1 N σ hx hx').continuousAt

private lemma rgs_contAt_fR2 (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) : ContinuousAt (fR2 N σ) x := by
  have h1 : ContinuousAt (fun y : ℝ => -2 * (y ^ 3)⁻¹) x :=
    continuousAt_const.mul ((continuousAt_id.pow 3).inv₀ (pow_ne_zero 3 hx))
  have h2 : ContinuousAt (fun y : ℝ => ∑ i, σ i ^ 3 / ((N : ℝ) * (1 + σ i * y) ^ 3)) x := by
    refine tendsto_finsetSum _ fun i _ => ?_
    by_cases hN : (N : ℝ) = 0
    · simp only [hN, zero_mul, div_zero]
      exact continuousAt_const
    · exact continuousAt_const.div (continuousAt_const.mul
        ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).pow 3))
        (mul_ne_zero hN (pow_ne_zero 3 (hx' i)))
  have h3 : ContinuousAt (fun y : ℝ => -2 * (y ^ 3)⁻¹ +
      2 * ∑ i, σ i ^ 3 / ((N : ℝ) * (1 + σ i * y) ^ 3)) x :=
    h1.add ((continuousAt_const (y := (2 : ℝ))).mul h2)
  exact h3

/-- `f' ≥ 1` near `0`. -/
private lemma rgs_near_zero (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    ∃ δ₀ > 0, ∀ x, x ≠ 0 → |x| ≤ δ₀ → 1 ≤ fR1 N σ x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S : ℝ := ∑ i, σ i + 1 with hSdef
  have hS1 : 1 ≤ S := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hσ i
    linarith
  have hσS : ∀ i, σ i ≤ S := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hσ j) (Finset.mem_univ i)
    linarith
  set B : ℝ := 4 * M * S ^ 2 / N with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨min (1 / (2 * S)) (1 / (1 + B)), lt_min (by positivity) (by positivity), ?_⟩
  intro x hx hxd
  have hx1 : |x| ≤ 1 / (2 * S) := hxd.trans (min_le_left _ _)
  have hx2 : |x| ≤ 1 / (1 + B) := hxd.trans (min_le_right _ _)
  have hxle1 : |x| ≤ 1 := hx1.trans (by
    rw [div_le_one (by positivity)]
    linarith)
  have hterm : ∀ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2) ≤ 4 * S ^ 2 / N := by
    intro i
    have hsx : |σ i * x| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (hσ i)]
      calc σ i * |x| ≤ S * (1 / (2 * S)) :=
            mul_le_mul (hσS i) hx1 (abs_nonneg _) (by linarith)
        _ = 1 / 2 := by field_simp
    have h1 : 1 / 2 ≤ 1 + σ i * x := by
      have := neg_abs_le (σ i * x)
      linarith
    have h2 : 1 / 4 ≤ (1 + σ i * x) ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hNr]
    have h3 : σ i ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (hσ i) (hσS i) 2
    have h4 : σ i ^ 2 ≤ 4 * S ^ 2 * (1 + σ i * x) ^ 2 := by nlinarith
    calc σ i ^ 2 * N ≤ (4 * S ^ 2 * (1 + σ i * x) ^ 2) * N :=
          mul_le_mul_of_nonneg_right h4 hNr.le
      _ = 4 * S ^ 2 * (N * (1 + σ i * x) ^ 2) := by ring
  have hsum : ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2) ≤ B := by
    calc ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2) ≤ ∑ _i : Fin M, 4 * S ^ 2 / N :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hB]; ring
  have hxsq : x ^ 2 ≤ 1 / (1 + B) := by
    have hax : 0 < |x| := abs_pos.mpr hx
    calc x ^ 2 = |x| * |x| := by rw [sq, abs_mul_abs_self]
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hxle1 hax.le
      _ ≤ 1 / (1 + B) := by linarith
  have hinv : 1 + B ≤ (x ^ 2)⁻¹ := by
    have hx2pos : 0 < x ^ 2 := by positivity
    rw [le_inv_comm₀ (by positivity) hx2pos]
    simpa [one_div] using hxsq
  unfold fR1
  linarith

/-- `f' < 0` near the pole `-1/s`. -/
private lemma rgs_near_pole (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : 1 + s * x ≠ 0)
    (hxd : |x + s⁻¹| ≤ 1 / (2 * s * (N + 1))) : fR1 N σ x < 0 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 := rgs_pos_of_mem σ hs
  obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  set δ := 1 / (2 * s * (N + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδs : δ ≤ 1 / (2 * s) := by
    rw [hδ]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsum : σ i₀ ^ 2 / ((N : ℝ) * (1 + σ i₀ * x) ^ 2) ≤
      ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2) :=
    Finset.single_le_sum (f := fun i => σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2))
      (fun i _ => by positivity) (Finset.mem_univ i₀)
  rw [hi₀] at hsum
  have e : 1 + s * x = s * (x + s⁻¹) := by field_simp; ring
  have hsq : (1 + s * x) ^ 2 ≤ s ^ 2 * δ ^ 2 := by
    rw [e, mul_pow]
    have : (x + s⁻¹) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxd 2
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hpos : 0 < (1 + s * x) ^ 2 := by positivity
  have hterm : 4 * s ^ 2 * ((N + 1) ^ 2 / N) ≤ s ^ 2 / ((N : ℝ) * (1 + s * x) ^ 2) := by
    have hden : (N : ℝ) * (1 + s * x) ^ 2 ≤ N * (s ^ 2 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hNr.le
    have h1 : s ^ 2 / ((N : ℝ) * (s ^ 2 * δ ^ 2)) ≤ s ^ 2 / ((N : ℝ) * (1 + s * x) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have e2 : s ^ 2 / ((N : ℝ) * (s ^ 2 * δ ^ 2)) = 4 * s ^ 2 * ((N + 1) ^ 2 / N) := by
      rw [hδ]; field_simp; norm_num
    linarith
  have hxabs : 1 / (2 * s) ≤ |x| := by
    have h1 : |s⁻¹| ≤ |x| + |x + s⁻¹| := by
      have := abs_sub (x + s⁻¹) x
      simp only [add_sub_cancel_left] at this
      linarith [abs_add_le (x + s⁻¹) (-x), abs_neg x]
    rw [abs_of_pos (inv_pos.mpr hs0)] at h1
    have : s⁻¹ - δ ≥ 1 / (2 * s) := by
      have : s⁻¹ = 2 * (1 / (2 * s)) := by field_simp
      linarith
    linarith
  have hx0 : 0 < |x| := lt_of_lt_of_le (by positivity) hxabs
  have hinv : (x ^ 2)⁻¹ ≤ 4 * s ^ 2 := by
    have h1 : (1 / (2 * s)) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (by positivity) hxabs 2
    have h2 : (x ^ 2)⁻¹ ≤ ((1 / (2 * s)) ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    calc (x ^ 2)⁻¹ ≤ ((1 / (2 * s)) ^ 2)⁻¹ := h2
      _ = 4 * s ^ 2 := by field_simp; ring
  have hgt : 4 * s ^ 2 < 4 * s ^ 2 * ((N + 1) ^ 2 / N) := by
    have : (1 : ℝ) < (N + 1) ^ 2 / N := by
      rw [one_lt_div hNr]
      nlinarith
    have h4 : 0 < 4 * s ^ 2 := by positivity
    nlinarith
  unfold fR1
  linarith

/-- Away from the critical points, `|f'|` is bounded below on bounded sets free of `0` and of
the poles; so `0 ≤ f'(x) ≤ ε` forces `x` near a critical point. -/
private lemma rgs_compact (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {η R : ℝ}
    (hη : 0 < η) :
    ∃ ε > 0, ∀ x, |x| ≤ R → x ≠ 0 → (∀ i, 1 + σ i * x ≠ 0) → 0 ≤ fR1 N σ x →
      fR1 N σ x ≤ ε → ∃ z, rgs_Good N σ z ∧ |x - z| < η := by
  obtain ⟨δ₀, hδ₀, h0⟩ := rgs_near_zero σ hσ hN
  set Z : Finset ℝ := (critPoly N σ).roots.toFinset.filter (rgs_Good N σ) with hZ
  set d : ℝ → ℝ := fun s => 1 / (2 * s * (N + 1)) with hd
  set B : Set ℝ := {x | |x| ≤ R} ∩ {x | δ₀ ≤ |x|} ∩
    (⋂ s ∈ posVals σ, {x | d s ≤ |x + s⁻¹|}) ∩ (⋂ z ∈ Z, {x | η ≤ |x - z|}) with hB
  have hBc : IsCompact B := by
    refine (isCompact_Icc (a := -R) (b := R)).of_isClosed_subset ?_ ?_
    · refine ((isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le continuous_const (by fun_prop))).inter ?_ |>.inter ?_
      · exact isClosed_biInter fun s _ => isClosed_le continuous_const (by fun_prop)
      · exact isClosed_biInter fun z _ => isClosed_le continuous_const (by fun_prop)
    · intro x hx
      exact abs_le.mp hx.1.1.1
  have hBgood : ∀ x ∈ B, x ≠ 0 ∧ ∀ i, 1 + σ i * x ≠ 0 := by
    intro x hx
    obtain ⟨⟨⟨-, hx0⟩, hxp⟩, -⟩ := hx
    have hx0' : δ₀ ≤ |x| := hx0
    refine ⟨fun h => by rw [h, abs_zero] at hx0'; linarith, fun i => ?_⟩
    rcases (hσ i).eq_or_lt with hi | hi
    · rw [← hi]; simp
    · have hs := rgs_mem_posVals σ hi
      have h1 : d (σ i) ≤ |x + (σ i)⁻¹| := by
        simp only [Set.mem_iInter] at hxp
        exact hxp (σ i) hs
      have hd0 : 0 < d (σ i) := by simp only [hd]; positivity
      intro h
      have e : x + (σ i)⁻¹ = (1 + σ i * x) / σ i := by field_simp; ring
      rw [e, h, zero_div, abs_zero] at h1
      linarith
  have hBne0 : ∀ x ∈ B, fR1 N σ x ≠ 0 := by
    intro x hx hf
    obtain ⟨hx0, hnp⟩ := hBgood x hx
    have hz : x ∈ Z := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr (rgs_root_of_good N σ hσ hx0 hnp hf), ⟨hx0, hnp, hf⟩⟩
    have := hx.2
    simp only [Set.mem_iInter] at this
    have := this x hz
    simp only [Set.mem_ofPred_eq, sub_self, abs_zero] at this
    linarith
  obtain ⟨ε₁, hε₁, hε₁B⟩ : ∃ ε₁ > 0, ∀ x ∈ B, ε₁ ≤ |fR1 N σ x| := by
    rcases B.eq_empty_or_nonempty with hBe | hBn
    · exact ⟨1, one_pos, fun x hx => by rw [hBe] at hx; exact absurd hx (Set.notMem_empty x)⟩
    · have hcont : ContinuousOn (fun x => |fR1 N σ x|) B := fun x hx =>
        (rgs_contAt_fR1 N σ (hBgood x hx).1 (hBgood x hx).2).abs.continuousWithinAt
      obtain ⟨xm, hxm, hmin⟩ := hBc.exists_isMinOn hBn hcont
      exact ⟨|fR1 N σ xm|, abs_pos.mpr (hBne0 xm hxm), fun x hx => hmin hx⟩
  refine ⟨min (1 / 2) (ε₁ / 2), lt_min (by norm_num) (by positivity), ?_⟩
  intro x hxR hx0 hnp hf0 hfε
  by_contra hno
  push Not at hno
  have hxB : x ∈ B := by
    refine ⟨⟨⟨hxR, ?_⟩, ?_⟩, ?_⟩
    · by_contra hlt
      have := h0 x hx0 (not_le.mp hlt).le
      have := hfε.trans (min_le_left _ _)
      linarith
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro s hs
      by_contra hlt
      have hneg := rgs_near_pole σ hN hs (rgs_nonpole_posVals σ hnp s hs)
        (not_le.mp hlt).le
      linarith
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro z hz
      exact hno z (Finset.mem_filter.mp hz).2
  have h1 := hε₁B x hxB
  rw [abs_of_nonneg hf0] at h1
  have := hfε.trans (min_le_right _ _)
  linarith

/-! ## Critical points of `f + c κ / (N (1 + κ x))` as `κ ↓ 0` -/

/-- Far out, every critical value of `f_κ` is small, uniformly in `κ`. -/
private lemma rgs_far (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {K : ℕ} (σ' : ℝ → Fin K → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ κ x, fR N (σ' κ) x = fR N σ x + c * (κ / (N * (1 + κ * x))))
    (h1 : ∀ κ x, fR1 N (σ' κ) x = fR1 N σ x - c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)))
    {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ κ x, R ≤ |x| → fR1 N (σ' κ) x = 0 → |fR N (σ' κ) x| < η := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set smin := (posVals σ).min' hS with hsmin
  have hsmin0 : 0 < smin := rgs_pos_of_mem σ ((posVals σ).min'_mem hS)
  have hge : ∀ i, 0 < σ i → smin ≤ σ i := fun i hi =>
    (posVals σ).min'_le _ (rgs_mem_posVals σ hi)
  set A : ℝ := 1 + 2 * M / N with hA
  set B : ℝ := c / N with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set R : ℝ := max (2 / smin) (max (3 * A / η) (3 * (B + 1) / η)) with hR
  have hR1 : 2 / smin ≤ R := le_max_left _ _
  have hR2 : 3 * A / η ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR3 : 3 * (B + 1) / η ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR1
  refine ⟨R, hRpos, fun κ x hRx hcrit => ?_⟩
  have hx0 : 0 < |x| := lt_of_lt_of_le hRpos hRx
  -- the terms of `f`
  have hterm : ∀ i, |σ i / ((N : ℝ) * (1 + σ i * x))| ≤ 2 / (N * |x|) := by
    intro i
    rcases (hσ i).eq_or_lt with h0i | hpi
    · rw [← h0i]; simp only [zero_div, abs_zero]; positivity
    · have h2 : 2 ≤ σ i * |x| := by
        calc (2 : ℝ) = smin * (2 / smin) := by field_simp
          _ ≤ σ i * |x| := mul_le_mul (hge i hpi) (hR1.trans hRx) (by positivity) hpi.le
      have h3 : σ i * |x| / 2 ≤ |1 + σ i * x| := by
        have : |σ i * x| ≤ |1 + σ i * x| + 1 := by
          have := abs_sub (1 + σ i * x) 1
          simp only [add_sub_cancel_left, abs_one] at this
          linarith
        rw [abs_mul, abs_of_pos hpi] at this
        linarith
      have h4 : 0 < |1 + σ i * x| := lt_of_lt_of_le (by positivity) h3
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hNr, div_le_div_iff₀ (by positivity)
        (by positivity)]
      have : σ i * (N * |x|) ≤ 2 * (N * |1 + σ i * x|) := by nlinarith
      exact this
  have hsum : |∑ i, σ i / ((N : ℝ) * (1 + σ i * x))| ≤ 2 * M / (N * |x|) := by
    calc |∑ i, σ i / ((N : ℝ) * (1 + σ i * x))| ≤ ∑ i, |σ i / ((N : ℝ) * (1 + σ i * x))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin M, 2 / (N * |x|) := Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * M / (N * |x|) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- the new term
  set t : ℝ := c * (κ / (N * (1 + κ * x))) with ht
  have hu : c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ≤ (x ^ 2)⁻¹ := by
    have e := h1 κ x
    rw [hcrit] at e
    have hnn : 0 ≤ ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    unfold fR1 at e
    linarith
  have ht2 : t ^ 2 = B * (c * (κ ^ 2 / (N * (1 + κ * x) ^ 2))) := by
    rw [ht, hB]
    by_cases hz : 1 + κ * x = 0
    · simp [hz]
    · field_simp
  have hx2 : R ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hRpos.le hRx 2
  have ht3 : t ^ 2 < (η / 3) ^ 2 := by
    have h1' : t ^ 2 ≤ B * (x ^ 2)⁻¹ := by
      rw [ht2]; exact mul_le_mul_of_nonneg_left hu hB0
    have h2' : B * (x ^ 2)⁻¹ ≤ B * (R ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hx2) hB0
    have h3' : B * (R ^ 2)⁻¹ < (η / 3) ^ 2 := by
      have hηR : 3 * (B + 1) ≤ η * R := by
        rw [div_le_iff₀ hη] at hR3; linarith
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have htabs : |t| < η / 3 := by
    obtain ⟨h1', h2'⟩ := abs_lt_of_sq_lt_sq' ht3 (by positivity)
    exact abs_lt.mpr ⟨h1', h2'⟩
  have hfeq : fR N (σ' κ) x = -x⁻¹ + ∑ i, σ i / ((N : ℝ) * (1 + σ i * x)) + t := by
    rw [h0, fR]
  have hAx : A / |x| ≤ η / 3 := by
    rw [div_le_iff₀ hx0]
    rw [div_le_iff₀ hη] at hR2
    nlinarith
  have hbound : |fR N (σ' κ) x| ≤ A / |x| + |t| := by
    rw [hfeq]
    calc |-x⁻¹ + ∑ i, σ i / ((N : ℝ) * (1 + σ i * x)) + t|
        ≤ |-x⁻¹| + |∑ i, σ i / ((N : ℝ) * (1 + σ i * x))| + |t| := by
          have := abs_add_le (-x⁻¹ + ∑ i, σ i / ((N : ℝ) * (1 + σ i * x))) t
          have := abs_add_le (-x⁻¹) (∑ i, σ i / ((N : ℝ) * (1 + σ i * x)))
          linarith
      _ ≤ 1 / |x| + 2 * M / (N * |x|) + |t| := by
          rw [abs_neg, abs_inv, one_div]; linarith
      _ = A / |x| + |t| := by rw [hA]; field_simp
  linarith

/-- For small `κ`, every finite critical point of `f_κ` is either near a critical point of `f`,
with nearby value, or has a small critical value. -/
private lemma rgs_global (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {K : ℕ} (σ' : ℝ → Fin K → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ κ x, fR N (σ' κ) x = fR N σ x + c * (κ / (N * (1 + κ * x))))
    (h1 : ∀ κ x, fR1 N (σ' κ) x = fR1 N σ x - c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)))
    (hpos : ∀ κ l, 0 < σ l → ∃ i, σ' κ i = σ l) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ x, rgs_Good N (σ' κ) x →
      (∃ z, rgs_Good N σ z ∧ |x - z| < η ∧ |fR N (σ' κ) x - fR N σ z| < η) ∨
        |fR N (σ' κ) x| < η := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨R, hR, hfar⟩ := rgs_far σ hσ hN hS σ' hc h0 h1 hη
  set Z : Finset ℝ := (critPoly N σ).roots.toFinset.filter (rgs_Good N σ) with hZ
  have hcont : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ Z, ∀ x, |x - z| < r →
      |fR N σ x - fR N σ z| < η / 2 := by
    rw [Filter.eventually_all_finset]
    intro z hz
    obtain ⟨hz0, hznp, -⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (rgs_contAt_fR N σ hz0 hznp) (η / 2)
      (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr x hx
    exact hδ' (by rw [Real.dist_eq]; exact hx.trans hr.2)
  obtain ⟨r, hrc, hr0, hrη⟩ := (hcont.and (Ioo_mem_nhdsGT hη)).exists
  obtain ⟨ε, hε, hcpt⟩ := rgs_compact σ hσ hN (R := R) hr0
  set κ₀ : ℝ := min (1 / (2 * R)) (min 1 (min (ε * N / (4 * c + 1)) (η * N / (4 * c + 4))))
    with hκ₀
  have hκ₀0 : 0 < κ₀ := by
    refine lt_min (by positivity) (lt_min one_pos (lt_min (by positivity) (by positivity)))
  filter_upwards [Ioo_mem_nhdsGT hκ₀0] with κ hκ x hx
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hκR : κ < 1 / (2 * R) := lt_of_lt_of_le hκ1 (min_le_left _ _)
  have hκ1' : κ < 1 := lt_of_lt_of_le hκ1 ((min_le_right _ _).trans (min_le_left _ _))
  have hκε : κ < ε * N / (4 * c + 1) :=
    lt_of_lt_of_le hκ1 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hκη : κ < η * N / (4 * c + 4) :=
    lt_of_lt_of_le hκ1 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hx0, hxnp, hxf⟩ := hx
  by_cases hxR : R ≤ |x|
  · exact Or.inr (hfar κ x hxR hxf)
  · left
    have hxR' : |x| < R := lt_of_not_ge hxR
    have hκx : 1 / 2 ≤ 1 + κ * x := by
      have h1' : |κ * x| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hκ0]
        calc κ * |x| ≤ (1 / (2 * R)) * R :=
              mul_le_mul hκR.le hxR'.le (abs_nonneg _) (by positivity)
          _ = 1 / 2 := by field_simp
      have := neg_abs_le (κ * x)
      linarith
    have hnp : ∀ l, 1 + σ l * x ≠ 0 := by
      intro l
      rcases (hσ l).eq_or_lt with h0l | hpl
      · rw [← h0l]; simp
      · obtain ⟨i, hi⟩ := hpos κ l hpl
        rw [← hi]
        exact hxnp i
    have hf' : fR1 N σ x = c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) := by
      have := h1 κ x
      rw [hxf] at this
      linarith
    have hsq : 1 / 4 ≤ (1 + κ * x) ^ 2 := by nlinarith
    have hgle : c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ≤ 4 * c * κ ^ 2 / N := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hNr]
      have : c * κ ^ 2 * 1 ≤ c * κ ^ 2 * (4 * (1 + κ * x) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hgε : 4 * c * κ ^ 2 / N ≤ ε := by
      rw [div_le_iff₀ hNr]
      have hk2 : κ ^ 2 ≤ κ := by nlinarith
      have h1' : κ * (4 * c + 1) < ε * N := by
        rwa [lt_div_iff₀ (by positivity)] at hκε
      nlinarith
    have hg0 : 0 ≤ c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) := by positivity
    obtain ⟨z, hz, hxz⟩ := hcpt x hxR'.le hx0 hnp (hf' ▸ hg0) (hf' ▸ hgle.trans hgε)
    have hzZ : z ∈ Z := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr (rgs_root_of_good N σ hσ hz.1 hz.2.1 hz.2.2), hz⟩
    have hfz := hrc z hzZ x hxz
    have hnew : |c * (κ / (N * (1 + κ * x)))| < η / 2 := by
      have hpos' : 0 < 1 + κ * x := by linarith
      rw [abs_of_nonneg (by positivity)]
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      have h1' : κ * (4 * c + 4) < η * N := by
        rwa [lt_div_iff₀ (by positivity)] at hκη
      have h2' := mul_le_mul_of_nonneg_left hκx (by positivity : (0 : ℝ) ≤ η / 2 * N)
      nlinarith
    refine ⟨z, hz, hxz.trans hrη, ?_⟩
    rw [h0]
    calc |fR N σ x + c * (κ / (N * (1 + κ * x))) - fR N σ z|
        ≤ |fR N σ x - fR N σ z| + |c * (κ / (N * (1 + κ * x)))| := by
          have := abs_add_le (fR N σ x - fR N σ z) (c * (κ / (N * (1 + κ * x))))
          rw [show fR N σ x + c * (κ / (N * (1 + κ * x))) - fR N σ z =
            fR N σ x - fR N σ z + c * (κ / (N * (1 + κ * x))) by ring]
          exact this
      _ < η / 2 + η / 2 := add_lt_add hfz hnew
      _ = η := by ring

/-- `|g(y) − g(x)| ≤ 48 c κ³ |y − x| / N` for `g(x) = c κ² / (N (1 + κ x)²)` when
`1 + κ x, 1 + κ y ∈ [1/2, 3/2]`. -/
private lemma rgs_lip {c κ x y : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) (hN : (0 : ℝ) < N)
    (hx1 : 1 / 2 ≤ 1 + κ * x) (hx2 : 1 + κ * x ≤ 3 / 2) (hy1 : 1 / 2 ≤ 1 + κ * y)
    (hy2 : 1 + κ * y ≤ 3 / 2) :
    |c * (κ ^ 2 / (N * (1 + κ * y) ^ 2)) - c * (κ ^ 2 / (N * (1 + κ * x) ^ 2))| ≤
      48 * c * κ ^ 3 / N * |y - x| := by
  set u := 1 + κ * x with hu
  set v := 1 + κ * y with hv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have key : c * (κ ^ 2 / (N * v ^ 2)) - c * (κ ^ 2 / (N * u ^ 2)) =
      c * κ ^ 2 / N * (κ * (x - y) * (u + v) / (u ^ 2 * v ^ 2)) := by
    have e1 : u - v = κ * (x - y) := by rw [hu, hv]; ring
    rw [← e1]
    field_simp
    ring
  rw [key, abs_mul, abs_of_nonneg (by positivity), abs_div, abs_mul, abs_mul,
    abs_of_pos hκ, abs_of_pos (by linarith : 0 < u + v),
    abs_of_pos (by positivity : 0 < u ^ 2 * v ^ 2),
    abs_sub_comm x y]
  have huv : 1 / 16 ≤ u ^ 2 * v ^ 2 := by
    have h1 : 1 / 4 ≤ u ^ 2 := by nlinarith
    have h2 : 1 / 4 ≤ v ^ 2 := by nlinarith
    nlinarith
  have hsum : u + v ≤ 3 := by linarith
  have h3 : κ * |y - x| * (u + v) / (u ^ 2 * v ^ 2) ≤ 48 * κ * |y - x| := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : 0 ≤ κ * |y - x| := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum h4, mul_le_mul_of_nonneg_left huv h4]
  calc c * κ ^ 2 / N * (κ * |y - x| * (u + v) / (u ^ 2 * v ^ 2))
      ≤ c * κ ^ 2 / N * (48 * κ * |y - x|) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 48 * c * κ ^ 3 / N * |y - x| := by ring

private lemma rgs_g_le {c κ x : ℝ} (hc : 0 ≤ c) (hN : (0 : ℝ) < N)
    (h : 1 / 2 ≤ 1 + κ * x) :
    0 ≤ c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ∧
      c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ≤ 4 * c * κ ^ 2 / N := by
  have hp : 0 < 1 + κ * x := by linarith
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hN]
  have hsq : (1 / 2) ^ 2 ≤ (1 + κ * x) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  have h1 : (1 : ℝ) ≤ 4 * (1 + κ * x) ^ 2 := by linarith
  calc c * κ ^ 2 * N = c * κ ^ 2 * N * 1 := by ring
    _ ≤ c * κ ^ 2 * N * (4 * (1 + κ * x) ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 4 * c * κ ^ 2 * (N * (1 + κ * x) ^ 2) := by ring

private lemma rgs_t_le {c κ x : ℝ} (hc : 0 ≤ c) (hN : (0 : ℝ) < N) (hκ : 0 ≤ κ)
    (h : 1 / 2 ≤ 1 + κ * x) :
    0 ≤ c * (κ / (N * (1 + κ * x))) ∧ c * (κ / (N * (1 + κ * x))) ≤ 2 * c * κ / N := by
  have hp : 0 < 1 + κ * x := by linarith
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hN]
  have h1 : (1 : ℝ) ≤ 2 * (1 + κ * x) := by linarith
  calc c * κ * N = c * κ * N * 1 := by ring
    _ ≤ c * κ * N * (2 * (1 + κ * x)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * c * κ * (N * (1 + κ * x)) := by ring

private lemma rgs_h_le {c κ x : ℝ} (hc : 0 ≤ c) (hN : (0 : ℝ) < N) (hκ : 0 ≤ κ)
    (h : 1 / 2 ≤ 1 + κ * x) :
    0 ≤ 2 * (c * (κ ^ 3 / (N * (1 + κ * x) ^ 3))) ∧
      2 * (c * (κ ^ 3 / (N * (1 + κ * x) ^ 3))) ≤ 16 * c * κ ^ 3 / N := by
  have hp : 0 < 1 + κ * x := by linarith
  refine ⟨by positivity, ?_⟩
  have hcube : (1 / 2) ^ 3 ≤ (1 + κ * x) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
  have h1 : (1 : ℝ) ≤ 8 * (1 + κ * x) ^ 3 := by linarith
  rw [mul_div_assoc', ← mul_div_assoc, div_le_div_iff₀ (by positivity) hN]
  calc 2 * (c * κ ^ 3) * N = 2 * (c * κ ^ 3) * N * 1 := by ring
    _ ≤ 2 * (c * κ ^ 3) * N * (8 * (1 + κ * x) ^ 3) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 16 * c * κ ^ 3 * (N * (1 + κ * x) ^ 3) := by ring

/-- A closed ball around a nondegenerate critical point `x₀` of `f`, free of `0` and of the poles,
on which `e f''` (`e = ±1` the sign of `f''(x₀)`) is at least `|f''(x₀)|/2`. -/
private lemma rgs_ball (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x₀ : ℝ}
    (hx₀ : rgs_Good N σ x₀) (hf2 : fR2 N σ x₀ ≠ 0) :
    ∃ ρ > 0, ∃ e m : ℝ, e * e = 1 ∧ |e| = 1 ∧ 0 < m ∧ e * fR2 N σ x₀ = m ∧
      (∀ x, |x - x₀| ≤ ρ → x ≠ 0 ∧ (∀ i, 1 + σ i * x ≠ 0) ∧ m / 2 ≤ e * fR2 N σ x) ∧
      ∀ a b, |a - x₀| ≤ ρ → |b - x₀| ≤ ρ → a ≤ b →
        m / 2 * (b - a) ≤ e * fR1 N σ b - e * fR1 N σ a := by
  obtain ⟨hx0, hxnp, -⟩ := hx₀
  set m := |fR2 N σ x₀| with hm
  have hm0 : 0 < m := abs_pos.mpr hf2
  set e : ℝ := if 0 < fR2 N σ x₀ then 1 else -1 with he
  have he2 : e * e = 1 := by rw [he]; split_ifs <;> norm_num
  have hem : e * fR2 N σ x₀ = m := by
    rw [he, hm]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hf2)]
      ring
  have heabs : |e| = 1 := by rw [he]; split_ifs <;> norm_num
  obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.continuousAt_iff.mp (rgs_contAt_fR2 N σ hx0 hxnp) (m / 2)
    (by positivity)
  have hpole : ∀ s ∈ posVals σ, 0 < |x₀ + s⁻¹| := by
    intro s hs
    have hs0 := rgs_pos_of_mem σ hs
    have := rgs_nonpole_posVals σ hxnp s hs
    rw [abs_pos]
    intro h
    apply this
    have e' : 1 + s * x₀ = s * (x₀ + s⁻¹) := by field_simp; ring
    rw [e', h, mul_zero]
  have hρev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < |x₀| / 2 ∧ ρ < δ2 ∧
      ∀ s ∈ posVals σ, ρ < |x₀ + s⁻¹| / 2 := by
    have hA := Ioo_mem_nhdsGT (show (0 : ℝ) < |x₀| / 2 by have := abs_pos.mpr hx0; positivity)
    have hB := Ioo_mem_nhdsGT hδ2
    have hC : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ s ∈ posVals σ, ρ < |x₀ + s⁻¹| / 2 := by
      rw [Filter.eventually_all_finset]
      intro s hs
      have := hpole s hs
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < |x₀ + s⁻¹| / 2 by positivity)] with ρ hρ
      exact hρ.2
    filter_upwards [hA, hB, hC] with ρ hρ1 hρ2 hρ3
    exact ⟨hρ1.1, hρ1.2, hρ2.2, hρ3⟩
  obtain ⟨ρ, hρ0, hρx, hρδ, hρs⟩ := hρev.exists
  have hIne : ∀ x, |x - x₀| ≤ ρ → x ≠ 0 := fun x hx h => by
    have h1 := abs_sub_abs_le_abs_sub x₀ x
    rw [abs_sub_comm, h, abs_zero] at h1
    rw [h, zero_sub, abs_neg] at hx
    linarith
  have hInp : ∀ x, |x - x₀| ≤ ρ → ∀ i, 1 + σ i * x ≠ 0 := by
    intro x hx i
    rcases (hσ i).eq_or_lt with hi | hi
    · rw [← hi]; simp
    · have hs := rgs_mem_posVals σ hi
      have h1' := hρs (σ i) hs
      have h2' : |x₀ + (σ i)⁻¹| - ρ ≤ |x + (σ i)⁻¹| := by
        have := abs_sub_abs_le_abs_sub (x₀ + (σ i)⁻¹) (x + (σ i)⁻¹)
        have e' : x₀ + (σ i)⁻¹ - (x + (σ i)⁻¹) = -(x - x₀) := by ring
        rw [e', abs_neg] at this
        linarith
      have h3' : 0 < |x + (σ i)⁻¹| := by linarith [hpole (σ i) hs]
      intro h
      have e' : 1 + σ i * x = σ i * (x + (σ i)⁻¹) := by field_simp; ring
      rw [e'] at h
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · rw [h, abs_zero] at h3'
        linarith
  have hIf2 : ∀ x, |x - x₀| ≤ ρ → m / 2 ≤ e * fR2 N σ x := by
    intro x hx
    have h1' := hδ2' (x := x) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h1'
    have h3 : |e * fR2 N σ x - e * fR2 N σ x₀| < m / 2 := by
      rw [← mul_sub, abs_mul, heabs, one_mul]
      exact h1'
    rw [hem] at h3
    have := (abs_lt.mp h3).1
    linarith
  have hGd : ∀ x, |x - x₀| ≤ ρ → HasDerivAt (fun y => e * fR1 N σ y) (e * fR2 N σ x) x :=
    fun x hx => (hasDerivAt_fR1 N σ (hIne x hx) (hInp x hx)).const_mul e
  refine ⟨ρ, hρ0, e, m, he2, heabs, hm0, hem, fun x hx => ⟨hIne x hx, hInp x hx, hIf2 x hx⟩, ?_⟩
  intro a b ha hb hab
  rcases hab.eq_or_lt with h | h
  · rw [h]; simp
  · have hIcc : ∀ x ∈ Set.Icc a b, |x - x₀| ≤ ρ := by
      intro x hx
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y => e * fR1 N σ y)
      (fun y => e * fR2 N σ y) h
      (fun x hx => (hGd x (hIcc x hx)).continuousAt.continuousWithinAt)
      (fun x hx => hGd x (hIcc x (Set.Ioo_subset_Icc_self hx)))
    have h1' := hIf2 ξ (hIcc ξ (Set.Ioo_subset_Icc_self hξ))
    rw [hξeq, le_div_iff₀ (by linarith)] at h1'
    linarith

/-- Near a nondegenerate critical point `x₀` of `f`, `f_κ` has exactly one critical point for
small `κ`; it tends to `x₀`, its value tends to `f(x₀)`, `f_κ''` there tends to `f''(x₀)` and
has the sign of `f''(x₀)`. -/
private lemma rgs_local (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {K : ℕ}
    (σ' : ℝ → Fin K → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ κ x, fR N (σ' κ) x = fR N σ x + c * (κ / (N * (1 + κ * x))))
    (h1 : ∀ κ x, fR1 N (σ' κ) x = fR1 N σ x - c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)))
    (h2 : ∀ κ x, fR2 N (σ' κ) x = fR2 N σ x + 2 * (c * (κ ^ 3 / (N * (1 + κ * x) ^ 3))))
    (hent : ∀ κ i, (∃ l, σ' κ i = σ l) ∨ σ' κ i = κ)
    {x₀ : ℝ} (hx₀ : rgs_Good N σ x₀) (hf2 : fR2 N σ x₀ ≠ 0) :
    ∃ ρ > 0, ∀ η > 0, ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ x', rgs_Good N (σ' κ) x' ∧ |x' - x₀| < η ∧
      |fR N (σ' κ) x' - fR N σ x₀| < η ∧ |fR2 N (σ' κ) x' - fR2 N σ x₀| < η ∧
      0 < fR2 N (σ' κ) x' * fR2 N σ x₀ ∧
      ∀ y, |y - x₀| < ρ → rgs_Good N (σ' κ) y → y = x' := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ρ, hρ0, e, m, he2, heabs, hm0, hem, hball, hslope⟩ := rgs_ball σ hσ hx₀ hf2
  obtain ⟨hx0, hxnp, hxf⟩ := hx₀
  have he0 : e ≠ 0 := by intro h; rw [h, abs_zero] at heabs; norm_num at heabs
  have hslope' : ∀ a b, |a - x₀| ≤ ρ → |b - x₀| ≤ ρ →
      m / 2 * |b - a| ≤ |e * fR1 N σ b - e * fR1 N σ a| := by
    intro a b ha hb
    rcases le_total a b with h | h
    · have := hslope a b ha hb h
      rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
      exact this.trans (le_abs_self _)
    · have := hslope b a hb ha h
      rw [abs_of_nonpos (by linarith : b - a ≤ 0), abs_sub_comm]
      calc m / 2 * -(b - a) = m / 2 * (a - b) := by ring
        _ ≤ _ := this.trans (le_abs_self _)
  refine ⟨ρ, hρ0, fun η hη => ?_⟩
  obtain ⟨δa, hδa, hδa'⟩ := Metric.continuousAt_iff.mp (rgs_contAt_fR N σ hx0 hxnp) (η / 2)
    (by positivity)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.mp (rgs_contAt_fR2 N σ hx0 hxnp) (η / 2)
    (by positivity)
  set δ0 := min δa δ1 with hδ0def
  have hδ0 : 0 < δ0 := lt_min hδa hδ1
  have hδ0' : ∀ {x : ℝ}, dist x x₀ < δ0 → dist (fR N σ x) (fR N σ x₀) < η / 2 :=
    fun hx => hδa' (lt_of_lt_of_le hx (min_le_left _ _))
  set Kx : ℝ := |x₀| + ρ with hKx
  have hKx0 : 0 < Kx := by positivity
  set Q : ℝ := 48 * c / N + 1 with hQ
  have hQ0 : 0 < Q := by positivity
  set θ : ℝ := min (m / 2) (min (m * ρ / 2) (min (m * min η δ0 / 8) (η / 2))) with hθ
  have hmin : 0 < min η δ0 := lt_min hη hδ0
  have hθ0 : 0 < θ :=
    lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hθ1 : θ ≤ m / 2 := min_le_left _ _
  have hθ2 : θ ≤ m * ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ m * min η δ0 / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ4 : θ ≤ η / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set κ₀ : ℝ := min 1 (min (1 / (2 * Kx)) (θ / Q)) with hκ₀
  have hκ₀0 : 0 < κ₀ := lt_min one_pos (lt_min (by positivity) (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hκ₀0] with κ hκ
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hκle : κ < 1 := lt_of_lt_of_le hκ1 (min_le_left _ _)
  have hκK : κ < 1 / (2 * Kx) := lt_of_lt_of_le hκ1 ((min_le_right _ _).trans (min_le_left _ _))
  have hκQ : κ < θ / Q := lt_of_lt_of_le hκ1 ((min_le_right _ _).trans (min_le_right _ _))
  have hcκ : 48 * c * κ / N < θ := by
    rw [lt_div_iff₀ hQ0] at hκQ
    have e1 : 48 * c * κ / N = κ * (48 * c / N) := by ring
    have e2 : κ * Q = κ * (48 * c / N) + κ := by rw [hQ]; ring
    rw [e1]
    linarith
  have hk2 : κ ^ 2 ≤ κ := by
    rw [sq]; exact mul_le_of_le_one_left hκ0.le hκle.le
  have hk3 : κ ^ 3 ≤ κ := by
    rw [pow_succ]; exact (mul_le_of_le_one_right (by positivity) hκle.le).trans hk2
  have hcκ2 : 4 * c * κ ^ 2 / N ≤ 48 * c * κ / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    have : 4 * c * κ ^ 2 ≤ 4 * c * κ := mul_le_mul_of_nonneg_left hk2 (by positivity)
    have : 4 * c * κ ≤ 48 * c * κ := by
      have : 0 ≤ c * κ := by positivity
      linarith
    linarith
  have hcκ3 : 48 * c * κ ^ 3 / N ≤ 48 * c * κ / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    exact mul_le_mul_of_nonneg_left hk3 (by positivity)
  have hcκ16 : 16 * c * κ ^ 3 / N ≤ 48 * c * κ / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    have : 16 * c * κ ^ 3 ≤ 16 * c * κ := mul_le_mul_of_nonneg_left hk3 (by positivity)
    have : 16 * c * κ ≤ 48 * c * κ := by
      have : 0 ≤ c * κ := by positivity
      linarith
    linarith
  have hcκ1 : 2 * c * κ / N ≤ 48 * c * κ / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    have : 0 ≤ c * κ := by positivity
    linarith
  have hκx : ∀ x, |x - x₀| ≤ ρ → 1 / 2 ≤ 1 + κ * x ∧ 1 + κ * x ≤ 3 / 2 := by
    intro x hx
    have h1' : |x| ≤ Kx := by
      have := abs_sub_abs_le_abs_sub x x₀
      rw [hKx]
      linarith
    have h2' : |κ * x| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hκ0]
      calc κ * |x| ≤ 1 / (2 * Kx) * Kx := mul_le_mul hκK.le h1' (abs_nonneg _) (by positivity)
        _ = 1 / 2 := by field_simp
    constructor <;> linarith [abs_le.mp h2']
  have hnpκ : ∀ x, |x - x₀| ≤ ρ → ∀ i, 1 + σ' κ i * x ≠ 0 := by
    intro x hx i
    rcases hent κ i with ⟨l, hl⟩ | hl
    · rw [hl]; exact (hball x hx).2.1 l
    · rw [hl]; have := (hκx x hx).1; linarith
  have hgb : ∀ x, |x - x₀| ≤ ρ →
      0 ≤ c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ∧
        c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) ≤ 4 * c * κ ^ 2 / N :=
    fun x hx => rgs_g_le hc hNr (hκx x hx).1
  have hF : ∀ x, e * fR1 N (σ' κ) x =
      e * fR1 N σ x - e * (c * (κ ^ 2 / (N * (1 + κ * x) ^ 2))) := by
    intro x
    rw [h1]
    ring
  have hFc : ContinuousOn (fun x => e * fR1 N (σ' κ) x) (Set.Icc (x₀ - ρ) (x₀ + ρ)) := by
    intro x hx
    have hx' : |x - x₀| ≤ ρ := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    exact ((rgs_contAt_fR1 N (σ' κ) (hball x hx').1 (hnpκ x hx')).const_mul e).continuousWithinAt
  have hρb : |x₀ + ρ - x₀| ≤ ρ := by rw [add_sub_cancel_left, abs_of_pos hρ0]
  have hρa : |x₀ - ρ - x₀| ≤ ρ := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hρ0]
  have hx₀b : |x₀ - x₀| ≤ ρ := by rw [sub_self, abs_zero]; exact hρ0.le
  have hgρ : 4 * c * κ ^ 2 / N < m * ρ / 2 := lt_of_le_of_lt hcκ2 (lt_of_lt_of_le hcκ hθ2)
  have hFb : 0 < e * fR1 N (σ' κ) (x₀ + ρ) := by
    rw [hF]
    have h1' := hslope x₀ (x₀ + ρ) hx₀b hρb (by linarith)
    rw [hxf, mul_zero, sub_zero, add_sub_cancel_left] at h1'
    have h2' := hgb (x₀ + ρ) hρb
    have h4' : e * (c * (κ ^ 2 / (N * (1 + κ * (x₀ + ρ)) ^ 2))) ≤
        c * (κ ^ 2 / (N * (1 + κ * (x₀ + ρ)) ^ 2)) := by
      have := le_abs_self (e * (c * (κ ^ 2 / (N * (1 + κ * (x₀ + ρ)) ^ 2))))
      rwa [abs_mul, heabs, one_mul, abs_of_nonneg h2'.1] at this
    have : m / 2 * ρ = m * ρ / 2 := by ring
    linarith
  have hFa : e * fR1 N (σ' κ) (x₀ - ρ) < 0 := by
    rw [hF]
    have h1' := hslope (x₀ - ρ) x₀ hρa hx₀b (by linarith)
    rw [hxf, mul_zero, zero_sub, sub_sub_cancel] at h1'
    have h2' := hgb (x₀ - ρ) hρa
    have h4' : -(c * (κ ^ 2 / (N * (1 + κ * (x₀ - ρ)) ^ 2))) ≤
        e * (c * (κ ^ 2 / (N * (1 + κ * (x₀ - ρ)) ^ 2))) := by
      have := neg_abs_le (e * (c * (κ ^ 2 / (N * (1 + κ * (x₀ - ρ)) ^ 2))))
      rwa [abs_mul, heabs, one_mul, abs_of_nonneg h2'.1] at this
    have : m / 2 * ρ = m * ρ / 2 := by ring
    linarith
  obtain ⟨x', hx'I, hx'F⟩ := intermediate_value_Ioo (by linarith : x₀ - ρ ≤ x₀ + ρ) hFc
    ⟨hFa, hFb⟩
  have hx'b : |x' - x₀| < ρ := by rw [abs_lt]; constructor <;> linarith [hx'I.1, hx'I.2]
  have hx'f : fR1 N (σ' κ) x' = 0 := by
    rcases mul_eq_zero.mp hx'F with h | h
    · exact absurd h he0
    · exact h
  have hx'G : e * fR1 N σ x' = e * (c * (κ ^ 2 / (N * (1 + κ * x') ^ 2))) := by
    have := hF x'
    rw [hx'f, mul_zero] at this
    linarith
  -- closeness
  have hclose : |x' - x₀| < min η δ0 := by
    have h1' := hslope' x₀ x' hx₀b hx'b.le
    rw [hx'G, hxf, mul_zero, sub_zero, abs_mul, heabs, one_mul,
      abs_of_nonneg (hgb x' hx'b.le).1] at h1'
    have h2' := (hgb x' hx'b.le).2
    have h4 : 48 * c * κ / N < m * min η δ0 / 8 := lt_of_lt_of_le hcκ hθ3
    have h5 : m * min η δ0 / 8 ≤ m / 2 * min η δ0 := by
      have : 0 ≤ m * min η δ0 := by positivity
      linarith
    have h3' : m / 2 * |x' - x₀| < m / 2 * min η δ0 := by linarith
    exact lt_of_mul_lt_mul_left h3' (by positivity)
  have hx'η : |x' - x₀| < η := lt_of_lt_of_le hclose (min_le_left _ _)
  have hx'δ : |x' - x₀| < δ0 := lt_of_lt_of_le hclose (min_le_right _ _)
  refine ⟨x', ⟨(hball x' hx'b.le).1, hnpκ x' hx'b.le, hx'f⟩, hx'η, ?_, ?_, ?_, ?_⟩
  · have hv1 : |fR N σ x' - fR N σ x₀| < η / 2 := by
      have := hδ0' (x := x') (by rw [Real.dist_eq]; exact hx'δ)
      rwa [Real.dist_eq] at this
    have hv2 : |c * (κ / (N * (1 + κ * x')))| < η / 2 := by
      obtain ⟨ht0, ht1⟩ := rgs_t_le hc hNr hκ0.le (hκx x' hx'b.le).1
      rw [abs_of_nonneg ht0]
      linarith
    rw [h0]
    calc |fR N σ x' + c * (κ / (N * (1 + κ * x'))) - fR N σ x₀|
        ≤ |fR N σ x' - fR N σ x₀| + |c * (κ / (N * (1 + κ * x')))| := by
          rw [show fR N σ x' + c * (κ / (N * (1 + κ * x'))) - fR N σ x₀ =
            fR N σ x' - fR N σ x₀ + c * (κ / (N * (1 + κ * x'))) by ring]
          exact abs_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add hv1 hv2
      _ = η := by ring
  · have hv1 : |fR2 N σ x' - fR2 N σ x₀| < η / 2 := by
      have := hδ1' (x := x') (by rw [Real.dist_eq]; exact lt_of_lt_of_le hx'δ (min_le_right _ _))
      rwa [Real.dist_eq] at this
    obtain ⟨hh0, hh1⟩ := rgs_h_le hc hNr hκ0.le (hκx x' hx'b.le).1
    have hv2 : 2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3))) < η / 2 := by linarith
    rw [h2]
    calc |fR2 N σ x' + 2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3))) - fR2 N σ x₀|
        ≤ |fR2 N σ x' - fR2 N σ x₀| + |2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3)))| := by
          rw [show fR2 N σ x' + 2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3))) - fR2 N σ x₀ =
            fR2 N σ x' - fR2 N σ x₀ + 2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3))) by ring]
          exact abs_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add hv1 (by rw [abs_of_nonneg hh0]; exact hv2)
      _ = η := by ring
  · have hs1 := (hball x' hx'b.le).2.2
    obtain ⟨hh0, hh1⟩ := rgs_h_le hc hNr hκ0.le (hκx x' hx'b.le).1
    have hs2 : 2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3))) < m / 2 := by linarith
    have hs3 : 0 < e * fR2 N (σ' κ) x' := by
      rw [h2, mul_add]
      have := neg_abs_le (e * (2 * (c * (κ ^ 3 / (N * (1 + κ * x') ^ 3)))))
      rw [abs_mul, heabs, one_mul, abs_of_nonneg hh0] at this
      linarith
    have : fR2 N (σ' κ) x' * fR2 N σ x₀ = (e * fR2 N (σ' κ) x') * (e * fR2 N σ x₀) := by
      rw [show (e * fR2 N (σ' κ) x') * (e * fR2 N σ x₀) =
        (e * e) * (fR2 N (σ' κ) x' * fR2 N σ x₀) by ring, he2, one_mul]
    rw [this, hem]
    positivity
  · intro y hy hyg
    obtain ⟨-, -, hyf⟩ := hyg
    have hyG : e * fR1 N σ y = e * (c * (κ ^ 2 / (N * (1 + κ * y) ^ 2))) := by
      have := hF y
      rw [hyf, mul_zero] at this
      linarith
    have h1' := hslope' x' y hx'b.le hy.le
    rw [hyG, hx'G, ← mul_sub, abs_mul, heabs, one_mul] at h1'
    have h2' := rgs_lip (N := N) hc hκ0 hNr (hκx x' hx'b.le).1 (hκx x' hx'b.le).2
      (hκx y hy.le).1 (hκx y hy.le).2
    have h3' : 48 * c * κ ^ 3 / N < m / 2 := lt_of_le_of_lt hcκ3 (lt_of_lt_of_le hcκ hθ1)
    by_contra hne
    have hpos' : 0 < |y - x'| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h4 : m / 2 * |y - x'| ≤ 48 * c * κ ^ 3 / N * |y - x'| := h1'.trans h2'
    have h5 : 48 * c * κ ^ 3 / N * |y - x'| < m / 2 * |y - x'| :=
      mul_lt_mul_of_pos_right h3' hpos'
    linarith

/-! ## The regular edge of `Ŝ + κ P₀` -/

private lemma rgs_edgec2_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgec2 τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  unfold edgec2
  positivity

/-- Two numbers whose product is positive, with signs `(-1)^{l+1}` and `(-1)^{l'+1}`, force
`l ≡ l' (mod 2)`. -/
private lemma rgs_parity {l l' : ℕ} {A B : ℝ} (hA : 0 < (-1 : ℝ) ^ (l + 1) * A)
    (hB : 0 < (-1 : ℝ) ^ (l' + 1) * B) (hAB : 0 < B * A) : (Even l ↔ Even l') := by
  have key : ∀ n : ℕ, (-1 : ℝ) ^ (n + 1) = if Even n then -1 else 1 := by
    intro n
    rcases Nat.even_or_odd n with h | h
    · rw [pow_succ, h.neg_one_pow]; simp [h]
    · rw [pow_succ, h.neg_one_pow]; simp [Nat.not_even_iff_odd.mpr h]
  rw [key] at hA hB
  by_cases hl : Even l <;> by_cases hl' : Even l' <;>
    simp only [hl, hl', ↓reduceIte] at hA hB
  · exact ⟨fun _ => hl', fun _ => hl⟩
  · exfalso
    have h1 : A < 0 := by linarith
    have h2 : 0 < B := by linarith
    nlinarith
  · exfalso
    have h1 : 0 < A := by linarith
    have h2 : B < 0 := by linarith
    nlinarith
  · exact ⟨fun h => absurd h hl, fun h => absurd h hl'⟩

/-- `Ŝ + κ P₀` has nonnegative eigenvalues, a positive value, and satisfies Assumption 2.1 at
some parameter. -/
private lemma rgs_regS_facts {K : ℕ} (hN : 0 < N) {T : Matrix (Fin M) (Fin K) ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hS : (posVals (specOf (T * Tᵀ))).Nonempty) :
    (∀ i, 0 ≤ specOf (regS κ (Tᵀ * T)) i) ∧ (posVals (specOf (regS κ (Tᵀ * T)))).Nonempty ∧
      ∃ τk, DensityAssumptions τk N (specOf (regS κ (Tᵀ * T))) := by
  have hpos := rgs_regS_pos hκ T
  obtain ⟨s, hs⟩ := hS
  obtain ⟨l, -, hl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  have hl0 : 0 < specOf (T * Tᵀ) l := by rw [hl]; exact rgs_pos_of_mem _ hs
  obtain ⟨i, -⟩ := rgs_regS_of_pos κ T hl0
  exact ⟨fun j => (hpos j).le, ⟨_, rgs_mem_posVals _ (hpos i)⟩,
    rgs_da_exists (fun j => (hpos j).le) hN (hpos i)⟩

/-- The edge part of the transfer: a regular edge `l` of `Σ` gives, for all small `κ`, an edge `l'`
of `Ŝ + κ P₀` of the same parity, regular at `τ_e`, within `η` of `a_l`, with `f_κ''(x_{l'})`
within `η` of `f''(x_l)`; every other edge value of `Ŝ + κ P₀` is `< η` or within `η` of an edge
value `a_i`, `i ≠ l`, of `Σ`. -/
private lemma rgs_edge_part {τ τ₀ : ℝ} (hτ : 0 < τ) (hτ₀ : τ / 2 ≤ τ₀) {K : ℕ} (hN : 1 ≤ N)
    {T : Matrix (Fin M) (Fin K) ℝ} (hda : DensityAssumptions τ N (specOf (T * Tᵀ)))
    {l : ℕ} (hl : RegularEdge τ₀ N (specOf (T * Tᵀ)) l) :
    ∃ ρ > 0, ∀ η, 0 < η → η ≤ ρ → η ≤ deltaA τ →
      ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
        |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) l| < η ∧
        (Even l ↔ Even l') ∧
        |fR2 N (specOf (regS κ (Tᵀ * T))) (xCrit N (specOf (regS κ (Tᵀ * T))) l') -
          fR2 N (specOf (T * Tᵀ)) (xCrit N (specOf (T * Tᵀ)) l)| < η ∧
        ∀ j, 1 ≤ j → j ≤ 2 * numBands N (specOf (regS κ (Tᵀ * T))) → j ≠ l' →
          edgeVal N (specOf (regS κ (Tᵀ * T))) j < η ∨
          ∃ i, 1 ≤ i ∧ i ≤ 2 * numBands N (specOf (T * Tᵀ)) ∧ i ≠ l ∧
            |edgeVal N (specOf (regS κ (Tᵀ * T))) j - edgeVal N (specOf (T * Tᵀ)) i| < η := by
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := hda.nonneg
  have hN0 : 0 < N := hN
  have hreg := hl
  obtain ⟨hl1, hl2, hal, hgap, hpole⟩ := hl
  have hp1 : 1 ≤ numBands N σ := by omega
  have hS : (posVals σ).Nonempty := rgs_posVals_nonempty N σ hp1
  have hτ₀0 : 0 < τ₀ := by linarith
  have hfin : ¬ (l = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨h1, h2⟩
    have := rgs_edgeVal_last_zero N σ h2
    rw [← h1] at this
    linarith
  set x₀ := xCrit N σ l with hx₀def
  have hx₀ : rgs_Good N σ x₀ := rgs_good_xCrit N σ hσ hN0 hS hl1 hl2 hfin
  have hal_eq : edgeVal N σ l = fR N σ x₀ := edgeVal_eq_fR N σ hσ hN0 hS hl1 hl2 hfin
  have hda2 : DensityAssumptions (τ / 2) N σ := rgs_da_mono hda (by positivity) (by linarith)
  have hc2 := edgec2_le_fR2_xCrit hda2 (regularEdge_mono hreg hτ₀)
  have hc2pos := rgs_edgec2_pos (show 0 < τ / 2 by positivity)
  have hsx₀ : 0 < (-1 : ℝ) ^ (l + 1) * fR2 N σ x₀ := lt_of_lt_of_le hc2pos hc2
  have hf2 : fR2 N σ x₀ ≠ 0 := fun h => by rw [h, mul_zero] at hsx₀; exact lt_irrefl 0 hsx₀
  set σ' : ℝ → Fin K → ℝ := fun κ => specOf (regS κ (Tᵀ * T)) with hσ'
  set c : ℝ := ((K - T.rank : ℕ) : ℝ) with hcdef
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have h0 : ∀ κ x, fR N (σ' κ) x = fR N σ x + c * (κ / (N * (1 + κ * x))) :=
    fun κ x => rgs_fR_regS N κ T x
  have h1 : ∀ κ x, fR1 N (σ' κ) x = fR1 N σ x - c * (κ ^ 2 / (N * (1 + κ * x) ^ 2)) :=
    fun κ x => rgs_fR1_regS N κ T x
  have h2 : ∀ κ x, fR2 N (σ' κ) x = fR2 N σ x + 2 * (c * (κ ^ 3 / (N * (1 + κ * x) ^ 3))) :=
    fun κ x => rgs_fR2_regS N κ T x
  have hent : ∀ κ i, (∃ l, σ' κ i = σ l) ∨ σ' κ i = κ := fun κ i => rgs_regS_eig κ T i
  have hpos : ∀ κ l, 0 < σ l → ∃ i, σ' κ i = σ l := fun κ l hl => rgs_regS_of_pos κ T hl
  obtain ⟨ρ, hρ, hloc⟩ := rgs_local σ hσ hN0 σ' hc h0 h1 h2 hent hx₀ hf2
  refine ⟨ρ, hρ, fun η hη hηρ hηδ => ?_⟩
  have hτe0 : 0 < tauE τ := tauE_pos hτ
  have hτe4 : tauE τ ≤ τ / 4 := min_le_right _ _
  have hδa16 : deltaA τ ≤ τ / 16 := min_le_right _ _
  have hglob := rgs_global σ hσ hN0 hS σ' hc h0 h1 hpos hη
  have hloc' := hloc η hη
  have hκsmall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ < 1 / (|x₀| + η + tauE τ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (|x₀| + η + tauE τ) by positivity)]
      with κ hκ using hκ.2
  filter_upwards [hglob, hloc', hκsmall, self_mem_nhdsWithin] with κ hG hL hκs hκ0
  have hκ0' : 0 < κ := hκ0
  obtain ⟨x', hx'g, hx'c, hx'v, hx'f2, hx'sign, huniq⟩ := hL
  obtain ⟨hσκ, hS', τk, hdak⟩ := rgs_regS_facts hN0 hκ0' hS
  obtain ⟨l', hl'1, hl'2, hl'fin, hl'x⟩ := rgs_index_of_good N (σ' κ) hσκ hN0 hS' hx'g
  have ha' : edgeVal N (σ' κ) l' = fR N (σ' κ) x' := by
    rw [edgeVal_eq_fR N (σ' κ) hσκ hN0 hS' hl'1 hl'2 hl'fin, hl'x]
  have hval : |edgeVal N (σ' κ) l' - edgeVal N σ l| < η := by
    rw [ha', hal_eq]
    exact hx'v
  have hval' := abs_lt.mp hval
  -- the other edges
  have hclass : ∀ j, 1 ≤ j → j ≤ 2 * numBands N (σ' κ) → j ≠ l' →
      edgeVal N (σ' κ) j < η ∨ ∃ i, 1 ≤ i ∧ i ≤ 2 * numBands N σ ∧ i ≠ l ∧
        |edgeVal N (σ' κ) j - edgeVal N σ i| < η := by
    intro j hj1 hj2 hjl
    by_cases hjf : j = 2 * numBands N (σ' κ) ∧ yEdge N (σ' κ) = 0
    · left
      rw [hjf.1, rgs_edgeVal_last_zero _ _ hjf.2]
      exact hη
    · have hgj := rgs_good_xCrit N (σ' κ) hσκ hN0 hS' hj1 hj2 hjf
      have haj : edgeVal N (σ' κ) j = fR N (σ' κ) (xCrit N (σ' κ) j) :=
        edgeVal_eq_fR N (σ' κ) hσκ hN0 hS' hj1 hj2 hjf
      rcases hG _ hgj with ⟨z, hz, hxz, hfz⟩ | hsmall
      · by_cases hzx : z = x₀
        · exfalso
          have hjx : xCrit N (σ' κ) j = x' := huniq _ (by rw [← hzx]; linarith) hgj
          have hz2 : fR2 N (σ' κ) x' = 0 := by
            rcases lt_or_gt_of_ne hjl with hlt | hgt
            · have := rgs_fR2_of_dup N (σ' κ) hσκ hN0 hS' hj1 hlt hl'2 hl'fin
                (by rw [hjx, hl'x])
              rwa [hjx] at this
            · have := rgs_fR2_of_dup N (σ' κ) hσκ hN0 hS' hl'1 hgt hj2 hjf
                (by rw [hjx, hl'x])
              rwa [hl'x] at this
          rw [hz2, zero_mul] at hx'sign
          exact lt_irrefl 0 hx'sign
        · right
          obtain ⟨i, hi1, hi2, hifin, hix⟩ := rgs_index_of_good N σ hσ hN0 hS hz
          refine ⟨i, hi1, hi2, fun hil => hzx (by rw [← hix, hil]), ?_⟩
          rw [haj, edgeVal_eq_fR N σ hσ hN0 hS hi1 hi2 hifin, hix]
          exact hfz
      · left
        rw [haj]
        exact (abs_lt.mp hsmall).2
  have hregE : RegularEdge (tauE τ) N (σ' κ) l' := by
    refine ⟨hl'1, hl'2, by linarith, ?_, ?_⟩
    · intro j hj1 hj2 hjl
      rcases hclass j hj1 hj2 hjl with hsmall | ⟨i, hi1, hi2, hil, hij⟩
      · have := le_abs_self (edgeVal N (σ' κ) l' - edgeVal N (σ' κ) j)
        linarith
      · have hg := hgap i hi1 hi2 hil
        have h1' := abs_sub_abs_le_abs_sub (edgeVal N σ l - edgeVal N σ i)
          (edgeVal N (σ' κ) l' - edgeVal N (σ' κ) j)
        have h2' : |edgeVal N σ l - edgeVal N σ i -
            (edgeVal N (σ' κ) l' - edgeVal N (σ' κ) j)| ≤
            |edgeVal N (σ' κ) l' - edgeVal N σ l| + |edgeVal N (σ' κ) j - edgeVal N σ i| := by
          have := abs_add_le (-(edgeVal N (σ' κ) l' - edgeVal N σ l))
            (edgeVal N (σ' κ) j - edgeVal N σ i)
          rw [abs_neg] at this
          rw [show edgeVal N σ l - edgeVal N σ i - (edgeVal N (σ' κ) l' - edgeVal N (σ' κ) j) =
            -(edgeVal N (σ' κ) l' - edgeVal N σ l) + (edgeVal N (σ' κ) j - edgeVal N σ i) by ring]
          exact this
        linarith
    · intro _ s hs
      rw [hl'x]
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
      rcases hent κ i with ⟨l₀, hl₀⟩ | hκi
      · have hs0 : 0 < s := rgs_pos_of_mem _ hs
        have hsσ : s ∈ posVals σ := by
          rw [← hi, hl₀] at hs0 ⊢
          exact rgs_mem_posVals σ hs0
        have h1' := hpole hfin s hsσ
        have h2' := abs_sub_abs_le_abs_sub (x₀ + s⁻¹) (x' + s⁻¹)
        rw [show x₀ + s⁻¹ - (x' + s⁻¹) = -(x' - x₀) by ring, abs_neg] at h2'
        linarith
      · rw [← hi, hκi]
        have h1' : |x'| ≤ |x₀| + η := by
          have := abs_sub_abs_le_abs_sub x' x₀
          linarith
        have h2' : |x₀| + η + tauE τ < κ⁻¹ := by
          rw [lt_inv_comm₀ (by positivity) hκ0', ← one_div]
          exact hκs
        have h3' : κ⁻¹ - |x'| ≤ |x' + κ⁻¹| := by
          have := abs_sub_abs_le_abs_sub κ⁻¹ (-x')
          rw [abs_neg, abs_of_pos (inv_pos.mpr hκ0'), sub_neg_eq_add, add_comm] at this
          exact this
        linarith
  refine ⟨l', hregE, hval, ?_, by rw [hl'x]; exact hx'f2, hclass⟩
  -- parity, from the sign of `f''`
  set τk' := min τk (tauE τ) with hτk'
  have hτk'0 : 0 < τk' := lt_min hdak.pos hτe0
  have hdak' := rgs_da_mono hdak hτk'0 (min_le_left _ _)
  have hck := edgec2_le_fR2_xCrit hdak' (regularEdge_mono hregE (min_le_right _ _))
  rw [hl'x] at hck
  have hsx' : 0 < (-1 : ℝ) ^ (l' + 1) * fR2 N (σ' κ) x' :=
    lt_of_lt_of_le (rgs_edgec2_pos hτk'0) hck
  exact rgs_parity hsx₀ hsx' hx'sign


/-- `(d' : ℝ) < d + 1` gives `d' ≤ d`. -/
private lemma rgs_nat_le {a b : ℕ} (h : (a : ℝ) < b + 1) : a ≤ b := by
  have : a < b + 1 := by exact_mod_cast h
  omega

/-- The gap condition of a regular edge `l`, in one-sided form. -/
private lemma rgs_gap_side {τ₀ : ℝ} {σ : Fin M → ℝ} {l : ℕ}
    (hgap : ∀ i, 1 ≤ i → i ≤ 2 * numBands N σ → i ≠ l →
      τ₀ ≤ |edgeVal N σ l - edgeVal N σ i|) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ 2 * numBands N σ) (hil : i ≠ l) :
    edgeVal N σ l + τ₀ ≤ edgeVal N σ i ∨ edgeVal N σ i ≤ edgeVal N σ l - τ₀ := by
  have h := hgap i hi1 hi2 hil
  rcases le_abs'.mp h with h' | h'
  · left; linarith
  · right; linarith

private lemma rgs_nClass_nonneg (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : 0 ≤ nClass N σ E := by
  unfold nClass
  positivity

/-- The transfer at an upper edge `l = 2k + 1`: for every `η > 0`, eventually in `κ ↓ 0`, an upper
edge `l'` of `Ŝ + κ P₀`, regular at `τ_e`, with `d'_{l̂'-1} = d_k`, `|a_{l'} - a_l| < η` and
`|f_κ''(x_{l'}) - f''(x_l)| < η`. -/
private lemma rgs_upper {τ τ₀ : ℝ} (hτ : 0 < τ) (hτ₀ : τ / 2 ≤ τ₀) {K : ℕ} (hN : 1 ≤ N)
    {T : Matrix (Fin M) (Fin K) ℝ} (hda : DensityAssumptions τ N (specOf (T * Tᵀ)))
    {k : ℕ} (hl : RegularEdge τ₀ N (specOf (T * Tᵀ)) (2 * k + 1)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      l' % 2 = 1 ∧
      cumCount N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2 - 1) = cumCount N (specOf (T * Tᵀ)) k ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) (2 * k + 1)| < η ∧
      |fR2 N (specOf (regS κ (Tᵀ * T))) (xCrit N (specOf (regS κ (Tᵀ * T))) l') -
        fR2 N (specOf (T * Tᵀ)) (xCrit N (specOf (T * Tᵀ)) (2 * k + 1))| < η := by
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := hda.nonneg
  have hN0 : 0 < N := hN
  obtain ⟨ρ, hρ, hedge⟩ := rgs_edge_part hτ hτ₀ hN hda hl
  obtain ⟨hl1, hl2, hal, hgap, -⟩ := hl
  have hp1 : 1 ≤ numBands N σ := by omega
  have hS := rgs_posVals_nonempty N σ hp1
  have hτ₀0 : 0 < τ₀ := by linarith
  have hδa0 : 0 < deltaA τ :=
    lt_min (by have := edgeTau'_pos (tauE_pos hτ); positivity) (by positivity)
  have hkp : k + 1 ≤ numBands N σ := by omega
  set Eg := edgeVal N σ (2 * k + 1) + τ₀ / 2 with hEg
  have hEg0 : 0 < Eg := by linarith
  set η' := min (min ρ (deltaA τ)) (min η (τ₀ / 4)) with hη'
  have hη'0 : 0 < η' := lt_min (lt_min hρ hδa0) (lt_min hη (by positivity))
  have hηρ : η' ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η' ≤ deltaA τ := (min_le_left _ _).trans (min_le_right _ _)
  have hηη : η' ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hητ : η' ≤ τ₀ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hT1 := (tendsto_nClass_regS hN T hEg0).eventually (Metric.ball_mem_nhds _ one_pos)
  have hlk : edgeVal N σ (2 * k + 1) = edgeVal N σ (2 * (k + 1) - 1) := by
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hnEg : nClass N σ Eg ≤ cumCount N σ k := by
    have h1 := (nClass_edgeVal hda (k := k + 1) (by omega) hkp).1
    rw [← hlk, show k + 1 - 1 = k by omega] at h1
    rw [← h1]
    exact rgs_nClass_anti hσ hN0 (by linarith)
  have hnEg' : (cumCount N σ k : ℝ) ≤ nClass N σ Eg := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simpa [cumCount] using rgs_nClass_nonneg N σ Eg
    · have hup := rgs_edgeVal_anti N σ hσ hN0 hS (i := 2 * k) (j := 2 * k + 1) (by omega)
        (by omega) hl2
      have hbig : Eg ≤ edgeVal N σ (2 * k) := by
        rcases rgs_gap_side hgap (i := 2 * k) (by omega) (by omega) (by omega) with h | h
        · linarith
        · linarith
      have h2 := (nClass_edgeVal hda (k := k) (by omega) (by omega)).2 (by linarith)
      rw [← h2]
      exact rgs_nClass_anti hσ hN0 hbig
  filter_upwards [hedge η' hη'0 hηρ hηδ, hT1, self_mem_nhdsWithin] with κ hE h1 hκ0
  obtain ⟨l', hreg', hval', hpar, hf2, hclass⟩ := hE
  have hκ0' : 0 < κ := hκ0
  obtain ⟨hσκ, hS', τk, hdak⟩ := rgs_regS_facts (T := T) hN0 hκ0' hS
  have hval := abs_lt.mp hval'
  have h1' : |nClass N (specOf (regS κ (Tᵀ * T))) Eg - nClass N σ Eg| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using h1
  have hl'1 := hreg'.1
  have hl'2 := hreg'.2.1
  have hodd : ¬ Even l' := fun h => (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩) (hpar.mpr h)
  obtain ⟨k', hk'⟩ := Nat.not_even_iff_odd.mp hodd
  subst hk'
  refine ⟨2 * k' + 1, hreg', by omega, ?_, lt_of_lt_of_le hval' hηη, lt_of_lt_of_le hf2 hηη⟩
  rw [show (2 * k' + 1 + 1) / 2 - 1 = k' by omega]
  have hle : nClass N (specOf (regS κ (Tᵀ * T))) Eg ≤
      cumCount N (specOf (regS κ (Tᵀ * T))) k' := by
    have h := (nClass_edgeVal hdak (k := k' + 1) (by omega) (by omega)).1
    rw [show 2 * (k' + 1) - 1 = 2 * k' + 1 by omega, show k' + 1 - 1 = k' by omega] at h
    rw [← h]
    exact rgs_nClass_anti hσκ hN0 (by linarith)
  have hge : (cumCount N (specOf (regS κ (Tᵀ * T))) k' : ℝ) ≤
      nClass N (specOf (regS κ (Tᵀ * T))) Eg := by
    rcases Nat.eq_zero_or_pos k' with hk0 | hk0
    · subst hk0
      simpa [cumCount] using rgs_nClass_nonneg N (specOf (regS κ (Tᵀ * T))) Eg
    · -- the edge `2k'` above `l'`
      have hj := hclass (2 * k') (by omega) (by omega) (by omega)
      have hanti' := rgs_edgeVal_anti N (specOf (regS κ (Tᵀ * T))) hσκ hN0 hS' (i := 2 * k')
        (j := 2 * k' + 1) (by omega) (by omega) hl'2
      have hbig : Eg < edgeVal N (specOf (regS κ (Tᵀ * T))) (2 * k') := by
        rcases hj with hsmall | ⟨i, hi1, hi2, hil, hij⟩
        · exfalso
          linarith
        · have hij' := abs_lt.mp hij
          rcases rgs_gap_side hgap hi1 hi2 hil with hi | hi
          · linarith
          · linarith
      have hcnt := (nClass_edgeVal hdak (k := k') (by omega) (by omega)).2 (by linarith)
      rw [← hcnt]
      exact rgs_nClass_anti hσκ hN0 hbig.le
  apply le_antisymm
  · exact rgs_nat_le (by linarith [(abs_lt.mp h1').2])
  · exact rgs_nat_le (by linarith [(abs_lt.mp h1').1])

/-- The transfer at a lower edge `l = 2k`: for every `η > 0`, eventually in `κ ↓ 0`, a lower edge
`l'` of `Ŝ + κ P₀`, regular at `τ_e`, with `d'_{l̂'} = d_k`, `|a_{l'} - a_l| < η` and
`|f_κ''(x_{l'}) - f''(x_l)| < η`. -/
private lemma rgs_lower {τ τ₀ : ℝ} (hτ : 0 < τ) (hτ₀ : τ / 2 ≤ τ₀) {K : ℕ} (hN : 1 ≤ N)
    {T : Matrix (Fin M) (Fin K) ℝ} (hda : DensityAssumptions τ N (specOf (T * Tᵀ)))
    {k : ℕ} (hl : RegularEdge τ₀ N (specOf (T * Tᵀ)) (2 * k)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      l' % 2 = 0 ∧
      cumCount N (specOf (regS κ (Tᵀ * T))) ((l' + 1) / 2) = cumCount N (specOf (T * Tᵀ)) k ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) (2 * k)| < η ∧
      |fR2 N (specOf (regS κ (Tᵀ * T))) (xCrit N (specOf (regS κ (Tᵀ * T))) l') -
        fR2 N (specOf (T * Tᵀ)) (xCrit N (specOf (T * Tᵀ)) (2 * k))| < η := by
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := hda.nonneg
  have hN0 : 0 < N := hN
  obtain ⟨ρ, hρ, hedge⟩ := rgs_edge_part hτ hτ₀ hN hda hl
  obtain ⟨hl1, hl2, hal, hgap, -⟩ := hl
  have hk1 : 1 ≤ k := by omega
  have hkp : k ≤ numBands N σ := by omega
  have hS := rgs_posVals_nonempty N σ (by omega)
  have hτ₀0 : 0 < τ₀ := by linarith
  have hδa0 : 0 < deltaA τ :=
    lt_min (by have := edgeTau'_pos (tauE_pos hτ); positivity) (by positivity)
  set Eg := edgeVal N σ (2 * k) - τ₀ / 2 with hEg
  have hEg0 : 0 < Eg := by linarith
  set η' := min (min ρ (deltaA τ)) (min η (τ₀ / 4)) with hη'
  have hη'0 : 0 < η' := lt_min (lt_min hρ hδa0) (lt_min hη (by positivity))
  have hηρ : η' ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η' ≤ deltaA τ := (min_le_left _ _).trans (min_le_right _ _)
  have hηη : η' ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hητ : η' ≤ τ₀ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hT1 := (tendsto_nClass_regS hN T hEg0).eventually (Metric.ball_mem_nhds _ one_pos)
  have hnEg : (cumCount N σ k : ℝ) ≤ nClass N σ Eg := by
    have h1 := (nClass_edgeVal hda hk1 hkp).2 (by linarith)
    rw [← h1]
    exact rgs_nClass_anti hσ hN0 (by linarith)
  have hnEg' : nClass N σ Eg ≤ cumCount N σ k := by
    refine rgs_nClass_le hda hk1 hkp hEg0 ?_
    by_cases hlast : k = numBands N σ
    · left; exact hlast
    · right; left
      have hkp' : k < numBands N σ := lt_of_le_of_ne hkp hlast
      refine ⟨hkp', ?_⟩
      have hanti := rgs_edgeVal_anti N σ hσ hN0 hS (i := 2 * k) (j := 2 * k + 1) (by omega)
        (by omega) (by omega)
      rcases rgs_gap_side hgap (i := 2 * k + 1) (by omega) (by omega) (by omega) with h | h
      · linarith
      · linarith
  filter_upwards [hedge η' hη'0 hηρ hηδ, hT1, self_mem_nhdsWithin] with κ hE h1 hκ0
  obtain ⟨l', hreg', hval', hpar, hf2, hclass⟩ := hE
  have hκ0' : 0 < κ := hκ0
  obtain ⟨hσκ, hS', τk, hdak⟩ := rgs_regS_facts (T := T) hN0 hκ0' hS
  have hval := abs_lt.mp hval'
  have h1' : |nClass N (specOf (regS κ (Tᵀ * T))) Eg - nClass N σ Eg| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using h1
  have hl'1 := hreg'.1
  have hl'2 := hreg'.2.1
  have hev : Even l' := hpar.mp ⟨k, by ring⟩
  obtain ⟨k', hk'⟩ := hev
  rw [show k' + k' = 2 * k' by ring] at hk'
  subst hk'
  refine ⟨2 * k', hreg', by omega, ?_, lt_of_lt_of_le hval' hηη, lt_of_lt_of_le hf2 hηη⟩
  rw [show (2 * k' + 1) / 2 = k' by omega]
  have hle : nClass N (specOf (regS κ (Tᵀ * T))) Eg ≤
      cumCount N (specOf (regS κ (Tᵀ * T))) k' := by
    refine rgs_nClass_le hdak (by omega) (by omega) hEg0 ?_
    by_cases hlast : k' = numBands N (specOf (regS κ (Tᵀ * T)))
    · left; exact hlast
    · right; left
      have hk'p : k' < numBands N (specOf (regS κ (Tᵀ * T))) := by omega
      refine ⟨hk'p, ?_⟩
      have hp' : 2 * k' + 1 ≤ 2 * numBands N (specOf (regS κ (Tᵀ * T))) := by omega
      have hj := hclass (2 * k' + 1) (by omega) hp' (by omega)
      have hanti' := rgs_edgeVal_anti N (specOf (regS κ (Tᵀ * T))) hσκ hN0 hS'
        (i := 2 * k') (j := 2 * k' + 1) (by omega) (by omega) hp'
      rcases hj with hsmall | ⟨i, hi1, hi2, hil, hij⟩
      · linarith
      · have hij' := abs_lt.mp hij
        rcases rgs_gap_side hgap hi1 hi2 hil with hi | hi
        · exfalso
          linarith
        · linarith
  have hge : (cumCount N (specOf (regS κ (Tᵀ * T))) k' : ℝ) ≤
      nClass N (specOf (regS κ (Tᵀ * T))) Eg := by
    have hcnt := (nClass_edgeVal hdak (k := k') (by omega) (by omega)).2 (by linarith)
    rw [← hcnt]
    exact rgs_nClass_anti hσκ hN0 (by linarith)
  apply le_antisymm
  · exact rgs_nat_le (by linarith [(abs_lt.mp h1').2])
  · exact rgs_nat_le (by linarith [(abs_lt.mp h1').1])

/-- `t ↦ (|t|/2)^{1/3}`, the map `f''(x_k) ↦ ϖ_k`, is continuous. -/
private lemma rgs_scale_continuous : Continuous fun t : ℝ => (|t| / 2) ^ (1 / 3 : ℝ) :=
  (Real.continuous_rpow_const (by norm_num)).comp (continuous_abs.div_const 2)

/-- For `Ŝ + κ P₀`, `κ ↓ 0`: a regular edge `k` of `T Tᵀ` is followed by regular edges `l'` of
`Ŝ + κ P₀` of the same parity, with the same eigenvalue indices and converging `a`, `ϖ`. -/
theorem regS_edge_transfer {τ : ℝ} (hτ : 0 < τ) {K : ℕ} (hN : 1 ≤ N)
    {T : Matrix (Fin M) (Fin K) ℝ} (hda : DensityAssumptions τ N (specOf (T * Tᵀ)))
    (hK : (K : ℝ) / N ≤ τ⁻¹) {k : ℕ} (hk : RegularEdge τ N (specOf (T * Tᵀ)) k) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      edgeSign l' = edgeSign k ∧
      (∀ i, edgeIdx N (specOf (regS κ (Tᵀ * T))) l' i = edgeIdx N (specOf (T * Tᵀ)) k i) ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) k| ≤ δ ∧
      |edgeScale N (specOf (regS κ (Tᵀ * T))) l' - edgeScale N (specOf (T * Tᵀ)) k| ≤ δ := by
  have _ := hK
  obtain ⟨θ, hθ, hθ'⟩ := Metric.continuousAt_iff.mp
    (rgs_scale_continuous.continuousAt (x := fR2 N (specOf (T * Tᵀ)) (xCrit N (specOf (T * Tᵀ)) k)))
    δ hδ
  have hη : 0 < min δ θ := lt_min hδ hθ
  have key : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      edgeSign l' = edgeSign k ∧
      (∀ i, edgeIdx N (specOf (regS κ (Tᵀ * T))) l' i = edgeIdx N (specOf (T * Tᵀ)) k i) ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) k| < min δ θ ∧
      |fR2 N (specOf (regS κ (Tᵀ * T))) (xCrit N (specOf (regS κ (Tᵀ * T))) l') -
        fR2 N (specOf (T * Tᵀ)) (xCrit N (specOf (T * Tᵀ)) k)| < min δ θ := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j by ring] at hj
      subst hj
      filter_upwards [rgs_lower hτ (by linarith) hN hda hk hη] with κ hκ
      obtain ⟨l', hreg, hpar, hcnt, hval, hf2⟩ := hκ
      refine ⟨l', hreg, ?_, fun i => ?_, hval, hf2⟩
      · unfold edgeSign
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · unfold edgeIdx
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hcnt,
          show (2 * j + 1) / 2 = j by omega]
    · subst hj
      filter_upwards [rgs_upper hτ (by linarith) hN hda hk hη] with κ hκ
      obtain ⟨l', hreg, hpar, hcnt, hval, hf2⟩ := hκ
      refine ⟨l', hreg, ?_, fun i => ?_, hval, hf2⟩
      · unfold edgeSign
        rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      · unfold edgeIdx
        rw [ite_eq_left (by omega), ite_eq_left (by omega), hcnt,
          show (2 * j + 1 + 1) / 2 - 1 = j by omega]
  filter_upwards [key] with κ hκ
  obtain ⟨l', hreg, hsgn, hidx, hval, hf2⟩ := hκ
  refine ⟨l', hreg, hsgn, hidx, (lt_of_lt_of_le hval (min_le_left _ _)).le, ?_⟩
  have h := hθ' (x := fR2 N (specOf (regS κ (Tᵀ * T))) (xCrit N (specOf (regS κ (Tᵀ * T))) l'))
    (by rw [Real.dist_eq]; exact lt_of_lt_of_le hf2 (min_le_right _ _))
  rw [Real.dist_eq] at h
  exact h.le
/-! ## Instance: `T = (1 0)`, `Σ = T Tᵀ = (1)`, `Tᵀ T = diag(1, 0)`, `N = 2`

Marchenko–Pastur at `φ = 1/2`: `f(x) = -1/x + 1/(2(1 + x))`, `x_1 = √2 - 2`, `a_1 = 3/2 + √2`,
`a_2 = 3/2 - √2`; the edge `a_1` is regular at `τ = 1/5`, and `Tᵀ T` has a kernel, so
`Ŝ + κ P₀ = diag(1, κ)` adds the atom `κ` of weight `1/2`. -/

/-- `T = (1 0)`. -/
local notation "rgs_T" => (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)


#print axioms Anisotropic.regS_spectrum
#print axioms Anisotropic.regS_norm_sub_le
#print axioms Anisotropic.regS_edge_transfer

end Anisotropic
