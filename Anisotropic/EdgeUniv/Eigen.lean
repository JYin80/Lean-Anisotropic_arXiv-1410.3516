module

public import Anisotropic.Density.Critical
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.Framework.Domination
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.MinMax

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lipschitz continuity of the ordered eigenvalues, measurability of `q_{k,l}`, and the mirror relation -/

/-- One side of Weyl's inequality: `λ_i(A) ≤ λ_i(B) + ‖A - B‖`. -/
private lemma sortedEig_le_add_norm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : ℕ) : sortedEig A i ≤ sortedEig B i + ‖A - B‖ := by
  by_cases hj : 1 ≤ i ∧ i ≤ n
  · have h1 : sortedEig A i - ‖A - B‖ ≤ sortedEig B i := by
      rw [sortedEig_ge_iff hB hj.1 hj.2]
      have hw := eigCount_weyl hA hB le_rfl (sortedEig A i - ‖A - B‖)
      rw [sub_add_cancel] at hw
      exact le_trans ((sortedEig_ge_iff hA hj.1 hj.2 _).1 le_rfl) hw
    linarith
  · have hA0 : sortedEig A i = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    have hB0 : sortedEig B i = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    rw [hA0, hB0]
    simp

/-- Weyl: sorted eigenvalues are `1`-Lipschitz in the operator norm. -/
theorem sortedEig_lipschitz {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : ℕ) : |sortedEig A i - sortedEig B i| ≤ ‖A - B‖ := by
  rw [abs_le]
  have h1 := sortedEig_le_add_norm hA hB i
  have h2 := sortedEig_le_add_norm hB hA i
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- `sortedEig · i` is measurable. -/
private lemma measurable_sortedEig (n i : ℕ) :
    Measurable fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i := by
  set H : Set (Matrix (Fin n) (Fin n) ℝ) := {A | A.IsHermitian} with hH
  have hHc : IsClosed H := by
    have : H = {A | Aᴴ = A} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have hpw : (fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i) =
      H.piecewise (fun A => sortedEig A i) (fun _ => 0) := by
    funext A
    by_cases hA : A ∈ H
    · rw [Set.piecewise_eq_of_mem _ _ _ hA]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hA]
      unfold sortedEig
      rw [dite_eq_right_iff]
      exact fun h => absurd h.1 hA
  rw [hpw]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hHc.measurableSet
  have hl : LipschitzOnWith 1 (fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i) H := by
    refine LipschitzOnWith.of_dist_le_mul fun A hA B hB => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact sortedEig_lipschitz hA hB i
  exact hl.continuousOn

/-- `A ↦ q_{k,l}(A)` is measurable. -/
theorem measurable_qVecA (N : ℕ) (σ : Fin M → ℝ) (n k l : ℕ) :
    Measurable fun A : Matrix (Fin n) (Fin n) ℝ => qVecA N σ A k l := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold qVecA
  exact measurable_const.mul (((measurable_sortedEig n _)).sub measurable_const)

/-- The characteristic polynomial of `-A` for Hermitian `A`. -/
private lemma charpoly_neg_herm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (-A).charpoly = ∏ i, (Polynomial.X - Polynomial.C (-hA.eigenvalues i)) := by
  have h := hA.spectral_theorem
  have h2 : -A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal fun i => -hA.eigenvalues i) := by
    conv_lhs => rw [h]
    rw [← map_neg, ← diagonal_neg]
    congr 2
  rw [h2, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/-- The eigenvalue multiset of `-A` is the negative of that of `A`, in the `eigenvalues₀`
indexing. -/
private lemma eigenvalues₀_neg_multiset {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    Multiset.map hA.neg.eigenvalues₀ Finset.univ.val =
      Multiset.map (fun i => -hA.eigenvalues₀ i) Finset.univ.val := by
  have h1 := hA.neg.roots_charpoly_eq_eigenvalues₀
  have h2 := hA.roots_charpoly_eq_eigenvalues₀
  have h3 : (-A).charpoly.roots = A.charpoly.roots.map fun x => -x := by
    rw [charpoly_neg_herm hA, hA.roots_charpoly_eq_eigenvalues, Polynomial.roots_prod]
    · simp
      exact List.Perm.refl _
    · rw [Finset.prod_ne_zero_iff]
      intro a _
      simpa [sub_eq_add_neg] using Polynomial.X_sub_C_ne_zero (-hA.eigenvalues a)
  have h4 := h1.symm.trans (h3.trans (congrArg (Multiset.map fun x => -x) h2))
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp, Multiset.map_map] at h4
  simpa [Function.comp_def] using h4

/-- Reflection of the ordered eigenvalues: `λ_j(-A) = -λ_{n+1-j}(A)` for `1 ≤ j ≤ n`. -/
private lemma sortedEig_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ n) : sortedEig (-A) j = -sortedEig A (n + 1 - j) := by
  set m := Fintype.card (Fin n) with hm
  have hm' : m = n := Fintype.card_fin n
  set f : Fin m → ℝ := hA.eigenvalues₀ with hf
  set g : Fin m → ℝ := hA.neg.eigenvalues₀ with hg
  set h : Fin m → ℝ := fun i => -f (Fin.rev i) with hh
  have hmul : Multiset.map g Finset.univ.val = Multiset.map h Finset.univ.val := by
    have h1 := eigenvalues₀_neg_multiset hA
    have h2 : Multiset.map h Finset.univ.val =
        Multiset.map (fun i => -f i) Finset.univ.val := by
      have : Multiset.map (fun i => -f i) (Multiset.map Fin.revPerm Finset.univ.val) =
          Multiset.map (fun i => -f i) Finset.univ.val := by
        rw [Multiset.map_univ_val_equiv]
      rw [← this, Multiset.map_map]
      rfl
    rw [h2]; exact h1
  have hgl : (List.ofFn g).SortedGE := hA.neg.eigenvalues₀_antitone.sortedGE_ofFn
  have hhl : (List.ofFn h).SortedGE := by
    refine Antitone.sortedGE_ofFn fun a b hab => ?_
    have : f (Fin.rev a) ≤ f (Fin.rev b) := hA.eigenvalues₀_antitone (Fin.rev_le_rev.2 hab)
    simp only [hh]
    linarith
  have hperm : (List.ofFn g).Perm (List.ofFn h) := by
    have := hmul
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at this
    exact this
  have heq := List.ofFn_inj.1 (hperm.eq_of_sortedGE hgl hhl)
  have hcond : (-A).IsHermitian ∧ 1 ≤ j ∧ j ≤ Fintype.card (Fin n) :=
    ⟨hA.neg, hj, by rw [Fintype.card_fin]; exact hjn⟩
  have hcond' : A.IsHermitian ∧ 1 ≤ n + 1 - j ∧ n + 1 - j ≤ Fintype.card (Fin n) :=
    ⟨hA, by omega, by rw [Fintype.card_fin]; omega⟩
  have e1 : sortedEig (-A) j = g ⟨j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond)]
  have e2 : sortedEig A (n + 1 - j) = f ⟨n + 1 - j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond')]
  rw [e1, e2, show g ⟨j - 1, by omega⟩ = h ⟨j - 1, by omega⟩ from congrFun heq _]
  simp only [hh]
  congr 2
  ext
  simp only [Fin.val_rev]
  omega

/-- The mirror relation: `q_{k,l}` is the upper-edge vector of `(-1)^{k+1} A` at
`(-1)^{k+1} a_k` with `edgeD` eigenvalues beyond the edge. -/
theorem qVecA_eq_edgeQ {N : ℕ} {σ : Fin M → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {k l : ℕ}
    (hl : cumCount N σ ((k + 1) / 2 - 1) + l ≤ cumCount N σ ((k + 1) / 2))
    (hd : cumCount N σ ((k + 1) / 2) ≤ N) :
    qVecA N σ A k l = edgeQ N (edgeSign k * edgeVal N σ k) (edgeScale N σ k) (edgeD N σ k) l
      (edgeSign k • A) := by
  funext i
  unfold qVecA edgeQ
  by_cases hk : k % 2 = 1
  · have hs : edgeSign k = 1 := by simp [edgeSign, hk]
    have hi : edgeIdx N σ k ((i : ℕ) + 1) = edgeD N σ k + ((i : ℕ) + 1) := by
      simp [edgeIdx, edgeD, hk]
    rw [hs, hi]
    simp
  · have hs : edgeSign k = -1 := by simp [edgeSign, hk]
    have hil : (i : ℕ) < l := i.2
    have hi : edgeIdx N σ k ((i : ℕ) + 1) = cumCount N σ ((k + 1) / 2) + 1 - ((i : ℕ) + 1) := by
      simp [edgeIdx, hk]
    have hdd : edgeD N σ k = N - cumCount N σ ((k + 1) / 2) := by simp [edgeD, hk]
    have hr := sortedEig_neg hA (j := N - cumCount N σ ((k + 1) / 2) + ((i : ℕ) + 1))
      (by omega) (by omega)
    rw [hs, hi, hdd, neg_one_smul, hr, show N + 1 - (N - cumCount N σ ((k + 1) / 2) + ((i : ℕ) + 1))
      = cumCount N σ ((k + 1) / 2) + 1 - ((i : ℕ) + 1) by omega]
    ring

/-- Weyl's inequality for `diag(1, 2)` and `diag(1, 3)` at the second eigenvalue, where it is
sharp: `|2 - 3| = 1 = ‖diag(0, -1)‖`. -/
example : |sortedEig (diagonal ![(1 : ℝ), 2]) 2 - sortedEig (diagonal ![(1 : ℝ), 3]) 2| ≤
    ‖(diagonal ![(1 : ℝ), 2] : Matrix (Fin 2) (Fin 2) ℝ) - diagonal ![(1 : ℝ), 3]‖ :=
  sortedEig_lipschitz (Matrix.isHermitian_diagonal _) (Matrix.isHermitian_diagonal _) 2

end Anisotropic
