import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Gaussian.Spectral
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.MinMax
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.GOE
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistent

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Symmetries: orthogonal invariance of the GOE and the reflection `(W, A) ↦ (−W, −A)` -/

/-- Conjugation `X ↦ O X Oᵀ` is measurable. -/
private lemma aux_measurable_conj {N : ℕ} (O : Matrix (Fin N) (Fin N) ℝ) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => O * X * Oᵀ := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (Finset.measurable_sum _ fun l _ =>
    (measurable_id.eval_matrix (i := l) (j := k)).const_mul _).mul_const _

/-- The GOE matrix is a measurable function on `GOESpace N`. -/
private lemma aux_measurable_goeW (N : ℕ) : Measurable (goeW N) :=
  Matrix.measurable_iff.2 (isGOE_goeW N).measurable

/-- Translation `X ↦ X + B` is measurable. -/
private lemma aux_measurable_add_const {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => X + B := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.add_apply]
  exact (measurable_id.eval_matrix (i := i) (j := j)).add_const _

/-- Reindexing the rows and columns of a matrix is measurable. -/
private lemma aux_measurable_submatrix {N : ℕ} (σ τ : Fin N → Fin N) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => X.submatrix σ τ :=
  Matrix.measurable_iff.2 fun i j => measurable_id.eval_matrix (i := σ i) (j := τ j)

/-- Negation of a matrix is measurable. -/
private lemma aux_measurable_neg (N : ℕ) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => -X :=
  Matrix.measurable_iff.2 fun i j => (measurable_id.eval_matrix (i := i) (j := j)).neg

/-- The law of the GOE matrix is invariant under negation. -/
private lemma aux_map_neg (N : ℕ) :
    Measure.map (fun X : Matrix (Fin N) (Fin N) ℝ => -X) (Measure.map (goeW N) ℙ) =
      Measure.map (goeW N) ℙ := by
  set neg : GOESpace N → GOESpace N := fun ω p => -ω p with hneg
  have hnegm : Measurable neg := measurable_pi_iff.2 fun p => (measurable_pi_apply p).neg
  have hmap : Measure.map neg (ℙ : Measure (GOESpace N)) = ℙ := by
    change Measure.map (fun (x : Fin N × Fin N → ℝ) p => (fun _ y => -y) p (x p))
      (Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)) = _
    rw [Measure.pi_map_pi fun _ => measurable_neg.aemeasurable]
    change Measure.pi _ = Measure.pi _
    congr 1
    funext p
    rw [gaussianReal_map_neg, neg_zero]
  have hpt : (fun X : Matrix (Fin N) (Fin N) ℝ => -X) ∘ goeW N = goeW N ∘ neg := by
    funext ω
    ext i j
    rfl
  rw [Measure.map_map (aux_measurable_neg N) (aux_measurable_goeW N), hpt,
    ← Measure.map_map (aux_measurable_goeW N) hnegm, hmap]

/-- For a measurable `Φ` invariant under orthogonal conjugation of symmetric matrices,
`E Φ(W^Gauss + A) = E Φ(W^Gauss + D)`, `D = diag(spec A)`. -/
theorem integral_goe_add_conj {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {Φ : Matrix (Fin N) (Fin N) ℝ → ℝ} (hΦ : Measurable Φ)
    (hinv : ∀ O : Matrix (Fin N) (Fin N) ℝ, O ∈ Matrix.orthogonalGroup (Fin N) ℝ →
      ∀ X : Matrix (Fin N) (Fin N) ℝ, X.IsHermitian → Φ (O * X * Oᵀ) = Φ X) :
    (∫ ω, Φ (goeW N ω + A)) = ∫ ω, Φ (goeW N ω + diagonal (specOf A)) := by
  obtain ⟨U, hU, hUA⟩ := exists_orth_diag hA
  set D : Matrix (Fin N) (Fin N) ℝ := diagonal (specOf A) with hD
  have hU1 : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have hU2 : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  have hUt : Uᵀ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa using hU1
  have hAD : A = U * D * Uᵀ := by
    rw [← hUA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2,
      Matrix.mul_one]
  have hDh : D.IsHermitian := Matrix.isHermitian_diagonal _
  -- the integrand
  have hpt : ∀ ω, Φ (goeW N ω + A) = Φ (Uᵀ * goeW N ω * Uᵀᵀ + D) := by
    intro ω
    have hS : (goeW N ω)ᵀ = goeW N ω := (isGOE_goeW N).symm ω
    have hXh : (Uᵀ * goeW N ω * Uᵀᵀ + D).IsHermitian := by
      refine Matrix.IsHermitian.add ?_ hDh
      have := Matrix.isHermitian_conjTranspose_mul_mul U
        (show (goeW N ω).IsHermitian by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS)
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have := hinv U hU _ hXh
    rw [← this]
    congr 1
    rw [hAD, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.transpose_transpose]
    rw [show U * (Uᵀ * goeW N ω * U) * Uᵀ = (U * Uᵀ) * goeW N ω * (U * Uᵀ) by
      simp only [Matrix.mul_assoc], hU2]
    simp [Matrix.mul_assoc]
  simp_rw [hpt]
  have hF : Measurable fun X : Matrix (Fin N) (Fin N) ℝ => Φ (X + D) :=
    hΦ.comp (aux_measurable_add_const D)
  have hf : Measurable fun ω => Uᵀ * goeW N ω * Uᵀᵀ :=
    (aux_measurable_conj Uᵀ).comp (aux_measurable_goeW N)
  have hm := (isGOE_goeW N).map_conj hUt
  calc (∫ ω, Φ (Uᵀ * goeW N ω * Uᵀᵀ + D))
      = ∫ y, Φ (y + D) ∂(Measure.map (fun ω => Uᵀ * goeW N ω * Uᵀᵀ) ℙ) := by
        rw [integral_map hf.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ y, Φ (y + D) ∂(Measure.map (goeW N) ℙ) := by rw [hm]
    _ = _ := by rw [integral_map (aux_measurable_goeW N).aemeasurable hF.aestronglyMeasurable]

/-- `-W^Gauss` has the law of `W^Gauss`. -/
theorem integral_goe_neg {N : ℕ} {Φ : Matrix (Fin N) (Fin N) ℝ → ℝ} (hΦ : Measurable Φ)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    (∫ ω, Φ (-goeW N ω + B)) = ∫ ω, Φ (goeW N ω + B) := by
  have hF : Measurable fun X : Matrix (Fin N) (Fin N) ℝ => Φ (X + B) :=
    hΦ.comp (aux_measurable_add_const B)
  have hF' : Measurable fun X : Matrix (Fin N) (Fin N) ℝ => Φ (-X + B) :=
    hF.comp (aux_measurable_neg N)
  calc (∫ ω, Φ (-goeW N ω + B))
      = ∫ X, Φ (-X + B) ∂(Measure.map (goeW N) ℙ) := by
        rw [integral_map (aux_measurable_goeW N).aemeasurable hF'.aestronglyMeasurable]
    _ = ∫ Y, Φ (Y + B) ∂(Measure.map (fun X : Matrix (Fin N) (Fin N) ℝ => -X)
          (Measure.map (goeW N) ℙ)) := by
        rw [integral_map (aux_measurable_neg N).aemeasurable hF.aestronglyMeasurable]
    _ = ∫ Y, Φ (Y + B) ∂(Measure.map (goeW N) ℙ) := by rw [aux_map_neg]
    _ = _ := by rw [integral_map (aux_measurable_goeW N).aemeasurable hF.aestronglyMeasurable]

/-- Orthogonal conjugation preserves symmetry. -/
private lemma aux_isHermitian_conj {n : ℕ} {O : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) : (O * X * Oᵀ).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Oᵀ hX
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- The ordered eigenvalues are invariant under orthogonal conjugation. -/
theorem sortedEig_conj {n : ℕ} {O : Matrix (Fin n) (Fin n) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) (i : ℕ) : sortedEig (O * X * Oᵀ) i = sortedEig X i := by
  have hY := aux_isHermitian_conj (O := O) hX
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · have hE : ∀ E, eigCount (O * X * Oᵀ) E = eigCount X E := by
      intro E
      unfold eigCount
      rw [specOf_conj hO]
    refine le_antisymm ?_ ?_
    · rw [sortedEig_ge_iff hX hi.1 hi.2, ← hE]
      exact (sortedEig_ge_iff hY hi.1 hi.2 _).1 le_rfl
    · rw [sortedEig_ge_iff hY hi.1 hi.2, hE]
      exact (sortedEig_ge_iff hX hi.1 hi.2 _).1 le_rfl
  · have h0 : ∀ Z : Matrix (Fin n) (Fin n) ℝ, sortedEig Z i = 0 := by
      intro Z
      unfold sortedEig
      rw [dite_eq_right_iff]
      rintro ⟨-, h1, h2⟩
      exact absurd ⟨h1, by simpa using h2⟩ hi
    rw [h0, h0]

/-- The characteristic polynomial of `-A` for Hermitian `A`. -/
private lemma aux_charpoly_neg_herm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
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
private lemma aux_eigenvalues₀_neg_multiset {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    Multiset.map hA.neg.eigenvalues₀ Finset.univ.val =
      Multiset.map (fun i => -hA.eigenvalues₀ i) Finset.univ.val := by
  have h1 := hA.neg.roots_charpoly_eq_eigenvalues₀
  have h2 := hA.roots_charpoly_eq_eigenvalues₀
  have h3 : (-A).charpoly.roots = A.charpoly.roots.map fun x => -x := by
    rw [aux_charpoly_neg_herm hA, hA.roots_charpoly_eq_eigenvalues, Polynomial.roots_prod]
    · simp only [map_neg, sub_neg_eq_add, Polynomial.roots_X_add_C, Multiset.bind_singleton,
        Fin.univ_val_map, RCLike.ofReal_real_eq_id, Function.comp_apply, id_eq, Multiset.map_coe,
        List.map_ofFn, Multiset.coe_eq_coe]
      exact List.Perm.refl _
    · rw [Finset.prod_ne_zero_iff]
      intro a _
      simpa [sub_eq_add_neg] using Polynomial.X_sub_C_ne_zero (-hA.eigenvalues a)
  have h4 := h1.symm.trans (h3.trans (congrArg (Multiset.map fun x => -x) h2))
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp, Multiset.map_map] at h4
  simpa [Function.comp_def] using h4

/-- Reflection of the ordered eigenvalues: `λ_j(-X) = -λ_{n+1-j}(X)` for `1 ≤ j ≤ n`. -/
theorem sortedEig_neg' {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ n) : sortedEig (-X) j = -sortedEig X (n + 1 - j) := by
  set m := Fintype.card (Fin n) with hm
  have hm' : m = n := Fintype.card_fin n
  set f : Fin m → ℝ := hX.eigenvalues₀ with hf
  set g : Fin m → ℝ := hX.neg.eigenvalues₀ with hg
  set h : Fin m → ℝ := fun i => -f (Fin.rev i) with hh
  have hmul : Multiset.map g Finset.univ.val = Multiset.map h Finset.univ.val := by
    have h1 := aux_eigenvalues₀_neg_multiset hX
    have h2 : Multiset.map h Finset.univ.val =
        Multiset.map (fun i => -f i) Finset.univ.val := by
      have : Multiset.map (fun i => -f i) (Multiset.map Fin.revPerm Finset.univ.val) =
          Multiset.map (fun i => -f i) Finset.univ.val := by
        rw [Multiset.map_univ_val_equiv]
      rw [← this, Multiset.map_map]
      rfl
    rw [h2]; exact h1
  have hgl : (List.ofFn g).SortedGE := hX.neg.eigenvalues₀_antitone.sortedGE_ofFn
  have hhl : (List.ofFn h).SortedGE := by
    refine Antitone.sortedGE_ofFn fun a b hab => ?_
    have : f (Fin.rev a) ≤ f (Fin.rev b) := hX.eigenvalues₀_antitone (Fin.rev_le_rev.2 hab)
    simp only [hh]
    linarith
  have hperm : (List.ofFn g).Perm (List.ofFn h) := by
    have := hmul
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at this
    exact this
  have heq := List.ofFn_inj.1 (hperm.eq_of_sortedGE hgl hhl)
  have hcond : (-X).IsHermitian ∧ 1 ≤ j ∧ j ≤ Fintype.card (Fin n) :=
    ⟨hX.neg, hj, by rw [Fintype.card_fin]; exact hjn⟩
  have hcond' : X.IsHermitian ∧ 1 ≤ n + 1 - j ∧ n + 1 - j ≤ Fintype.card (Fin n) :=
    ⟨hX, by omega, by rw [Fintype.card_fin]; omega⟩
  have e1 : sortedEig (-X) j = g ⟨j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond)]
  have e2 : sortedEig X (n + 1 - j) = f ⟨n + 1 - j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond')]
  rw [e1, e2, show g ⟨j - 1, by omega⟩ = h ⟨j - 1, by omega⟩ from congrFun heq _]
  simp only [hh]
  congr 2
  ext
  simp only [Fin.val_rev]
  omega

/-- One side of Weyl's inequality: `λ_i(A) ≤ λ_i(B) + ‖A - B‖`. -/
private lemma aux_sortedEig_le_add_norm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : ℕ) :
    sortedEig A i ≤ sortedEig B i + ‖A - B‖ := by
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
private lemma aux_sortedEig_lipschitz {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : ℕ) : |sortedEig A i - sortedEig B i| ≤ ‖A - B‖ := by
  rw [abs_le]
  have h1 := aux_sortedEig_le_add_norm hA hB i
  have h2 := aux_sortedEig_le_add_norm hB hA i
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- `sortedEig · i` is measurable. -/
theorem measurable_sortedEig' (n i : ℕ) :
    Measurable fun X : Matrix (Fin n) (Fin n) ℝ => sortedEig X i := by
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
    exact aux_sortedEig_lipschitz hA hB i
  exact hl.continuousOn

/-- `-W` lies in the class of entry laws with `W`. -/
theorem WigClassEntries.neg {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (h : WigClassEntries C N W) :
    WigClassEntries C N (fun ω => -W ω) := by
  exact
    { measurable := fun i j => (h.measurable i j).neg
      symm := fun ω => by rw [Matrix.transpose_neg, h.symm]
      indep := by
        have := h.indep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
        simpa [Function.comp_def] using this
      mean := fun i j => by simp [integral_neg, h.mean]
      var_off := fun i j hij => by simpa using h.var_off i j hij
      var_diag_ge := fun i => by simpa using h.var_diag_ge i
      var_diag_le := fun i => by simpa using h.var_diag_le i
      integrable_moment := fun p i j => by simpa [abs_mul] using h.integrable_moment p i j
      moment := fun p i j => by simpa [abs_mul] using h.moment p i j }

/-- The eigenvalue list of `-A` is the negative of that of `A`, up to a permutation. -/
private lemma aux_specOf_neg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ e : Equiv.Perm (Fin N), specOf (-A) = (-specOf A) ∘ e := by
  obtain ⟨U, hU, hUA⟩ := exists_orth_diag hA
  have hUt : Uᵀ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa using (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h1 := specOf_conj hUt (-A)
  have hd : (-diagonal (specOf A) : Matrix (Fin N) (Fin N) ℝ) = diagonal (-specOf A) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, hUA, hd] at h1
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal (-specOf A)
  exact ⟨e, by rw [← h1, he]⟩

/-- Reflection of the edges: `L₊(spec(-A)) = -L₋(spec A)` and `L₋(spec(-A)) = -L₊(spec A)`. -/
theorem LpW_specOf_neg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    LpW (specOf (-A)) = -LmW (specOf A) ∧ LmW (specOf (-A)) = -LpW (specOf A) := by
  obtain ⟨e, he⟩ := aux_specOf_neg hA
  rw [he, LpW_comp_perm, LmW_comp_perm, LmW_neg (specOf A), LmW_neg (-specOf A), neg_neg, neg_neg]
  exact ⟨rfl, rfl⟩

/-- The reflection `z ↦ -conj z` maps `domW τ N` to itself. -/
private lemma aux_domW_reflect {τ : ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ domW τ N) :
    -(starRingEnd ℂ) z ∈ domW τ N := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ‹_›

/-- The standing bound on `𝐃^W(τ, N)` passes to `-A` (`m^W_{-a}(-z̄) = -conj m^W_a(z)`). -/
theorem standingBoundW_specOf_neg {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (h : StandingBoundW τ (specOf A) (domW τ N)) :
    StandingBoundW τ (specOf (-A)) (domW τ N) := by
  obtain ⟨e, he⟩ := aux_specOf_neg hA
  intro z hz i
  have hwD := aux_domW_reflect hz
  set w : ℂ := -(starRingEnd ℂ) z with hw
  have hwz : z = -(starRingEnd ℂ) w := by simp [hw]
  have hm : mW (-specOf A) z = -(starRingEnd ℂ) (mW (specOf A) w) := by
    rw [hwz]
    exact mW_neg hN _ hwD.1
  have key := h w hwD (e i)
  rw [he, mW_comp_perm, hm]
  have e1 : -(-(starRingEnd ℂ) (mW (specOf A) w)) + (((-specOf A) ∘ e) i : ℂ) - z =
      -(starRingEnd ℂ) (-(mW (specOf A) w) + (specOf A (e i) : ℂ) - w) := by
    simp only [Function.comp_apply, Pi.neg_apply, Complex.ofReal_neg, map_add, map_sub, map_neg,
      Complex.conj_ofReal, hw, Complex.conj_conj]
    ring
  rw [e1, norm_neg, Complex.norm_conj]
  exact key

/-- The inverse of the negative of a matrix. -/
private lemma aux_inv_neg {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) :
    (-B)⁻¹ = -B⁻¹ := by
  by_cases h : IsUnit B.det
  · refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    exact Matrix.mul_nonsing_inv B h
  · have h' : ¬ IsUnit (-B).det := by
      rw [isUnit_iff_ne_zero, Matrix.det_neg]
      rw [isUnit_iff_ne_zero] at h
      simpa using h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

/-- The inverse commutes with entrywise complex conjugation. -/
private lemma aux_inv_conj {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (M.map (starRingEnd ℂ))⁻¹ = M⁻¹.map (starRingEnd ℂ) := by
  rw [Matrix.inv_def, Matrix.inv_def]
  ext i j
  have h1 := RingHom.map_det (starRingEnd ℂ) M
  have h2 := congrFun (congrFun (RingHom.map_adjugate (starRingEnd ℂ) M) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1 h2
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Ring.inverse_eq_inv', map_mul,
    map_inv₀]
  rw [h2, h1]

/-- Reflection of the resolvent: for the matrix `-D` with rows and columns reindexed by `e`, `G^W`
at `z` is the reindexing by `e` of `-conj G^W(-conj z)`, where `G^W` is taken for `D` and for the
matrix `-X` with rows and columns reindexed by `e⁻¹`. -/
private lemma aux_GW_neg {N : ℕ} (D X : Matrix (Fin N) (Fin N) ℝ) (e : Equiv.Perm (Fin N))
    (z : ℂ) :
    GW ((-D).submatrix e e) X z =
      (-((GW D (-(X.submatrix e.symm e.symm)) (-(starRingEnd ℂ) z)).map (starRingEnd ℂ))).submatrix
        e e := by
  unfold GW
  set M : Matrix (Fin N) (Fin N) ℂ := cplx (-(X.submatrix e.symm e.symm) + D) with hM
  have h1 : cplx (X + (-D).submatrix e e) - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (-(M + z • (1 : Matrix (Fin N) (Fin N) ℂ))).submatrix e e := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hM, cplx, Matrix.submatrix_apply]
      ring
    · have : e i ≠ e j := fun h => hij (e.injective h)
      simp [hM, cplx, Matrix.submatrix_apply, hij, this]
      ring
  have h2 : M + z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (M - (-(starRingEnd ℂ) z) • (1 : Matrix (Fin N) (Fin N) ℂ)).map (starRingEnd ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hM, cplx]
    · simp [hM, cplx, hij]
  rw [h1, Matrix.inv_submatrix_equiv, aux_inv_neg, h2, aux_inv_conj]

/-- Reflection of `Π^W`: for the matrix `-D` with rows and columns reindexed by `e`, and when the
solutions `m^W` correspond, `Π^W` at `z` is the reindexing by `e` of `-conj Π^W(-conj z)`, where
`Π^W` is taken for `D`. -/
private lemma aux_piW_neg {N : ℕ} (D : Matrix (Fin N) (Fin N) ℝ) (e : Equiv.Perm (Fin N))
    (z : ℂ)
    (hm : mW (specOf ((-D).submatrix e e)) z =
      -(starRingEnd ℂ) (mW (specOf D) (-(starRingEnd ℂ) z))) :
    piW ((-D).submatrix e e) z =
      (-((piW D (-(starRingEnd ℂ) z)).map (starRingEnd ℂ))).submatrix e e := by
  unfold piW
  rw [hm]
  set mw : ℂ := mW (specOf D) (-(starRingEnd ℂ) z) with hmw
  set Nm : Matrix (Fin N) (Fin N) ℂ :=
    cplx D - (mw + -(starRingEnd ℂ) z) • (1 : Matrix (Fin N) (Fin N) ℂ) with hNm
  have h1 : cplx ((-D).submatrix e e) -
      (-(starRingEnd ℂ) mw + z) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (-(Nm.map (starRingEnd ℂ))).submatrix e e := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hNm, cplx, Matrix.submatrix_apply]
      ring
    · have : e i ≠ e j := fun h => hij (e.injective h)
      simp [hNm, cplx, Matrix.submatrix_apply, hij, this]
  rw [h1, Matrix.inv_submatrix_equiv, aux_inv_neg, aux_inv_conj]

/-- The trace of the negative conjugate of a reindexed matrix. -/
private lemma aux_trace_refl {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (e : Equiv.Perm (Fin N)) :
    Matrix.trace ((-(G.map (starRingEnd ℂ))).submatrix e e) =
      -(starRingEnd ℂ) (Matrix.trace G) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply, Matrix.neg_apply,
    Matrix.map_apply, Finset.sum_neg_distrib, map_sum]
  rw [Equiv.sum_comp e (fun i => (starRingEnd ℂ) (G i i))]

/-- The permutation matrix of `σ` is orthogonal. -/
private lemma aux_perm_mem {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

/-- Conjugation by the permutation matrix of `σ` reindexes rows and columns by `σ`. -/
private lemma aux_perm_conj {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Matrix (Fin N) (Fin N) ℝ) :
    σ.permMatrix ℝ * M * (σ.permMatrix ℝ)ᵀ = M.submatrix σ σ := by
  rw [Matrix.transpose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix]
  rfl

/-- Reindexing a symmetric matrix by a permutation preserves its ordered eigenvalues. -/
private lemma aux_sortedEig_submatrix {N : ℕ} {Y : Matrix (Fin N) (Fin N) ℝ}
    (hY : Y.IsHermitian) (σ : Equiv.Perm (Fin N)) (i : ℕ) :
    sortedEig (Y.submatrix σ σ) i = sortedEig Y i := by
  rw [← aux_perm_conj]
  exact sortedEig_conj (aux_perm_mem σ) hY i

/-- The law of the GOE matrix is invariant under reindexing by a permutation. -/
private lemma aux_map_perm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Measure.map (fun X : Matrix (Fin N) (Fin N) ℝ => X.submatrix σ σ)
      (Measure.map (goeW N) ℙ) = Measure.map (goeW N) ℙ := by
  rw [Measure.map_map (aux_measurable_submatrix σ σ) (aux_measurable_goeW N)]
  have := (isGOE_goeW N).map_conj (aux_perm_mem σ)
  rw [← this]
  congr 1
  funext ω
  exact (aux_perm_conj σ (goeW N ω)).symm

/-- The map `X ↦ -X.submatrix e⁻¹ e⁻¹` preserves the law of the GOE matrix. -/
private lemma aux_map_R (N : ℕ) (e : Equiv.Perm (Fin N)) :
    Measure.map (fun X : Matrix (Fin N) (Fin N) ℝ => -(X.submatrix e.symm e.symm))
      (Measure.map (goeW N) ℙ) = Measure.map (goeW N) ℙ := by
  have h : (fun X : Matrix (Fin N) (Fin N) ℝ => -(X.submatrix e.symm e.symm)) =
      (fun X => -X) ∘ (fun X => X.submatrix e.symm e.symm) := rfl
  rw [h, ← Measure.map_map (aux_measurable_neg N) (aux_measurable_submatrix _ _),
    aux_map_perm N e.symm, aux_map_neg]

/-- A statement of stochastic domination for `f₂ (goeW N)` gives one for `f₁ (goeW N)` when
`f₁ = f₂ ∘ R` along the GOE and `R` preserves the law of the GOE. -/
private lemma aux_domAt_transfer {N : ℕ} {ε D c : ℝ}
    {R : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ} (hR : Measurable R)
    (hν : Measure.map R (Measure.map (goeW N) ℙ) = Measure.map (goeW N) ℙ)
    {f₁ f₂ : Matrix (Fin N) (Fin N) ℝ → ℝ} (hf₂ : Measurable f₂)
    (hf : ∀ ω, f₁ (goeW N ω) = f₂ (R (goeW N ω)))
    (h : DomAt N ε D (fun ω => f₂ (goeW N ω)) (fun _ => c)) :
    DomAt N ε D (fun ω => f₁ (goeW N ω)) (fun _ => c) := by
  unfold DomAt at h ⊢
  have hP : MeasurableSet {x : Matrix (Fin N) (Fin N) ℝ | (N : ℝ) ^ ε * c < f₂ x} :=
    measurableSet_lt measurable_const hf₂
  have e1 : {ω | (N : ℝ) ^ ε * c < f₁ (goeW N ω)} =
      (R ∘ goeW N) ⁻¹' {x | (N : ℝ) ^ ε * c < f₂ x} := by
    ext ω
    change (N : ℝ) ^ ε * c < f₁ (goeW N ω) ↔ (N : ℝ) ^ ε * c < f₂ (R (goeW N ω))
    rw [hf]
  have e2 : {ω | (N : ℝ) ^ ε * c < f₂ (goeW N ω)} =
      goeW N ⁻¹' {x | (N : ℝ) ^ ε * c < f₂ x} := rfl
  rw [e2] at h
  rw [e1, ← Measure.map_apply (hR.comp (aux_measurable_goeW N)) hP,
    ← Measure.map_map hR (aux_measurable_goeW N), hν, Measure.map_apply (aux_measurable_goeW N) hP]
  exact h

/-- The reflected spectrum: a permutation `e` with `diag(spec(-A)) = (-diag(spec A))` reindexed
by `e`, and the matching relation between the solutions `m^W`. -/
private lemma aux_refl_data {N : ℕ} (hN : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) :
    ∃ e : Equiv.Perm (Fin N),
      diagonal (specOf (-A)) = (-diagonal (specOf A)).submatrix e e ∧
      ∀ z : ℂ, 0 < z.im →
        mW (specOf (diagonal (specOf (-A)))) z =
          -(starRingEnd ℂ) (mW (specOf (diagonal (specOf A))) (-(starRingEnd ℂ) z)) := by
  obtain ⟨e, he⟩ := aux_specOf_neg hA
  refine ⟨e, ?_, fun z hz => ?_⟩
  · have hd : (-diagonal (specOf A) : Matrix (Fin N) (Fin N) ℝ) = diagonal (-specOf A) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hd, Matrix.submatrix_diagonal_equiv, he]
  · have hw : 0 < (-(starRingEnd ℂ) z).im := by simpa using hz
    rw [specOf_diagonal_specOf, specOf_diagonal_specOf, he, mW_comp_perm]
    have := mW_neg hN (specOf A) hw
    rwa [show -(starRingEnd ℂ) (-(starRingEnd ℂ) z) = z by simp] at this

/-- Every entry of `G^W` is a measurable function of the matrix `W`. -/
private lemma aux_measurable_GW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s t : Fin N) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t := by
  have hc : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    unfold cplx
    exact ((continuous_id.add continuous_const).matrix_map Complex.continuous_ofReal).sub
      continuous_const
  have hdet : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    hc.matrix_det.measurable
  have hadj : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t :=
    (Matrix.measurable_iff.1 hc.matrix_adjugate.measurable) s t
  have h : (fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t) = fun Wm =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t := by
    funext Wm
    unfold GW
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

/-- `N⁻¹ tr G^W` is a measurable function of the matrix `W`. -/
private lemma aux_measurable_mNW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => mNW A Wm z := by
  unfold mNW Matrix.trace
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => by
    simpa using aux_measurable_GW A z i i)

/-- Splitting `X + (-D)` reindexed by `e` as the negative of a reindexed matrix. -/
private lemma aux_refl_X {N : ℕ} (D X : Matrix (Fin N) (Fin N) ℝ) (e : Equiv.Perm (Fin N)) :
    X + (-D).submatrix e e = -((-(X.submatrix e.symm e.symm) + D).submatrix e e) := by
  ext i j
  simp [Matrix.submatrix_apply]
  ring

/-- The entrywise law for `(W^Gauss, D, 𝐃^W)` passes to `(W^Gauss, D_{-A}, 𝐃^W)`
(`G^{-H}(z) = -conj G^{H}(-z̄)`, `Ψ_{-a}(z) = Ψ_a(-z̄)`, `-W^Gauss` and `P W^Gauss Pᵀ` have the
law of `W^Gauss`). -/
theorem entrywiseLawWAt_goe_neg {N : ℕ} (hN : 1 ≤ N) {ε D τ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (h : EntrywiseLawWAt N ε D (diagonal (specOf A)) (goeW N) (domW τ N)) :
    EntrywiseLawWAt N ε D (diagonal (specOf (-A))) (goeW N) (domW τ N) := by
  obtain ⟨e, hDe, hmW⟩ := aux_refl_data hN hA
  intro z hz s t
  have hwD := aux_domW_reflect hz
  set w : ℂ := -(starRingEnd ℂ) z with hw
  have hwim : w.im = z.im := by simp [hw]
  have hm := hmW z hz.1
  rw [← hw] at hm
  set D0 : Matrix (Fin N) (Fin N) ℝ := diagonal (specOf A) with hD0
  have hpt : ∀ X : Matrix (Fin N) (Fin N) ℝ,
      ‖(GW (diagonal (specOf (-A))) X z - piW (diagonal (specOf (-A))) z) s t‖ =
        ‖(GW D0 (-(X.submatrix e.symm e.symm)) w - piW D0 w) (e s) (e t)‖ := by
    intro X
    have h1 := aux_GW_neg D0 X e z
    have h2 := aux_piW_neg D0 e z (by rw [← hDe]; exact hm)
    rw [← hDe] at h1 h2
    rw [h1, h2]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.map_apply]
    rw [show ∀ a b : ℂ, -(starRingEnd ℂ) a - -(starRingEnd ℂ) b = -(starRingEnd ℂ) (a - b) from
      fun a b => by rw [map_sub]; ring, norm_neg, Complex.norm_conj]
  have hψ : PsiW (specOf (diagonal (specOf (-A)))) z = PsiW (specOf D0) w := by
    unfold PsiW
    rw [hm, hwim]
    simp
  have h' := h w hwD (e s) (e t)
  rw [hψ]
  unfold ODomAt at h' ⊢
  refine aux_domAt_transfer (R := fun X => -(X.submatrix e.symm e.symm))
    ((aux_measurable_neg N).comp (aux_measurable_submatrix _ _)) (aux_map_R N e)
    (f₁ := fun X => ‖(GW (diagonal (specOf (-A))) X z - piW (diagonal (specOf (-A))) z) s t‖)
    (f₂ := fun X => ‖(GW D0 X w - piW D0 w) (e s) (e t)‖) ?_ (fun ω => hpt _) h'
  exact ((aux_measurable_GW D0 w (e s) (e t)).sub measurable_const).norm

/-- The averaged law for `(W^Gauss, D, 𝐃^W)` passes to `(W^Gauss, D_{-A}, 𝐃^W)`. -/
theorem averagedLawWAt_goe_neg {N : ℕ} (hN : 1 ≤ N) {ε D τ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (h : AveragedLawWAt N ε D (diagonal (specOf A)) (goeW N) (domW τ N)) :
    AveragedLawWAt N ε D (diagonal (specOf (-A))) (goeW N) (domW τ N) := by
  obtain ⟨e, hDe, hmW⟩ := aux_refl_data hN hA
  intro z hz
  have hwD := aux_domW_reflect hz
  set w : ℂ := -(starRingEnd ℂ) z with hw
  have hwim : w.im = z.im := by simp [hw]
  have hm := hmW z hz.1
  rw [← hw] at hm
  set D0 : Matrix (Fin N) (Fin N) ℝ := diagonal (specOf A) with hD0
  have hpt : ∀ X : Matrix (Fin N) (Fin N) ℝ,
      ‖mNW (diagonal (specOf (-A))) X z - mW (specOf (diagonal (specOf (-A)))) z‖ =
        ‖mNW D0 (-(X.submatrix e.symm e.symm)) w - mW (specOf D0) w‖ := by
    intro X
    have h1 := aux_GW_neg D0 X e z
    rw [← hDe] at h1
    unfold mNW
    rw [h1, aux_trace_refl, hm]
    rw [show ∀ a b : ℂ, (N : ℂ)⁻¹ * -(starRingEnd ℂ) a - -(starRingEnd ℂ) b =
        -(starRingEnd ℂ) ((N : ℂ)⁻¹ * a - b) from
      fun a b => by simp only [map_sub, map_mul, map_inv₀, Complex.conj_natCast]; ring,
      norm_neg, Complex.norm_conj]
  have h' := h w hwD
  rw [← hwim]
  unfold ODomAt at h' ⊢
  refine aux_domAt_transfer (R := fun X => -(X.submatrix e.symm e.symm))
    ((aux_measurable_neg N).comp (aux_measurable_submatrix _ _)) (aux_map_R N e)
    (f₁ := fun X => ‖mNW (diagonal (specOf (-A))) X z - mW (specOf (diagonal (specOf (-A)))) z‖)
    (f₂ := fun X => ‖mNW D0 X w - mW (specOf D0) w‖) ?_ (fun ω => hpt _) h'
  exact ((aux_measurable_mNW D0 w).sub measurable_const).norm

/-- The rigid extremes of `W^Gauss + D` pass to `W^Gauss + D_{-A}` (the two edges swap). -/
theorem rigidExtremesWAt_goe_neg {N : ℕ} (hN : 1 ≤ N) {ε D : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (h : RigidExtremesWAt N ε D (specOf A) (fun ω => goeW N ω + diagonal (specOf A))) :
    RigidExtremesWAt N ε D (specOf (-A)) (fun ω => goeW N ω + diagonal (specOf (-A))) := by
  obtain ⟨e, hDe, -⟩ := aux_refl_data hN hA
  obtain ⟨hLp, hLm⟩ := LpW_specOf_neg hA
  set D0 : Matrix (Fin N) (Fin N) ℝ := diagonal (specOf A) with hD0
  have hsym : ∀ ω, (goeW N ω).IsHermitian := fun ω => by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (isGOE_goeW N).symm ω
  have hherm : ∀ ω, (-((goeW N ω).submatrix e.symm e.symm) + D0).IsHermitian := fun ω =>
    ((Matrix.IsHermitian.submatrix (hsym ω) e.symm).neg).add (Matrix.isHermitian_diagonal _)
  have hid : ∀ ω j, 1 ≤ j → j ≤ N →
      sortedEig (goeW N ω + diagonal (specOf (-A))) j =
        -sortedEig (-((goeW N ω).submatrix e.symm e.symm) + D0) (N + 1 - j) := by
    intro ω j hj hjN
    rw [hDe, aux_refl_X D0 (goeW N ω) e, sortedEig_neg' ((hherm ω).submatrix e) hj hjN,
      aux_sortedEig_submatrix (hherm ω) e]
  have hRm : Measurable fun X : Matrix (Fin N) (Fin N) ℝ => -(X.submatrix e.symm e.symm) :=
    (aux_measurable_neg N).comp (aux_measurable_submatrix _ _)
  unfold RigidExtremesWAt RigidExtremesAt at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · refine aux_domAt_transfer (R := fun X => -(X.submatrix e.symm e.symm)) hRm (aux_map_R N e)
      (f₁ := fun X => max (sortedEig (X + diagonal (specOf (-A))) 1 - LpW (specOf (-A))) 0)
      (f₂ := fun X => max (LmW (specOf A) - sortedEig (X + D0) N) 0) ?_ ?_ h2
    · exact (measurable_const.sub
        ((measurable_sortedEig' N N).comp (aux_measurable_add_const D0))).max measurable_const
    · intro ω
      rw [hid ω 1 le_rfl hN, Nat.add_sub_cancel, hLp]
      congr 1
      ring
  · refine aux_domAt_transfer (R := fun X => -(X.submatrix e.symm e.symm)) hRm (aux_map_R N e)
      (f₁ := fun X => max (LmW (specOf (-A)) - sortedEig (X + diagonal (specOf (-A))) N) 0)
      (f₂ := fun X => max (sortedEig (X + D0) 1 - LpW (specOf A)) 0) ?_ ?_ h1
    · exact (((measurable_sortedEig' N 1).comp (aux_measurable_add_const D0)).sub
        measurable_const).max measurable_const
    · intro ω
      rw [hid ω N hN le_rfl, show N + 1 - N = 1 by omega, hLm]
      congr 1
      ring

/-- The orthogonal invariance of the GOE for `Φ = λ₁` and the non-diagonal `A = aEx N`. -/
example (N : ℕ) :
    (∫ ω, sortedEig (goeW N ω + aEx N) 1) =
      ∫ ω, sortedEig (goeW N ω + diagonal (specOf (aEx N))) 1 :=
  integral_goe_add_conj (aEx_isHermitian N) (measurable_sortedEig' N 1)
    fun _O hO _X hX => sortedEig_conj hO hX 1

/-- Reflection along `(wigRad N, aEx N)`: `-wigRad N` is in the class, the standing bound passes
to `-aEx N`, and `L₊(spec(-aEx N)) = -L₋(spec(aEx N))`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    WigClassEntries (fun _ => 1) N (fun ω => -wigRad N ω) ∧
      StandingBoundW (1 / 2) (specOf (-aEx N)) (domW (1 / 2) N) ∧
      LpW (specOf (-aEx N)) = -LmW (specOf (aEx N)) :=
  ⟨(wignerEntries_wigRad hN).toClass.neg,
    standingBoundW_specOf_neg hN (aEx_isHermitian N) (standingBoundW_aEx hN),
    (LpW_specOf_neg (aEx_isHermitian N)).1⟩

/-- The negation symmetry of the GOE for `Φ = λ₁` and the non-diagonal `B = aEx N`. -/
example (N : ℕ) :
    (∫ ω, sortedEig (-goeW N ω + aEx N) 1) = ∫ ω, sortedEig (goeW N ω + aEx N) 1 :=
  integral_goe_neg (measurable_sortedEig' N 1) (aEx N)

/-- The reflection `λ₁(-X) = -λ_N(X)` for the non-diagonal `X = aEx N`, `N ≥ 1`. -/
example (N : ℕ) (hN : 1 ≤ N) : sortedEig (-aEx N) 1 = -sortedEig (aEx N) N := by
  simpa using sortedEig_neg' (aEx_isHermitian N) le_rfl hN

/-- The entrywise law along `(goeW N, aEx N)`, `N ≥ 2`, with `aEx N` not diagonal. The law
hypothesis is a binder. -/
example (N : ℕ) (hN : 2 ≤ N) {ε D : ℝ}
    (h : EntrywiseLawWAt N ε D (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N)) :
    EntrywiseLawWAt N ε D (diagonal (specOf (-aEx N))) (goeW N) (domW (1 / 2) N) :=
  entrywiseLawWAt_goe_neg (by omega) (aEx_isHermitian N) h

/-- The averaged law along `(goeW N, aEx N)`, `N ≥ 2`. The law hypothesis is a binder. -/
example (N : ℕ) (hN : 2 ≤ N) {ε D : ℝ}
    (h : AveragedLawWAt N ε D (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N)) :
    AveragedLawWAt N ε D (diagonal (specOf (-aEx N))) (goeW N) (domW (1 / 2) N) :=
  averagedLawWAt_goe_neg (by omega) (aEx_isHermitian N) h

/-- The rigid extremes along `(goeW N, aEx N)`, `N ≥ 2`. The hypothesis is a binder. -/
example (N : ℕ) (hN : 2 ≤ N) {ε D : ℝ}
    (h : RigidExtremesWAt N ε D (specOf (aEx N))
      (fun ω => goeW N ω + diagonal (specOf (aEx N)))) :
    RigidExtremesWAt N ε D (specOf (-aEx N))
      (fun ω => goeW N ω + diagonal (specOf (-aEx N))) :=
  rigidExtremesWAt_goe_neg (by omega) (aEx_isHermitian N) h

#print axioms integral_goe_add_conj
#print axioms integral_goe_neg
#print axioms sortedEig_conj
#print axioms sortedEig_neg'
#print axioms measurable_sortedEig'
#print axioms WigClassEntries.neg
#print axioms LpW_specOf_neg
#print axioms standingBoundW_specOf_neg
#print axioms entrywiseLawWAt_goe_neg
#print axioms averagedLawWAt_goe_neg
#print axioms rigidExtremesWAt_goe_neg

end Anisotropic
