import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Eigen
import Anisotropic.EdgeUniv.Invariance
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.EdgeUniv.RegS
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.GeneralT.Model
import Anisotropic.GeneralT.Spectra
import Anisotropic.Instances.MarchenkoPasturTwo
import Anisotropic.Instances.Models
import Anisotropic.LinAlg.Spectral
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Qdot.Defs
import Anisotropic.Qdot.EdgeCompare
import Anisotropic.Qdot.EdgeCompareMain
import Anisotropic.Qdot.EdgeDefs
import Anisotropic.Qdot.EdgeRegime
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 11.4: edge universality for `Q̇` at the partner edge, under (T_diag) and for general `T` -/

/-- The matrix `O` with columns `b_i` of an orthonormal basis of `ℝⁿ` has `OᵀO = I`. -/
private lemma qdot_onb_transpose_mul {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (Matrix.of fun μ i => b i μ)ᵀ * (Matrix.of fun μ i => b i μ) = 1 := by
  ext i j
  have h := orthonormal_iff_ite.1 b.orthonormal i j
  rw [PiLp.inner_apply] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [mul_comm]

/-- The matrix `O` with columns `b_i` of an orthonormal basis of `ℝⁿ` has `OOᵀ = I`. -/
private lemma qdot_onb_mul_transpose {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (Matrix.of fun μ i => b i μ) * (Matrix.of fun μ i => b i μ)ᵀ = 1 :=
  mul_eq_one_comm.1 (qdot_onb_transpose_mul b)

/-- An `N × (N − 1)` isometry onto `1^⊥`: `PᵀP = I_{N−1}` and `PPᵀ = π̄`. -/
theorem exists_piBar_isometry (hN : 1 ≤ N) :
    ∃ P : Matrix (Fin N) (Fin (N - 1)) ℝ, Pᵀ * P = 1 ∧ P * Pᵀ = piBar N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hN0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  set e : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (fun _ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) with he
  have hsq : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ =
      ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hN0.le]
  have hnorm : ‖e‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow]
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    push_cast
    field_simp
  have hon : Orthonormal ℝ (({Fin.last n} : Set (Fin (n + 1))).domRestrict fun _ => e) := by
    refine ⟨fun _ => hnorm, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  have h1 := qdot_onb_transpose_mul b
  have h2 := qdot_onb_mul_transpose b
  have hlast : ∀ μ, b (Fin.last n) μ = (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro μ
    simp [hb (Fin.last n) rfl, he]
  refine ⟨Matrix.of fun μ j => b (Fin.castSucc j) μ, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h1 (Fin.castSucc i)) (Fin.castSucc j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply,
      Fin.castSucc_inj] at this ⊢
    exact this
  · ext μ ν
    have := congrFun (congrFun h2 μ) ν
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] at this ⊢
    rw [hlast, hlast, hsq] at this
    simp only [piBar, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
    rw [eq_sub_iff_add_eq]
    convert this using 3

/-- The entries of `A` listed over `Fin K × Fin N`. -/
private def qdot_flatMat {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) : Fin K × Fin N → ℝ :=
  fun p => A p.1 p.2

/-- Listing the entries is measurable. -/
private lemma qdot_measurable_flatMat {K N : ℕ} : Measurable (qdot_flatMat (K := K) (N := N)) :=
  measurable_pi_iff.2 fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- A measurable matrix with the law of a Gaussian ensemble is a Gaussian ensemble. -/
private lemma qdot_isGaussianEnsemble_of_map_eq {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {K N : ℕ} {X Y : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hYm : Measurable Y)
    (hYX : (ℙ : Measure Ω).map Y = (ℙ : Measure Ω).map X) : IsGaussianEnsemble Y := by
  have hmeas : ∀ i μ, Measurable fun ω => Y ω i μ := fun i μ =>
    (measurable_pi_apply μ).comp ((measurable_pi_apply i).comp hYm)
  have hjoint : (ℙ : Measure Ω).map (fun ω (p : Fin K × Fin N) => Y ω p.1 p.2) =
      Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    have h : (fun ω (p : Fin K × Fin N) => Y ω p.1 p.2) = qdot_flatMat ∘ Y := rfl
    rw [h, ← Measure.map_map qdot_measurable_flatMat hYm, hYX,
      Measure.map_map qdot_measurable_flatMat hX.measurable_mat]
    exact hX.map_entries
  have hlaw : ∀ i μ, (ℙ : Measure Ω).map (fun ω => Y ω i μ) = gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    intro i μ
    have h : (fun ω => Y ω i μ) =
        Function.eval (i, μ) ∘ fun ω (p : Fin K × Fin N) => Y ω p.1 p.2 := rfl
    rw [h, ← Measure.map_map (measurable_pi_apply (i, μ))
      (measurable_pi_iff.2 fun p => hmeas p.1 p.2), hjoint]
    exact (measurePreserving_eval (fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹)
      (i, μ)).map_eq
  refine ⟨hmeas, ?_, hlaw⟩
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun (p : Fin K × Fin N) ω => Y ω p.1 p.2)
    fun p => (hmeas p.1 p.2).aemeasurable).2 ?_
  rw [hjoint]
  congr 1
  funext p
  exact (hlaw p.1 p.2).symm

/-- For a Gaussian `K × N` ensemble (entries `N(0, 1/N)`) and an `N × n` isometry `P`
(`PᵀP = I_n`), `(N/n)^{1/2} X P` is a Gaussian `K × n` ensemble (entries `N(0, 1/n)`). -/
theorem IsGaussianEnsemble.mul_isometry {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {K N n : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) {P : Matrix (Fin N) (Fin n) ℝ} (hP : Pᵀ * P = 1) :
    IsGaussianEnsemble (fun ω => Real.sqrt ((N : ℝ) / n) • (X ω * P)) := by
  set v : Fin n → EuclideanSpace ℝ (Fin N) := fun j => WithLp.toLp 2 (fun μ => P μ j) with hv
  have hvo : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have := congrFun (congrFun hP i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    rw [PiLp.inner_apply, ← this]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [hv, mul_comm]
  have hnN : n ≤ N := by
    have := hvo.linearIndependent.fintype_card_le_finrank
    simpa [finrank_euclideanSpace] using this
  set s : Set (Fin N) := {i | (i : ℕ) < n} with hs
  set v' : Fin N → EuclideanSpace ℝ (Fin N) :=
    fun i => if h : (i : ℕ) < n then v ⟨i, h⟩ else 0 with hv'
  have hon : Orthonormal ℝ (s.domRestrict v') := by
    have : s.domRestrict v' = v ∘ (fun i : s => (⟨i.1, i.2⟩ : Fin n)) := by
      funext i
      have hi : ((i : Fin N) : ℕ) < n := i.2
      simp [hv', Set.domRestrict, hi]
    rw [this]
    refine hvo.comp _ fun a b h => Subtype.ext (Fin.ext ?_)
    simpa using congrArg Fin.val h
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace, Fintype.card_fin])
  set O : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun μ i => b i μ with hO
  have hcol : ∀ μ (j : Fin n), O μ (Fin.castLE hnN j) = P μ j := by
    intro μ j
    have := hb (Fin.castLE hnN j) (show ((Fin.castLE hnN j : Fin N) : ℕ) < n from j.2)
    simp [hO, this, hv', hv]
  have hOg : Oᵀ ∈ orthogonalGroup (Fin N) ℝ := by
    rw [mem_orthogonalGroup_iff', transpose_transpose]
    exact qdot_onb_mul_transpose b
  have hrot := hX.map_rotate (one_mem (orthogonalGroup (Fin K) ℝ)) hOg
  simp only [Matrix.one_mul, transpose_transpose] at hrot
  have hZ : IsGaussianEnsemble fun ω => X ω * O :=
    qdot_isGaussianEnsemble_of_map_eq hX
      ((continuous_id.matrix_mul continuous_const).measurable.comp hX.measurable_mat) hrot
  set c := Real.sqrt ((N : ℝ) / n) with hc
  have hY : ∀ ω i j, (c • (X ω * P)) i j = c * (X ω * O) i (Fin.castLE hnN j) := by
    intro ω i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, hcol]
  refine ⟨fun i j => ?_, ?_, fun i j => ?_⟩
  · simp_rw [hY]
    exact (hZ.measurable i _).const_mul c
  · have : (fun (p : Fin K × Fin n) ω => (c • (X ω * P)) p.1 p.2) = fun p =>
        (fun x => c * x) ∘ fun ω => (X ω * O) (p.1, Fin.castLE hnN p.2).1
          (p.1, Fin.castLE hnN p.2).2 := by
      funext p ω
      exact hY ω p.1 p.2
    rw [this]
    have hinj : Function.Injective fun p : Fin K × Fin n => (p.1, Fin.castLE hnN p.2) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.castLE_injective hnN h.2)
    exact (hZ.indep.precomp hinj).comp (fun _ x => c * x) fun _ => measurable_const_mul c
  · have hn : 0 < n := Fin.pos j
    have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    simp_rw [hY]
    rw [show (fun ω => c * (X ω * O) i (Fin.castLE hnN j)) =
        (fun x => c * x) ∘ fun ω => (X ω * O) i (Fin.castLE hnN j) from rfl,
      ← Measure.map_map (measurable_const_mul c) (hZ.measurable i _), hZ.law i _,
      gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_natCast, hc,
      Real.sq_sqrt (div_nonneg hNp.le hnp.le)]
    field_simp

/-- The multiplicity of a value in `specOf A` is its root multiplicity in the characteristic
polynomial, for symmetric `A`. -/
private lemma qdot_card_eigen {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (s : ℝ) :
    (Finset.univ.filter fun i => specOf A i = s).card = A.charpoly.roots.count s := by
  rw [hA.roots_charpoly_eq_eigenvalues, specOf_eq hA]
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id]
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

/-- For `PᵀP = I` and symmetric `B`, `P B Pᵀ` and `B` have the same nonzero eigenvalues with
multiplicity. -/
private lemma qdot_nzEq_conj {K n : ℕ} {P : Matrix (Fin K) (Fin n) ℝ} (hP : Pᵀ * P = 1)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (hA : (P * B * Pᵀ).IsHermitian) :
    NzEq (specOf (P * B * Pᵀ)) (specOf B) := by
  intro s hs
  rw [qdot_card_eigen hA, qdot_card_eigen hB]
  have h := Matrix.charpoly_mul_comm' P (B * Pᵀ)
  rw [Matrix.mul_assoc B, hP, Matrix.mul_one, ← Matrix.mul_assoc] at h
  have hc := congrArg (fun p => p.roots.count s) h
  rw [Polynomial.roots_mul, Polynomial.roots_mul, Multiset.count_add, Multiset.count_add] at hc
  · simpa [Polynomial.roots_X_pow, Multiset.count_nsmul, Multiset.count_singleton, hs] using hc
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero

/-- Equal nonzero spectra give equal counts `n_A(E)` for `E > 0`. -/
private lemma qdot_eigCount_eq {K n : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} (h : NzEq (specOf A) (specOf B)) {E : ℝ} (hE : 0 < E) :
    eigCount A E = eigCount B E := by
  set S : Finset ℝ := Finset.univ.image (specOf A) ∪ Finset.univ.image (specOf B) with hS
  have key : ∀ {L : ℕ} (τ : Fin L → ℝ), Finset.univ.image τ ⊆ S →
      (Finset.univ.filter fun j => E ≤ τ j).card =
        ∑ s ∈ S, (Finset.univ.filter fun i => τ i = s).card * (if E ≤ s then 1 else 0) := by
    intro L τ hτ
    rw [Finset.card_filter, Finset.sum_comp (fun s => if E ≤ s then 1 else 0) τ,
      Finset.sum_subset hτ]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_eq_mul]
    · intro s _ hs
      have : (Finset.univ.filter fun i => τ i = s) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      simp [this]
  unfold eigCount
  rw [key (specOf A) Finset.subset_union_left, key (specOf B) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = 0
  · simp [hs, not_le.2 hE]
  · rw [h s hs]

/-- A positive semidefinite matrix has `λ_i ≥ 0` for every index. -/
private lemma qdot_sortedEig_nonneg {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.PosSemidef)
    (i : ℕ) : 0 ≤ sortedEig A i := by
  by_cases hi : 1 ≤ i ∧ i ≤ K
  · rw [sortedEig_ge_iff hA.isHermitian hi.1 hi.2]
    have : eigCount A 0 = K := by
      unfold eigCount
      rw [specOf_eq hA.isHermitian, Finset.filter_true_of_mem fun j _ => hA.eigenvalues_nonneg j]
      simp
    omega
  · unfold sortedEig
    rw [dite_eq_right_iff.2]
    rintro ⟨-, h1, h2⟩
    exact absurd ⟨h1, by simpa using h2⟩ hi

/-- For `Σ ⪰ 0` and an isometry `P` onto `1^⊥`, the ordered eigenvalues of the `N × N` companion
of `Q̇` are those of `Q_{N−1} = Yᵀ Σ Y`, `Y = (N/(N−1))^{1/2} X P`, index by index (both vanish
from the index `N` on). -/
theorem sortedEig_QdotN_isometry {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef)
    (hN : 2 ≤ N) {P : Matrix (Fin N) (Fin (N - 1)) ℝ} (hP : Pᵀ * P = 1)
    (hPP : P * Pᵀ = piBar N) (Xm : Matrix (Fin M) (Fin N) ℝ) (j : ℕ) :
    sortedEig (QdotN Sig Xm) j =
      sortedEig (QN Sig (Real.sqrt ((N : ℝ) / ((N - 1 : ℕ) : ℝ)) • (Xm * P))) j := by
  set c := Real.sqrt ((N : ℝ) / ((N - 1 : ℕ) : ℝ)) with hc
  set B := QN Sig (c • (Xm * P)) with hBdef
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hcc : c * c = (N : ℝ) / ((N : ℝ) - 1) := by
    rw [hc, Real.mul_self_sqrt (by positivity), hN1]
  have hA : QdotN Sig Xm = P * B * Pᵀ := by
    unfold QdotN QN Xdot at *
    rw [hBdef, ← hPP, ← hcc]
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have hBpsd : B.PosSemidef := by
    have h := hSig.conjTranspose_mul_mul_same (c • (Xm * P))
    simpa [conjTranspose_eq_transpose_of_trivial, hBdef, QN] using h
  have hApsd := QdotN_posSemidef hSig Xm
  have hz : NzEq (specOf (QdotN Sig Xm)) (specOf B) := by
    rw [hA]
    exact qdot_nzEq_conj hP hBpsd.isHermitian (hA ▸ hApsd.isHermitian)
  have hcnt : ∀ E, 0 < E → eigCount (QdotN Sig Xm) E = eigCount B E :=
    fun E hE => qdot_eigCount_eq hz hE
  rcases Nat.lt_or_ge j N with hj | hj
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp [sortedEig]
    have hjN : j ≤ N := hj.le
    have hjN' : j ≤ N - 1 := by omega
    have key : ∀ {K₁ K₂ : ℕ} {A₁ : Matrix (Fin K₁) (Fin K₁) ℝ} {A₂ : Matrix (Fin K₂) (Fin K₂) ℝ},
        A₁.PosSemidef → A₂.PosSemidef → j ≤ K₁ → j ≤ K₂ →
        (∀ E, 0 < E → eigCount A₁ E = eigCount A₂ E) → sortedEig A₁ j ≤ sortedEig A₂ j := by
      intro K₁ K₂ A₁ A₂ h₁ h₂ hj₁ hj₂ hE
      rcases le_or_gt (sortedEig A₁ j) 0 with hle | hlt
      · exact hle.trans (qdot_sortedEig_nonneg h₂ j)
      · rw [sortedEig_ge_iff h₂.isHermitian h0 hj₂, ← hE _ hlt]
        exact (sortedEig_ge_iff h₁.isHermitian h0 hj₁ _).1 le_rfl
    exact le_antisymm (key hApsd hBpsd hjN hjN' hcnt)
      (key hBpsd hApsd hjN' hjN fun E hE => (hcnt E hE).symm)
  · have hB0 : sortedEig B j = 0 := by
      unfold sortedEig
      rw [dite_eq_right_iff]
      rintro ⟨-, -, h2⟩
      simp at h2
      omega
    rw [hB0]
    rcases hj.eq_or_lt with h | h
    · subst h
      exact sortedEig_QdotN_last hSig Xm (by omega)
    · unfold sortedEig
      rw [dite_eq_right_iff]
      rintro ⟨-, -, h2⟩
      simp at h2
      omega

private def qdot_unflatMat {K N : ℕ} (x : Fin K × Fin N → ℝ) : Matrix (Fin K) (Fin N) ℝ :=
  fun i μ => x (i, μ)

private lemma qdot_measurable_unflatMat {K N : ℕ} :
    Measurable (qdot_unflatMat (K := K) (N := N)) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => measurable_pi_apply (i, μ)

private lemma qdot_measurable_QN (Sig : Matrix (Fin M) (Fin M) ℝ) :
    Measurable fun Xm : Matrix (Fin M) (Fin N) ℝ => QN Sig Xm :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_id).measurable

private lemma qdot_map_eq_pi_map {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : IsGaussianEnsemble X) :
    (ℙ : Measure Ω).map X =
      (Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹).map qdot_unflatMat := by
  have h : X = qdot_unflatMat ∘ fun ω (p : Fin K × Fin N) => X ω p.1 p.2 := rfl
  have hm : Measurable fun ω (p : Fin K × Fin N) => X ω p.1 p.2 :=
    measurable_pi_iff.2 fun p => hX.measurable p.1 p.2
  rw [h, ← Measure.map_map qdot_measurable_unflatMat hm, hX.map_entries]

private lemma qdot_integral_ensemble_eq {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} {Y : Ω' → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hY : IsGaussianEnsemble Y)
    {g : Matrix (Fin K) (Fin N) ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X ω) = ∫ ω, g (Y ω) := by
  rw [← integral_map hX.measurable_mat.aemeasurable hg.aestronglyMeasurable,
    ← integral_map hY.measurable_mat.aemeasurable hg.aestronglyMeasurable, qdot_map_eq_pi_map hX,
    qdot_map_eq_pi_map hY]

/-- The reference value of Theorem 11.4: for Gaussian `X`, `Q̇` is a sample covariance matrix
with `N − 1` Gaussian samples, so `E f(q̇_{k,l}) = b_{N−1}(f, π)` (`bRef` at `N − 1`). -/
theorem integral_qDotVec_gauss {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) (hN : 2 ≤ N)
    (k l : ℕ) {f : (Fin l → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, f (qDotVec Sig (gaussX M N ω) k l) = bRef (N - 1) (specOf Sig) k l f := by
  obtain ⟨P, hP, hPP⟩ := exists_piBar_isometry (N := N) (by omega)
  have hY := (gaussX_isGaussianEnsemble M N).mul_isometry hP
  have hq : ∀ Xm : Matrix (Fin M) (Fin N) ℝ, qDotVec Sig Xm k l =
      qVecA (N - 1) (specOf Sig)
        (QN Sig (Real.sqrt ((N : ℝ) / ((N - 1 : ℕ) : ℝ)) • (Xm * P))) k l := by
    intro Xm
    funext i
    unfold qDotVec qVecA
    rw [sortedEig_QdotN_isometry hSig.posSemidef hN hP hPP]
  simp_rw [hq]
  have hg : Measurable fun Y : Matrix (Fin M) (Fin (N - 1)) ℝ =>
      f (qVecA (N - 1) (specOf Sig) (QN Sig Y) k l) :=
    hf.comp ((measurable_qVecA (N - 1) (specOf Sig) (N - 1) k l).comp (qdot_measurable_QN Sig))
  rw [qdot_integral_ensemble_eq (g := fun Y => f (qVecA (N - 1) (specOf Sig) (QN Sig Y) k l)) hY
    (gaussX_isGaussianEnsemble M (N - 1)) hg]
  exact bRef_gauss hSig (N - 1) k l hf

private lemma qdot_rpow_pred_le {N : ℕ} (hN : 2 ≤ N) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ((N - 1 : ℕ) : ℝ) ^ (-θ) ≤ 2 * (N : ℝ) ^ (-θ) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < N / 2 := by linarith
  have hle : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by rw [hc]; linarith
  have h2 : ((N - 1 : ℕ) : ℝ) ^ (-θ) ≤ ((N : ℝ) / 2) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul] at h2
  have h3 : (2 : ℝ) ^ θ ≤ 2 := by
    calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ (N : ℝ) ^ (-θ) := Real.rpow_nonneg (by linarith) _
  nlinarith

private lemma qdot_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (s : ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) : (s • QdotN Sig Xm).IsHermitian := by
  unfold QdotN QN
  exact ((XSX_isHermitian hSig (Xdot Xm)).smul (IsSelfAdjoint.all _)).smul (IsSelfAdjoint.all _)

private lemma qdot_measurable {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (s : ℝ) {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : Measurable X) :
    Measurable fun ω => s • QdotN Sig (X ω) := by
  have hc : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => s • QdotN Sig Xm := by
    have h1 : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => Xm * piBar N :=
      continuous_id.matrix_mul continuous_const
    have h2 : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ =>
        (Xm * piBar N)ᵀ * Sig * (Xm * piBar N) :=
      (h1.matrix_transpose.matrix_mul continuous_const).matrix_mul h1
    unfold QdotN QN Xdot
    exact (h2.const_smul ((N : ℝ) / (N - 1))).const_smul s
  exact hc.measurable.comp hX

/-- Theorem 11.4 under (T_diag), bounded Lipschitz `h`, with rate: the rescaled extreme
eigenvalues `q̇` of `Q̇` at the partner `k' = edgePartner N σ k` of a regular edge `k` (the edge of
the classical data of `N − 1` samples within `C₁/N` of `a_k`), against the Gaussian reference value
with `N − 1` samples. -/
theorem edge_univ_dot_lip (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
        |(∫ ω, h (qDotVec Sig (X ω) (edgePartner N (specOf Sig) k) l)) -
            bRef (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k) l h| ≤
          K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  obtain ⟨r₀, C₀, hr₀, hC₀, hreg⟩ := edgeRegime_dot τ hτ
  have hl1 : (0 : ℝ) < l + 1 := by positivity
  obtain ⟨N₁, h₁⟩ := hreg C l ((1 / 200) / (8 * (l + 1))) (by positivity)
    (by rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
  obtain ⟨N₂, h₂⟩ := hreg gaussMoment l ((1 / 200) / (8 * (l + 1))) (by positivity)
    (by rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
  obtain ⟨N₃, h₃⟩ := smoothComparable_dot τ C l (1 / 200) hτ (by norm_num) le_rfl
  obtain ⟨C₁, N₄, h₄⟩ := edgePartner_spec τ hτ
  obtain ⟨N₅, h₅⟩ := cumCount_edge_window (τ / 2) l (by linarith)
  have hc2 := edgec2_pos (by linarith : 0 < τ / 2)
  have hϖm : 0 < min 1 (edgec2 (τ / 2) / 2) := lt_min one_pos (by linarith)
  have hϖ : min 1 (edgec2 (τ / 2) / 2) ≤ max 1 (edgeC2 (τ / 2) / 2) :=
    (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨K, N₆, h₆⟩ := edge_reduction l (1 / 200) (1 / 6 - 25 * (1 / 200))
    (min 1 (edgec2 (τ / 2) / 2)) (max 1 (edgeC2 (τ / 2) / 2)) C₀ r₀ (by norm_num) le_rfl
    (by norm_num) hϖm hϖ (by linarith) hr₀
  refine ⟨2 * |K|, max (max (max N₁ N₂) (max N₃ N₄)) (max (N₅ + 1) (max (N₆ + 1) 2)), ?_⟩
  intro N hN Ω _ _ M Sig X k hm hk h B L hB hL
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N - 1 := by omega
  have hN6 : N₆ ≤ N - 1 := by omega
  have hN7 : 2 ≤ N := by omega
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hda' := densityAssumptions_pred hda hN7
  obtain ⟨-, -, hk'⟩ := h₄ N hN4 M (specOf Sig) hda k hk
  obtain ⟨hw1, hw2⟩ := h₅ (N - 1) hN5 M (specOf Sig) hda' _ hk'
  obtain ⟨hϖpos, hϖlo, hϖhi⟩ := edgeScale_bounds hda' hk'
  have hmem : edgeScale (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k) ∈
      Set.Icc (min 1 (edgec2 (τ / 2) / 2)) (max 1 (edgeC2 (τ / 2) / 2)) := by
    set w := edgeScale (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k)
    constructor
    · rcases le_or_gt 1 w with h1 | h1
      · exact (min_le_left _ _).trans h1
      · refine (min_le_right _ _).trans ?_
        have h2 : w * w ≤ 1 := by nlinarith
        have : w ^ 3 ≤ w := by nlinarith [mul_le_mul_of_nonneg_left h2 hϖpos.le]
        linarith
    · rcases le_or_gt w 1 with h1 | h1
      · exact h1.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have h2 : 1 ≤ w * w := by nlinarith
        have : w ≤ w ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h2 hϖpos.le]
        linarith
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX (by omega) hm.ratio_ge hm.ratio_le hm.sigma
  have hSigH : Sig.IsHermitian := hm.sigma.posDef.isHermitian
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M N) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ =>
      (gaussX_isGaussianEnsemble M N).measurable i μ
  have hnC : ((N : ℕ) : ℝ) ≤ C₀ * ((N - 1 : ℕ) : ℝ) := by
    have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN7
    rw [hc]
    nlinarith
  have hred := h₆ (N - 1) hN6 N
    (edgeDn N (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k))
    (edgeSign (edgePartner N (specOf Sig) k) *
      edgeVal (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k))
    (edgeScale (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k)) hnC hmem
    (fun ω => edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig (X ω))
    (fun ω => edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig (gaussX M N ω))
    (qdot_measurable Sig _ hXm) (qdot_measurable Sig _ hGm)
    (fun ω => qdot_isHermitian hSigH _ _) (fun ω => qdot_isHermitian hSigH _ _)
    (h₁ N hN1 M Sig X k hm hk) (h₂ N hN2 M Sig (gaussX M N) k hgm hk)
    (h₃ N hN3 M Sig X k hm hk) h B L hB hL
  have hq : ∀ Xm : Matrix (Fin M) (Fin N) ℝ,
      qDotVec Sig Xm (edgePartner N (specOf Sig) k) l =
        edgeQ (N - 1) (edgeSign (edgePartner N (specOf Sig) k) *
          edgeVal (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k))
          (edgeScale (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k))
          (edgeDn N (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k)) l
          (edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig Xm) := by
    intro Xm
    have h1 := qdot_isHermitian hSigH 1 Xm
    rw [one_smul] at h1
    exact qVecA_eq_edgeQ_gen h1 hw1 (by omega)
  have hb := integral_qDotVec_gauss hm.sigma.posDef hN7 (edgePartner N (specOf Sig) k) l
    hL.continuous.measurable
  rw [← hb]
  simp_rw [hq]
  have hexp : (1 / 200 : ℝ) / (4 * (l + 1)) = 1 / (800 * (l + 1)) := by
    field_simp; ring
  rw [hexp] at hred
  have hθ0 : (0 : ℝ) ≤ 1 / (800 * (l + 1)) := by positivity
  have hθ1 : (1 : ℝ) / (800 * (l + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hrate := qdot_rpow_pred_le hN7 hθ0 hθ1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hBL : 0 ≤ B + L := add_nonneg hB0 L.2
  have hx0 : 0 ≤ ((N - 1 : ℕ) : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc _ ≤ K * (B + L) * ((N - 1 : ℕ) : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := hred
    _ ≤ |K| * (B + L) * ((N - 1 : ℕ) : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
        gcongr; exact le_abs_self K
    _ ≤ |K| * (B + L) * (2 * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ))) := by gcongr
    _ = 2 * |K| * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by ring

/-- On a probability space, `|E f(Y) - E g(Y)| ≤ δ` for bounded measurable `f, g` with
`|f - g| ≤ δ`. -/
private lemma qdot_integral_sub_le {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {l : ℕ} {Y : Ω → Fin l → ℝ} (hY : Measurable Y)
    {f g : (Fin l → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) {B δ : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) (hfg : ∀ x, |f x - g x| ≤ δ) :
    |(∫ ω, f (Y ω)) - ∫ ω, g (Y ω)| ≤ δ := by
  have hfi : Integrable (fun ω => f (Y ω)) :=
    Integrable.of_bound (hf.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _)
  have hgi : Integrable (fun ω => g (Y ω)) :=
    Integrable.of_bound (hg.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgB _)
  rw [← integral_sub hfi hgi]
  have := norm_integral_le_of_norm_le_const (μ := (ℙ : Measure Ω))
    (f := fun ω => f (Y ω) - g (Y ω)) (C := δ)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfg _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

/-- The rate `K (B + L) N^{-1/(800(l+1))}` is eventually at most `ε`. -/
private lemma qdot_rate_eventually (K B : ℝ) (L : ℝ≥0) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤ ε := by
  have hθ : (0 : ℝ) < 1 / (800 * (l + 1)) := by positivity
  have ht : Tendsto (fun N : ℕ => K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)))
      atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul
      (K * (B + L))
    simpa using this
  exact eventually_atTop.mp (ht.eventually (ge_mem_nhds hε))

/-- Theorem 11.4 under (T_diag), bounded uniformly continuous `h`, at the partner edge. -/
theorem edge_univ_dot (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      |(∫ ω, h (qDotVec Sig (X ω) (edgePartner N (specOf Sig) k) l)) -
          bRef (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k) l h| ≤ ε := by
  obtain ⟨B, hB⟩ := hb
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, L, hgL, hgB, hhg⟩ := exists_lipschitz_approx hB hu hε3
  obtain ⟨K, N₀, hK⟩ := edge_univ_dot_lip τ C l hτ
  obtain ⟨N₁, hN₁⟩ := qdot_rate_eventually K B L l hε3
  refine ⟨max N₀ N₁, fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  set k' := edgePartner N (specOf Sig) k with hk'
  have hhm : Measurable h := hu.continuous.measurable
  have hgm : Measurable g := hgL.continuous.measurable
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M (N - 1)) :=
    (gaussX_isGaussianEnsemble M (N - 1)).measurable_mat
  have hY : Measurable fun ω => qDotVec Sig (X ω) k' l := by
    have := qdot_measurable Sig 1 hXm
    simp only [one_smul] at this
    exact (measurable_qVecA (N - 1) (specOf Sig) N k' l).comp this
  have hY0 : Measurable fun ω =>
      qVecA (N - 1) (specOf Sig) (QN (diagonal (specOf Sig)) (gaussX M (N - 1) ω)) k' l :=
    (measurable_qVecA (N - 1) (specOf Sig) (N - 1) k' l).comp ((qdot_measurable_QN _).comp hGm)
  have e1 := qdot_integral_sub_le hY hhm hgm hB hgB hhg
  have e2 := (hK N (le_of_max_le_left hN) M Sig X k hm hk g B L hgB hgL).trans
    (hN₁ N (le_of_max_le_right hN))
  have e3 : |bRef (N - 1) (specOf Sig) k' l g - bRef (N - 1) (specOf Sig) k' l h| ≤ ε / 3 := by
    unfold bRef
    exact qdot_integral_sub_le hY0 hgm hhm hgB hB (fun x => by rw [abs_sub_comm]; exact hhg x)
  have := abs_add_three ((∫ ω, h (qDotVec Sig (X ω) k' l)) - ∫ ω, g (qDotVec Sig (X ω) k' l))
    ((∫ ω, g (qDotVec Sig (X ω) k' l)) - bRef (N - 1) (specOf Sig) k' l g)
    (bRef (N - 1) (specOf Sig) k' l g - bRef (N - 1) (specOf Sig) k' l h)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at this
  linarith

/-- For symmetric `A, B`, `|λ_j(A) - λ_j(B)| ≤ ‖A - B‖` for the eigenvalues `specOf` (Weyl). -/
private lemma qdot_specOf_lipschitz {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin K) :
    |specOf A j - specOf B j| ≤ ‖A - B‖ := by
  set i : Fin (Fintype.card (Fin K)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j
  have key : ∀ (C : Matrix (Fin K) (Fin K) ℝ) (hC : C.IsHermitian),
      specOf C j = sortedEig C ((i : ℕ) + 1) := by
    intro C hC
    rw [specOf_eq hC]
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true ⟨hC, by omega, by have := i.isLt; omega⟩)]
    rfl
  rw [key A hA, key B hB]
  exact sortedEig_lipschitz hA hB _

/-- `Q_N = Xᵀ S X` is symmetric for symmetric `S`. -/
private lemma qdot_QN_herm {K : ℕ} {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.IsHermitian)
    (Xm : Matrix (Fin K) (Fin N) ℝ) : (QN S Xm).IsHermitian :=
  XSX_isHermitian hS Xm

/-- `‖Xᵀ S X - Xᵀ S' X‖ ≤ ‖Xᵀ‖ ‖S - S'‖ ‖X‖`. -/
private lemma qdot_norm_QN_sub_le {K : ℕ} (S S' : Matrix (Fin K) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) :
    ‖QN S Xm - QN S' Xm‖ ≤ ‖Xmᵀ‖ * ‖S - S'‖ * ‖Xm‖ := by
  have e : QN S Xm - QN S' Xm = Xmᵀ * (S - S') * Xm := by
    simp only [QN, Matrix.mul_sub, Matrix.sub_mul]
  rw [e]
  calc ‖Xmᵀ * (S - S') * Xm‖ ≤ ‖Xmᵀ * (S - S')‖ * ‖Xm‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Xmᵀ‖ * ‖S - S'‖ * ‖Xm‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)

/-- If `‖S_n - S‖ ≤ κ_n → 0`, then `‖Xᵀ S_n X - Xᵀ S X‖ → 0`. -/
private lemma qdot_QN_tendsto {K : ℕ} {Ss : ℕ → Matrix (Fin K) (Fin K) ℝ}
    {S : Matrix (Fin K) (Fin K) ℝ} {κs : ℕ → ℝ} (hle : ∀ n, ‖Ss n - S‖ ≤ κs n)
    (hκ : Tendsto κs atTop (𝓝 0)) (Xm : Matrix (Fin K) (Fin N) ℝ) :
    Tendsto (fun n => ‖QN (Ss n) Xm - QN S Xm‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ‖Xmᵀ‖ * κs n * ‖Xm‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hκ).mul (tendsto_const_nhds (x := ‖Xm‖))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  refine (qdot_norm_QN_sub_le _ _ _).trans ?_
  have := hle n
  gcongr

/-- If `‖S_n - S‖ ≤ κ_n → 0`, then `‖Q̇(S_n) - (N/(N−1)) π̄ Xᵀ S X π̄‖ → 0`. -/
private lemma qdot_QdotN_tendsto {K : ℕ} {Ss : ℕ → Matrix (Fin K) (Fin K) ℝ}
    {S : Matrix (Fin K) (Fin K) ℝ} {κs : ℕ → ℝ} (hle : ∀ n, ‖Ss n - S‖ ≤ κs n)
    (hκ : Tendsto κs atTop (𝓝 0)) (Xm : Matrix (Fin K) (Fin N) ℝ) :
    Tendsto (fun n => ‖QdotN (Ss n) Xm - ((N : ℝ) / (N - 1)) • QN S (Xdot Xm)‖) atTop (𝓝 0) := by
  have h := (qdot_QN_tendsto hle hκ (Xdot Xm)).const_mul ‖((N : ℝ) / (N - 1))‖
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  unfold QdotN
  rw [← smul_sub, norm_smul]

/-- `Q̇` for a general `T` is symmetric. -/
private lemma qdot_QdotNT_herm {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) : (QdotNT T Xm).IsHermitian := by
  have hS : (Tᵀ * T).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian
  unfold QdotNT QN
  exact (XSX_isHermitian hS (Xdot Xm)).smul (IsSelfAdjoint.all _)

/-- `Xm ↦ Q̇` for a general `T` is measurable along a measurable `X`. -/
private lemma qdot_measurable_T {Ω : Type*} [MeasureSpace Ω] {K : ℕ}
    (T : Matrix (Fin M) (Fin K) ℝ) {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : Measurable X) :
    Measurable fun ω => QdotNT T (X ω) := by
  have hc : Continuous fun Xm : Matrix (Fin K) (Fin N) ℝ => QdotNT T Xm := by
    have h1 : Continuous fun Xm : Matrix (Fin K) (Fin N) ℝ => Xm * piBar N :=
      continuous_id.matrix_mul continuous_const
    have h2 : Continuous fun Xm : Matrix (Fin K) (Fin N) ℝ =>
        (Xm * piBar N)ᵀ * (Tᵀ * T) * (Xm * piBar N) :=
      (h1.matrix_transpose.matrix_mul continuous_const).matrix_mul h1
    unfold QdotNT QN Xdot
    exact h2.const_smul ((N : ℝ) / (N - 1))
  exact hc.measurable.comp hX

/-- The vectors `q_{l_n,l}(A_n)` built from the data `σ_n` converge to `q_{k,l}(A)` built from
`σ` when the sign and the indices agree, the edges and the scales converge (the limit scale is
nonzero), and `‖A_n - A‖ → 0`. -/
private lemma qdot_qVecA_tendsto {K M' n : ℕ} {σs : ℕ → Fin K → ℝ} {ls : ℕ → ℕ}
    {σ : Fin M' → ℝ} {k l : ℕ} {As : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hAs : ∀ m, (As m).IsHermitian) (hA : A.IsHermitian)
    (hsign : ∀ m, edgeSign (ls m) = edgeSign k)
    (hidx : ∀ m i, edgeIdx N (σs m) (ls m) i = edgeIdx N σ k i)
    (hval : Tendsto (fun m => edgeVal N (σs m) (ls m)) atTop (𝓝 (edgeVal N σ k)))
    (hscale : Tendsto (fun m => edgeScale N (σs m) (ls m)) atTop (𝓝 (edgeScale N σ k)))
    (hϖ : edgeScale N σ k ≠ 0) (hconv : Tendsto (fun m => ‖As m - A‖) atTop (𝓝 0)) :
    Tendsto (fun m => qVecA N (σs m) (As m) (ls m) l) atTop (𝓝 (qVecA N σ A k l)) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  unfold qVecA
  simp_rw [hsign, hidx]
  have heig : Tendsto (fun m => sortedEig (As m) (edgeIdx N σ k (i + 1))) atTop
      (𝓝 (sortedEig A (edgeIdx N σ k (i + 1)))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun m => dist_nonneg)
      (fun m => by rw [Real.dist_eq]; exact sortedEig_lipschitz (hAs m) hA _) hconv
  exact (tendsto_const_nhds.div hscale hϖ).mul (heig.sub hval)

/-- `q_{k,l}` depends on `σ` only through its nonzero values with multiplicity. -/
private lemma qdot_qVecA_nzEq {K n : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k l : ℕ) : qVecA N σ' A k l = qVecA N σ A k l := by
  funext i
  unfold qVecA edgeIdx
  rw [h.cumCount_eq N, h.edgeVal_eq N, h.edgeScale_eq N]

/-- Dominated convergence on a probability space with a constant bound. -/
private lemma qdot_integral_tendsto {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {B : ℝ}
    (hF : ∀ m, Measurable (F m)) (hB : ∀ m ω, |F m ω| ≤ B)
    (hlim : ∀ ω, Tendsto (fun m => F m ω) atTop (𝓝 (f ω))) :
    Tendsto (fun m => ∫ ω, F m ω) atTop (𝓝 (∫ ω, f ω)) :=
  tendsto_integral_of_dominated_convergence (fun _ => B) (fun m => (hF m).aestronglyMeasurable)
    (integrable_const B)
    (fun m => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB m ω)
    (Eventually.of_forall hlim)

/-- Equal signs `edgeSign` mean equal parities. -/
private lemma qdot_mod_two_of_edgeSign {a b : ℕ} (h : edgeSign a = edgeSign b) :
    a % 2 = b % 2 := by
  unfold edgeSign at h
  split_ifs at h with h1 h2 h2 <;> first | omega | norm_num at h

/-- Theorem 11.4 for a general `T` (§11.1), bounded Lipschitz `h`, with rate, at the partner
edge of `Σ = T Tᵀ`. -/
theorem edge_univ_dotT_lip (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ K₀ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ)
      (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
        |(∫ ω, h (qDotVecT T (X ω) (edgePartner N (specOf (T * Tᵀ)) k) l)) -
            bRef (N - 1) (specOf (T * Tᵀ)) (edgePartner N (specOf (T * Tᵀ)) k) l h| ≤
          K₀ * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  have hτ3 : 0 < τ ^ 3 := pow_pos hτ 3
  have hτE : 0 < tauE τ := lt_min hτ3 (by linarith)
  have hτ2 : 0 < τ / 2 := by linarith
  have hτE2 : 0 < tauE (τ / 2) := lt_min (pow_pos hτ2 3) (by linarith)
  obtain ⟨K₁, N₁, h₁⟩ := edge_univ_dot_lip (tauE τ) C l hτE
  obtain ⟨C₁, N₂, h₂⟩ := edgePartner_spec τ hτ
  refine ⟨K₁, max (max N₁ N₂) (⌈8 * |C₁| / tauE (τ / 2)⌉₊ + 2), ?_⟩
  intro N hN Ω _ _ M K T X k hm hk h B L hB hL
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : ⌈8 * |C₁| / tauE (τ / 2)⌉₊ + 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN7 : 2 ≤ N := by omega
  have hNp : 1 ≤ N := by omega
  have hNp' : 1 ≤ N - 1 := by omega
  set tE := tauE (τ / 2) with htE
  set k' := edgePartner N (specOf (T * Tᵀ)) k with hk'
  have hda := hm.densityAssumptions hτ
  have hda' := densityAssumptions_pred hda hN7
  obtain ⟨hpar, hdist, hk'reg⟩ := h₂ N hN2 M (specOf (T * Tᵀ)) hda k hk
  have hratio' : (K : ℝ) / ((N - 1 : ℕ) : ℝ) ≤ (τ / 2)⁻¹ := by
    have h0 := hm.ratioK_le
    have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN7
    have hτi : (τ / 2)⁻¹ = 2 * τ⁻¹ := by rw [inv_div]; field_simp
    rw [hc, hτi, div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (by linarith)] at h0
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    nlinarith
  have hC₁ : C₁ / N ≤ tE / 8 := by
    have hc := Nat.le_ceil (8 * |C₁| / tE)
    have hN' : ((⌈8 * |C₁| / tE⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN3
    push_cast at hN'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h8 : 8 * |C₁| / tE < N := by linarith
    have h8' : 8 * |C₁| < N * tE := (div_lt_iff₀ hτE2).1 h8
    rw [div_le_iff₀ hNpos]
    linarith [le_abs_self C₁]
  -- a sequence `κ_n ↓ 0`, with edges `l''_n` (for `N` samples) and `l_n` (for `N − 1` samples)
  -- of `Ŝ + κ_n P₀` whose data converge to those of `k` and of its partner `k'`
  have hseq : ∀ n : ℕ, ∃ κ : ℝ, ∃ l'' : ℕ, ∃ l' : ℕ, 0 < κ ∧ κ ≤ τ ^ 3 ∧
      κ < 1 / ((n : ℝ) + 1) ∧
      RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l'' ∧ edgeSign l'' = edgeSign k ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l'' - edgeVal N (specOf (T * Tᵀ)) k| ≤
        min (1 / ((n : ℝ) + 1)) (tE / 16) ∧
      RegularEdge tE (N - 1) (specOf (regS κ (Tᵀ * T))) l' ∧ edgeSign l' = edgeSign k' ∧
      (∀ i, edgeIdx (N - 1) (specOf (regS κ (Tᵀ * T))) l' i =
        edgeIdx (N - 1) (specOf (T * Tᵀ)) k' i) ∧
      |edgeVal (N - 1) (specOf (regS κ (Tᵀ * T))) l' - edgeVal (N - 1) (specOf (T * Tᵀ)) k'| ≤
        min (1 / ((n : ℝ) + 1)) (tE / 16) ∧
      |edgeScale (N - 1) (specOf (regS κ (Tᵀ * T))) l' -
        edgeScale (N - 1) (specOf (T * Tᵀ)) k'| ≤ min (1 / ((n : ℝ) + 1)) (tE / 16) := by
    intro n
    have hδ : 0 < min (1 / ((n : ℝ) + 1)) (tE / 16) := lt_min (by positivity) (by positivity)
    have ev1 := regS_edge_transfer hτ hNp hda hm.ratioK_le hk hδ
    have ev2 := regS_edge_transfer hτ2 hNp' hda' hratio' hk'reg hδ
    have ev3 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 ∧ κ < 1 / ((n : ℝ) + 1) := by
      have e1 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ := self_mem_nhdsWithin
      have e2 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ < min (τ ^ 3) (1 / ((n : ℝ) + 1)) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hτ3 (by positivity)))
      filter_upwards [e1, e2] with κ hκ1 hκ2
      exact ⟨hκ1, (lt_of_lt_of_le hκ2 (min_le_left _ _)).le,
        lt_of_lt_of_le hκ2 (min_le_right _ _)⟩
    obtain ⟨κ, ⟨h1, h2, h3⟩, ⟨l'', hl1, hl2, -, hl4, -⟩, ⟨l', hm1, hm2, hm3, hm4, hm5⟩⟩ :=
      (ev3.and (ev1.and ev2)).exists
    exact ⟨κ, l'', l', h1, h2, h3, hl1, hl2, hl4, hm1, hm2, hm3, hm4, hm5⟩
  choose κs l2s ls hκ0 hκτ hκn hreg2 hsign2 hval2 hreg hsign hidx hval hscale using hseq
  -- the partner of `l''_n` for `Ŝ + κ_n P₀` is `l_n`
  have hpart : ∀ n, edgePartner N (specOf (regS (κs n) (Tᵀ * T))) (l2s n) = ls n := by
    intro n
    have hpar' : ls n % 2 = l2s n % 2 := by
      have e1 := qdot_mod_two_of_edgeSign (hsign n)
      have e2 := qdot_mod_two_of_edgeSign (hsign2 n)
      omega
    have hr : |edgeVal (N - 1) (specOf (regS (κs n) (Tᵀ * T))) (ls n) -
        edgeVal N (specOf (regS (κs n) (Tᵀ * T))) (l2s n)| ≤ tE / 4 := by
      have a1 := abs_le.1 ((hval n).trans (min_le_right _ _))
      have a2 := abs_le.1 hdist
      have a3 := abs_le.1 ((hval2 n).trans (min_le_right _ _))
      rw [abs_le]
      constructor <;> linarith
    exact edgePartner_eq (hreg n) hpar' hr (by linarith)
  -- the bound of Theorem 11.4 under (T_diag) for `(Ŝ + κ_n P₀, X)` at `τ_E`
  have hbd : ∀ n, |(∫ ω, h (qDotVec (regS (κs n) (Tᵀ * T)) (X ω) (ls n) l)) -
      bRef (N - 1) (specOf (regS (κs n) (Tᵀ * T))) (ls n) l h| ≤
        K₁ * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := fun n => by
    have := h₁ N hN1 K (regS (κs n) (Tᵀ * T)) X (l2s n)
      ((isModel_regS hτ hm (hκ0 n) (hκτ n)).mono hτE (min_le_left _ _)) (hreg2 n) h B L hB hL
    rwa [hpart n] at this
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hκlim : Tendsto κs atTop (𝓝 0) :=
    squeeze_zero (fun n => (hκ0 n).le) (fun n => (hκn n).le) h1n
  have hval' : Tendsto (fun n => edgeVal (N - 1) (specOf (regS (κs n) (Tᵀ * T))) (ls n)) atTop
      (𝓝 (edgeVal (N - 1) (specOf (T * Tᵀ)) k')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => by rw [Real.dist_eq]; exact (hval n).trans (min_le_left _ _)) h1n
  have hscale' : Tendsto (fun n => edgeScale (N - 1) (specOf (regS (κs n) (Tᵀ * T))) (ls n))
      atTop (𝓝 (edgeScale (N - 1) (specOf (T * Tᵀ)) k')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => by rw [Real.dist_eq]; exact (hscale n).trans (min_le_left _ _)) h1n
  have hϖ : edgeScale (N - 1) (specOf (T * Tᵀ)) k' ≠ 0 := (edgeScale_bounds hda' hk'reg).1.ne'
  have hPS : (Tᵀ * T).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hSH := hPS.isHermitian
  have hnz := nzEq_specOf_mul_transpose T
  have hRH : ∀ n, (regS (κs n) (Tᵀ * T)).IsHermitian := fun n =>
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ _)
  have hnorm : ∀ n, ‖regS (κs n) (Tᵀ * T) - Tᵀ * T‖ ≤ κs n := fun n =>
    regS_norm_sub_le (hκ0 n).le hPS
  have hhm : Measurable h := hL.continuous.measurable
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  -- the model side: `E h(q̇^{κ_n}) → E h(q̇)`
  have hmodel : Tendsto (fun n => ∫ ω, h (qDotVec (regS (κs n) (Tᵀ * T)) (X ω) (ls n) l)) atTop
      (𝓝 (∫ ω, h (qDotVecT T (X ω) k' l))) := by
    refine qdot_integral_tendsto (B := B) (fun n => ?_) (fun n ω => hB _) (fun ω => ?_)
    · have := qdot_measurable (regS (κs n) (Tᵀ * T)) 1 hXm
      simp only [one_smul] at this
      exact hhm.comp ((measurable_qVecA _ _ _ _ _).comp this)
    · have hconv := qdot_QdotN_tendsto hnorm hκlim (X ω)
      exact (hL.continuous.tendsto _).comp
        (qdot_qVecA_tendsto (fun n => by simpa using qdot_isHermitian (hRH n) 1 (X ω))
          (qdot_QdotNT_herm T (X ω)) hsign hidx hval' hscale' hϖ hconv)
  -- the reference side: `b_{N−1}(h, spec(Ŝ + κ_n P₀)) → b_{N−1}(h, spec Σ)`
  have hσ' : ∀ j, 0 ≤ specOf (Tᵀ * T) j := fun j => by
    rw [specOf_eq hSH]
    exact hPS.eigenvalues_nonneg j
  have hdiag : ∀ n, ‖diagonal (specOf (regS (κs n) (Tᵀ * T))) - diagonal (specOf (Tᵀ * T))‖ ≤
      κs n := by
    intro n
    rw [diagonal_sub, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (hκ0 n).le).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact (qdot_specOf_lipschitz (hRH n) hSH j).trans (hnorm n)
  have hGm : Measurable (gaussX K (N - 1)) := (gaussX_isGaussianEnsemble K (N - 1)).measurable_mat
  have hlimref : bRef (N - 1) (specOf (T * Tᵀ)) k' l h = ∫ ω, h (qVecA (N - 1) (specOf (T * Tᵀ))
      (QN (diagonal (specOf (Tᵀ * T))) (gaussX K (N - 1) ω)) k' l) := by
    rw [bRef_nzEq hnz hda.nonneg hσ' (N - 1) k' l hhm]
    unfold bRef
    simp_rw [qdot_qVecA_nzEq hnz]
  have href : Tendsto (fun n => bRef (N - 1) (specOf (regS (κs n) (Tᵀ * T))) (ls n) l h) atTop
      (𝓝 (bRef (N - 1) (specOf (T * Tᵀ)) k' l h)) := by
    rw [hlimref]
    unfold bRef
    refine qdot_integral_tendsto (B := B)
      (fun n => hhm.comp ((measurable_qVecA _ _ _ _ _).comp ((qdot_measurable_QN _).comp hGm)))
      (fun n ω => hB _) (fun ω => ?_)
    exact (hL.continuous.tendsto _).comp
      (qdot_qVecA_tendsto (fun n => qdot_QN_herm (isHermitian_diagonal _) _)
        (qdot_QN_herm (isHermitian_diagonal _) _) hsign hidx hval' hscale' hϖ
        (qdot_QN_tendsto hdiag hκlim _))
  exact le_of_tendsto' (hmodel.sub href).abs hbd

/-- Theorem 11.4 for a general `T`, bounded uniformly continuous `h`, at the partner edge. -/
theorem edge_univ_dotT (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ)
    (hτ : 0 < τ) (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      |(∫ ω, h (qDotVecT T (X ω) (edgePartner N (specOf (T * Tᵀ)) k) l)) -
          bRef (N - 1) (specOf (T * Tᵀ)) (edgePartner N (specOf (T * Tᵀ)) k) l h| ≤ ε := by
  obtain ⟨B, hB⟩ := hb
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, L, hgL, hgB, hhg⟩ := exists_lipschitz_approx hB hu hε3
  obtain ⟨K₀, N₀, hK⟩ := edge_univ_dotT_lip τ C l hτ
  obtain ⟨N₁, hN₁⟩ := qdot_rate_eventually K₀ B L l hε3
  refine ⟨max N₀ N₁, fun N hN Ω _ _ M K T X k hm hk => ?_⟩
  set k' := edgePartner N (specOf (T * Tᵀ)) k with hk'
  have hhm : Measurable h := hu.continuous.measurable
  have hgm : Measurable g := hgL.continuous.measurable
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M (N - 1)) :=
    (gaussX_isGaussianEnsemble M (N - 1)).measurable_mat
  have hY : Measurable fun ω => qDotVecT T (X ω) k' l :=
    (measurable_qVecA (N - 1) (specOf (T * Tᵀ)) N k' l).comp (qdot_measurable_T T hXm)
  have hY0 : Measurable fun ω => qVecA (N - 1) (specOf (T * Tᵀ))
      (QN (diagonal (specOf (T * Tᵀ))) (gaussX M (N - 1) ω)) k' l :=
    (measurable_qVecA (N - 1) (specOf (T * Tᵀ)) (N - 1) k' l).comp
      ((qdot_measurable_QN _).comp hGm)
  have e1 := qdot_integral_sub_le hY hhm hgm hB hgB hhg
  have e2 := (hK N (le_of_max_le_left hN) M K T X k hm hk g B L hgB hgL).trans
    (hN₁ N (le_of_max_le_right hN))
  have e3 : |bRef (N - 1) (specOf (T * Tᵀ)) k' l g - bRef (N - 1) (specOf (T * Tᵀ)) k' l h| ≤
      ε / 3 := by
    unfold bRef
    exact qdot_integral_sub_le hY0 hgm hhm hgB hB (fun x => by rw [abs_sub_comm]; exact hhg x)
  have := abs_add_three ((∫ ω, h (qDotVecT T (X ω) k' l)) - ∫ ω, g (qDotVecT T (X ω) k' l))
    ((∫ ω, g (qDotVecT T (X ω) k' l)) - bRef (N - 1) (specOf (T * Tᵀ)) k' l g)
    (bRef (N - 1) (specOf (T * Tᵀ)) k' l g - bRef (N - 1) (specOf (T * Tᵀ)) k' l h)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at this
  linarith

/-- Theorem 11.4, the paper's form: there is `b_N(h, π)`, depending only on `N` and the
nonzero eigenvalues of `Σ` with multiplicity, such that `E h(q̇) − b_N(h, π) → 0` along every
sequence of models with `N → ∞` and the edge `k_n` regular, `q̇` taken at the partner edge. -/
example (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) :
    ∃ b : (N : ℕ) → (M : ℕ) → (Fin M → ℝ) → ℕ → ℝ,
      (∀ (N M M' : ℕ) (σ : Fin M → ℝ) (σ' : Fin M' → ℝ) (k : ℕ), NzEq σ σ' →
          (∀ i, 0 ≤ σ i) → (∀ j, 0 ≤ σ' j) → b N M σ k = b N M' σ' k) ∧
      ∀ (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
        (Ms Ns : ℕ → ℕ) (Sig : ∀ n, Matrix (Fin (Ms n)) (Fin (Ms n)) ℝ)
        (X : ∀ n, Ω n → Matrix (Fin (Ms n)) (Fin (Ns n)) ℝ) (k : ℕ → ℕ),
        Tendsto Ns atTop atTop →
        (∀ n, IsModel τ C (Ms n) (Ns n) (Sig n) (X n)) →
        (∀ n, RegularEdge τ (Ns n) (specOf (Sig n)) (k n)) →
        Tendsto (fun n => (∫ ω, h (qDotVec (Sig n) (X n ω)
          (edgePartner (Ns n) (specOf (Sig n)) (k n)) l)) -
          b (Ns n) (Ms n) (specOf (Sig n)) (k n)) atTop (𝓝 0) := by
  refine ⟨fun N M σ k => bRef (N - 1) σ (edgePartner N σ k) l h,
    fun N M M' σ σ' k hz hσ hσ' => ?_, ?_⟩
  · simp only
    rw [hz.edgePartner_eq N k]
    exact bRef_nzEq hz hσ hσ' (N - 1) _ l hu.continuous.measurable
  intro Ω _ _ Ms Ns Sig X k hNs hm hk
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := edge_univ_dot τ C l h (ε / 2) hτ hb hu (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hNs.eventually_ge_atTop N₀)
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hN₀ (Ns n) (hn₀ n hn) (Ms n) (Sig n) (X n) (k n) (hm n) (hk n)).trans_lt
    (half_lt_self hε)

/-- The clamp `x ↦ max(-1, min(x₁, 1))` is bounded by `1` and `1`-Lipschitz. -/
private theorem qdot_clamp_bounded_lipschitz :
    (∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1) ∧
      LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  refine ⟨fun x => abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩, ?_⟩
  exact ((LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).min_const 1).const_max (-1)

/-- Theorem 11.4 for a general `T` at `T = tPad n` (`M = 2n`, `K = n`, `N = 2n`,
`Σ = diag(I_n, 0)` singular), Rademacher `X`, for the clamp of the top eigenvalue: every
hypothesis is discharged. -/
example : ∃ K₀ : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qDotVecT (tPad n) (radXn n ω)
        (edgePartner (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) 1 0) 1)) -
        bRef (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ))
          (edgePartner (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) 1
          (fun x => max (-1) (min (x 0) 1))| ≤
      K₀ * (1 + 1) * ((2 * n : ℕ) : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨K₀, N₀, h⟩ := edge_univ_dotT_lip (1 / 5) (fun _ => 1) 1 (by norm_num)
  refine ⟨K₀, N₀, fun n hn hN => ?_⟩
  have := h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn) (mpT_hyps hn).2.2.1
    (fun x => max (-1) (min (x 0) 1)) 1 1 qdot_clamp_bounded_lipschitz.1
    qdot_clamp_bounded_lipschitz.2
  simpa using this

/-- The constants of the reduction for Theorem 11.4 (`ε = 1/200`, `c₁ = 1/24`, the rate
`1/(800(l+1))` at `N − 1` samples) satisfy its side conditions, and the rate at `N − 1` costs at
most a factor `2` at `N`. -/
example (l : ℕ) (N : ℕ) (hN : 2 ≤ N) :
    (0 : ℝ) < 1 / 200 ∧ (1 / 200 : ℝ) ≤ 1 / 6 - 25 * (1 / 200) ∧
      (1 / 200 : ℝ) / (4 * (l + 1)) = 1 / (800 * (l + 1)) ∧
      9 * (1 / 200 : ℝ) + 1 / 6 < 1 / 3 ∧ (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) ∧
      ((N - 1 : ℕ) : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤
        2 * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  have hl : (0 : ℝ) < l + 1 := by positivity
  refine ⟨by norm_num, by norm_num, by field_simp; ring, by norm_num, ?_, ?_⟩
  · have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hc]; linarith
  · exact qdot_rpow_pred_le hN (by positivity) (by rw [div_le_one (by positivity)]; nlinarith)

/-! ## Instances -/

/-- An isometry onto `1^⊥` for `N = 3`. -/
example : ∃ P : Matrix (Fin 3) (Fin (3 - 1)) ℝ, Pᵀ * P = 1 ∧ P * Pᵀ = piBar 3 :=
  exists_piBar_isometry (by norm_num)

/-- The Gaussian `2 × 3` ensemble against an isometry onto `1^⊥` of `ℝ³`: `(3/2)^{1/2} X P` is a
Gaussian `2 × 2` ensemble. -/
example : ∃ P : Matrix (Fin 3) (Fin (3 - 1)) ℝ, Pᵀ * P = 1 ∧
    IsGaussianEnsemble (fun ω => Real.sqrt (((3 : ℕ) : ℝ) / ((3 - 1 : ℕ) : ℝ)) •
      (gaussX 2 3 ω * P)) := by
  obtain ⟨P, hP, -⟩ := exists_piBar_isometry (N := 3) (by norm_num)
  exact ⟨P, hP, (gaussX_isGaussianEnsemble 2 3).mul_isometry hP⟩

/-- `Σ = I_4`, `N = 3`: the ordered eigenvalues of the companion of `Q̇` are those of
`Q_2 = Yᵀ Y`, `Y = (3/2)^{1/2} X P`, for every `X` and every index. -/
example : ∃ P : Matrix (Fin 3) (Fin (3 - 1)) ℝ, Pᵀ * P = 1 ∧ P * Pᵀ = piBar 3 ∧
    ∀ (Xm : Matrix (Fin 4) (Fin 3) ℝ) (j : ℕ),
      sortedEig (QdotN (1 : Matrix (Fin 4) (Fin 4) ℝ) Xm) j =
        sortedEig (QN 1 (Real.sqrt (((3 : ℕ) : ℝ) / ((3 - 1 : ℕ) : ℝ)) • (Xm * P))) j := by
  obtain ⟨P, hP, hPP⟩ := exists_piBar_isometry (N := 3) (by norm_num)
  exact ⟨P, hP, hPP, fun Xm j =>
    sortedEig_QdotN_isometry Matrix.PosDef.one.posSemidef (by norm_num) hP hPP Xm j⟩

/-- The reference value of Theorem 11.4 at `Σ = I_4`, `N = 3`, for the clamp of the top
rescaled eigenvalue: the Gaussian expectation equals `b_2`. -/
example : ∫ ω, max (-1) (min (qDotVec (1 : Matrix (Fin 4) (Fin 4) ℝ) (gaussX 4 3 ω) 1 1 0) 1) =
    bRef (3 - 1) (specOf (1 : Matrix (Fin 4) (Fin 4) ℝ)) 1 1 (fun x => max (-1) (min (x 0) 1)) :=
  integral_qDotVec_gauss Matrix.PosDef.one (by norm_num) 1 1
    qdot_clamp_bounded_lipschitz.2.continuous.measurable

/-- `Σ = I_{2n}` with `N = n` is regular at both edges at `τ = 1/20`. -/
private lemma qdot_regularEdge_two {n : ℕ} (hn : 0 < n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    RegularEdge (1 / 20) n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k := by
  rw [specOf_one_eq]
  have h := regularEdge_two hn hk1 hk2
  norm_num at h ⊢
  exact h

/-- Theorem 11.4 under (T_diag) at `Σ = I_{2n}`, `N = n` (rank `Σ ≥ N`), Gaussian `X`,
`τ = 1/20`, at the bottom edge `k = 2`, for the clamp of the first rescaled eigenvalue: every
hypothesis is discharged. -/
example : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ n →
    |(∫ ω, max (-1) (min (qDotVec (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (gaussX (2 * n) n ω)
        (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2) 1 0) 1)) -
        bRef (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
          (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2) 1
          (fun x => max (-1) (min (x 0) 1))| ≤
      K * (1 + 1) * (n : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨K, N₀, h⟩ := edge_univ_dot_lip (1 / 20) gaussMoment 1 (by norm_num)
  refine ⟨K, N₀, fun n hn hN => ?_⟩
  have := h n hN (2 * n) 1 (gaussX (2 * n) n) 2
    ((isModel_two hn).mono (by norm_num) (by norm_num))
    (qdot_regularEdge_two hn (by norm_num) le_rfl)
    (fun x => max (-1) (min (x 0) 1)) 1 1 qdot_clamp_bounded_lipschitz.1
    qdot_clamp_bounded_lipschitz.2
  simpa using this

/-- Theorem 11.4 under (T_diag) and bounded uniformly continuous `h` at `Σ = I_{2n}`, `N = n`,
Gaussian `X`, `τ = 1/20`, the top edge `k = 1`, for the clamp of the top rescaled eigenvalue and
the precision `ε = 1/10`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ n →
    |(∫ ω, max (-1) (min (qDotVec (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (gaussX (2 * n) n ω)
        (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1) 1 0) 1)) -
        bRef (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
          (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1) 1
          (fun x => max (-1) (min (x 0) 1))| ≤ 1 / 10 := by
  obtain ⟨N₀, h⟩ := edge_univ_dot (1 / 20) gaussMoment 1 (fun x => max (-1) (min (x 0) 1))
    (1 / 10) (by norm_num) ⟨1, qdot_clamp_bounded_lipschitz.1⟩
    qdot_clamp_bounded_lipschitz.2.uniformContinuous (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  exact h n hN (2 * n) 1 (gaussX (2 * n) n) 1
    ((isModel_two hn).mono (by norm_num) (by norm_num))
    (qdot_regularEdge_two hn le_rfl (by norm_num))

/-- The sequence hypotheses of the paper's form hold together along the family
`Σ_n = I_{2(n+1)}`, `N_n = n + 1`, Gaussian entries, `k_n = 1`, `τ = 1/20`, `C = gaussMoment`. -/
example :
    Tendsto (fun n : ℕ => n + 1) atTop atTop ∧
      (∀ n : ℕ, IsModel (1 / 20) gaussMoment (2 * (n + 1)) (n + 1)
        (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ) (gaussX (2 * (n + 1)) (n + 1))) ∧
      ∀ n : ℕ, RegularEdge (1 / 20) (n + 1)
        (specOf (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ)) 1 :=
  ⟨tendsto_add_atTop_nat 1, fun n => (isModel_two (by omega)).mono (by norm_num) (by norm_num),
    fun n => qdot_regularEdge_two n.succ_pos le_rfl (by norm_num)⟩

/-- Theorem 11.4 for a general `T` and bounded uniformly continuous `h` at `T = tPad n`
(`M = 2n`, `K = n`, `N = 2n`, `Σ` singular), Rademacher `X`, for the clamp of the top rescaled
eigenvalue and the precision `ε = 1/10`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qDotVecT (tPad n) (radXn n ω)
        (edgePartner (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) 1 0) 1)) -
        bRef (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ))
          (edgePartner (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) 1
          (fun x => max (-1) (min (x 0) 1))| ≤ 1 / 10 := by
  obtain ⟨N₀, h⟩ := edge_univ_dotT (1 / 5) (fun _ => 1) 1 (fun x => max (-1) (min (x 0) 1))
    (1 / 10) (by norm_num) ⟨1, qdot_clamp_bounded_lipschitz.1⟩
    qdot_clamp_bounded_lipschitz.2.uniformContinuous (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  exact h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn) (mpT_hyps hn).2.2.1

#print axioms exists_piBar_isometry
#print axioms IsGaussianEnsemble.mul_isometry
#print axioms sortedEig_QdotN_isometry
#print axioms integral_qDotVec_gauss
#print axioms edge_univ_dot_lip
#print axioms edge_univ_dot
#print axioms edge_univ_dotT_lip
#print axioms edge_univ_dotT

end Anisotropic
