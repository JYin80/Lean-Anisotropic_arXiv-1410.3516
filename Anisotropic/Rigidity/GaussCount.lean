import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Probability.NormBound.Main
import Anisotropic.Rigidity.Deform
import Anisotropic.Rigidity.DeformFacts
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Gap
import Anisotropic.Rigidity.Interp
import Anisotropic.Rigidity.MinMax

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 10.4, the bottom count and Proposition 10.2 -/

/-! ## Elementary facts -/

/-- `R = φ π((0,∞))` is a symmetric function of `σ`. -/
private lemma gc_massRatio_perm (N : ℕ) (σ : Fin M → ℝ) (e : Equiv.Perm (Fin M)) :
    massRatio N (σ ∘ e) = massRatio N σ := by
  unfold massRatio
  congr 2
  exact Finset.card_equiv e (by simp)

/-- `ϱ` is a symmetric function of `σ`. -/
private lemma gc_varrho_perm (N : ℕ) (σ : Fin M → ℝ) (e : Equiv.Perm (Fin M)) :
    varrho N (σ ∘ e) = varrho N σ := by
  have hm : mFun N (σ ∘ e) = mFun N σ := funext (mFun_comp_perm N σ e)
  have hx : mExt N (σ ∘ e) = mExt N σ := by
    funext z
    unfold mExt
    rw [hm]
  have hr : rhoDens N (σ ∘ e) = rhoDens N σ := by
    funext x
    unfold rhoDens
    rw [hx]
  unfold varrho
  rw [hr, gc_massRatio_perm]

/-- `ϱ` for `diag(v)` is `ϱ` for `v`. -/
private lemma gc_varrho_specOf_diagonal (N : ℕ) (v : Fin M → ℝ) :
    varrho N (specOf (diagonal v)) = varrho N v := by
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal v
  rw [he, gc_varrho_perm]

/-- `Σ(1) = Σ`. -/
private lemma gc_sig_one (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : deformSig N σ k 1 = σ := by
  funext i
  unfold deformSig
  split_ifs <;> simp

/-- `Xᵀ diag(v) X` is symmetric. -/
private lemma gc_QN_herm (v : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) :
    (QN (diagonal v) Xm).IsHermitian := by
  unfold QN Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- With no eigenvalue in `[a, b]`, the counts at `a` and `b` agree. -/
private lemma gc_eigCount_eq {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ i, specOf A i ∉ Set.Icc a b) : eigCount A a = eigCount A b := by
  unfold eigCount
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hi
    by_contra hlt
    exact h i ⟨hi, (not_le.1 hlt).le⟩
  · intro hi
    linarith

/-- `C_x > 0`. -/
private lemma gc_Cx_pos {τ τg : ℝ} (hτ : 0 < τ) (hτg : 0 < τg) : 0 < gapCx τ τg := by
  have hκ : 0 < kappaMax τ := by unfold kappaMax; positivity
  unfold gapCx mBoundConst genPropConst
  have h1 : 0 < min (τg / 2) (kappaMax τ)⁻¹ := lt_min (by linarith) (inv_pos.mpr hκ)
  positivity

/-- The edges are ordered: `a_{m+j} ≤ a_m`. -/
private lemma gc_edge_chain (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (j : ℕ) {m : ℕ} (hm : 1 ≤ m) (hmj : m + j ≤ 2 * numBands N σ) :
    edgeVal N σ (m + j) ≤ edgeVal N σ m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := edgeVal_succ_le N σ hσ hN hS (k := m + j) (by omega) (by omega)
    rw [← add_assoc]
    linarith

/-! ## Rotation invariance of the Gaussian ensemble -/

/-- The entries of a matrix as a point of `GaussSpace`. -/
private def gc_flat (A : Matrix (Fin M) (Fin N) ℝ) : GaussSpace M N := fun p => A p.1 p.2

private lemma gc_measurable_flat : Measurable (gc_flat : Matrix (Fin M) (Fin N) ℝ → _) :=
  measurable_pi_iff.2 fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- `ω ↦ O X(ω)` in coordinates. -/
private def gc_rot (O : Matrix (Fin M) (Fin M) ℝ) (ω : GaussSpace M N) : GaussSpace M N :=
  gc_flat (O * gaussX M N ω * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ)

private lemma gc_gaussX_rot (O : Matrix (Fin M) (Fin M) ℝ) (ω : GaussSpace M N) :
    gaussX M N (gc_rot O ω) = O * gaussX M N ω := by
  ext i μ
  simp [gc_rot, gc_flat, gaussX]

private lemma gc_measurable_rot (O : Matrix (Fin M) (Fin M) ℝ) :
    Measurable (gc_rot (N := N) O) :=
  gc_measurable_flat.comp
    (measurable_rotate (gaussX_isGaussianEnsemble M N).measurable_mat O 1)

private lemma gc_rot_rot {O O' : Matrix (Fin M) (Fin M) ℝ} (h : O' * O = 1)
    (ω : GaussSpace M N) : gc_rot O' (gc_rot O ω) = ω := by
  change gc_flat (O' * gaussX M N (gc_rot O ω) * _) = ω
  rw [gc_gaussX_rot, ← Matrix.mul_assoc, h, transpose_one, Matrix.mul_one, Matrix.one_mul]
  rfl

private lemma gc_rot_preserving {O : Matrix (Fin M) (Fin M) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin M) ℝ) :
    MeasurePreserving (gc_rot (N := N) O) ℙ ℙ := by
  refine ⟨gc_measurable_rot O, ?_⟩
  have hG := gaussX_isGaussianEnsemble M N
  have h1 : gc_rot (N := N) O =
      gc_flat ∘ fun ω => O * gaussX M N ω * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ := rfl
  have h2 : (gc_flat ∘ gaussX M N) = id := rfl
  rw [h1, ← Measure.map_map gc_measurable_flat
    (measurable_rotate hG.measurable_mat O 1),
    hG.map_rotate hO (one_mem _), Measure.map_map gc_measurable_flat
    hG.measurable_mat, h2, Measure.map_id]

/-- For Gaussian `X`, every event of `Q_N(Σ)` has the probability of the same event of
`Q_N(D(Σ))`, `D(Σ) = diag(specOf Σ)` (rotation invariance). -/
private lemma gc_rotate {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (P : Matrix (Fin N) (Fin N) ℝ → Prop) :
    (ℙ : Measure (GaussSpace M N)) {ω | P (QN Sig (gaussX M N ω))} =
      ℙ {ω | P (QN (diagonal (specOf Sig)) (gaussX M N ω))} := by
  have hH : Sig.IsHermitian := hSig.isHermitian
  set U : Matrix (Fin M) (Fin M) ℝ := (hH.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℝ)
    with hU
  have hsm : star U * U = 1 := Unitary.coe_star_mul_self _
  have hms : U * star U = 1 := Unitary.coe_mul_star_self _
  rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hsm hms
  have hdec : Sig = U * diagonal hH.eigenvalues * Uᵀ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [← conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
    simpa [hU] using this
  have hOt : Uᵀ ∈ Matrix.orthogonalGroup (Fin M) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, transpose_transpose, hsm]
  let e : GaussSpace M N ≃ᵐ GaussSpace M N :=
    { toFun := gc_rot Uᵀ
      invFun := gc_rot U
      left_inv := gc_rot_rot hms
      right_inv := gc_rot_rot hsm
      measurable_toFun := gc_measurable_rot _
      measurable_invFun := gc_measurable_rot _ }
  have hpres : MeasurePreserving e ℙ ℙ := gc_rot_preserving hOt
  have hset : {ω | P (QN Sig (gaussX M N ω))} =
      e ⁻¹' {ω | P (QN (diagonal (specOf Sig)) (gaussX M N ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have : QN (diagonal (specOf Sig)) (gaussX M N (e ω)) = QN Sig (gaussX M N ω) := by
      change QN _ (gaussX M N (gc_rot Uᵀ ω)) = _
      rw [gc_gaussX_rot, specOf_eq hH]
      conv_rhs => rw [QN, hdec]
      rw [QN, transpose_mul, transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [this]
  rw [hset, hpres.measure_preimage_equiv]

/-! ## Sub-ensembles of the Gaussian ensemble -/

/-- Entries of `gaussX` taken along an injective index map and multiplied by `c`, with
`c² / N = 1/b`, form a Gaussian `a × b` ensemble. -/
private lemma gc_sub_gauss {a b : ℕ} (g : Fin a × Fin b → Fin M × Fin N)
    (hg : Function.Injective g) (c : ℝ) (hc : c ^ 2 * (N : ℝ)⁻¹ = (b : ℝ)⁻¹) :
    IsGaussianEnsemble (fun (ω : GaussSpace M N) (i : Fin a) (μ : Fin b) =>
      c * gaussX M N ω (g (i, μ)).1 (g (i, μ)).2) where
  measurable i μ := ((gaussX_isGaussianEnsemble M N).measurable _ _).const_mul c
  indep := by
    have h := ((gaussX_isGaussianEnsemble M N).indep.precomp hg).comp
      (fun _ x => c * x) (fun _ => measurable_const_mul c)
    exact h
  law i μ := by
    have hG := gaussX_isGaussianEnsemble M N
    have hmeas : Measurable fun ω : GaussSpace M N => gaussX M N ω (g (i, μ)).1 (g (i, μ)).2 :=
      hG.measurable _ _
    have e1 : (fun ω : GaussSpace M N => c * gaussX M N ω (g (i, μ)).1 (g (i, μ)).2) =
        (fun x => c * x) ∘ fun ω => gaussX M N ω (g (i, μ)).1 (g (i, μ)).2 := rfl
    rw [e1, ← Measure.map_map (measurable_const_mul c) hmeas, hG.law,
      gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    push_cast
    rw [hc]

/-! ## Lower bounds on the count -/

private lemma gc_dot_self_nonneg {K : ℕ} (v : Fin K → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `⟨w, Xᵀ diag(v) X w⟩ = Σ_i v_i (X w)_i²`. -/
private lemma gc_quad (v : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (w : Fin N → ℝ) :
    w ⬝ᵥ QN (diagonal v) Xm *ᵥ w = ∑ i, v i * (Xm *ᵥ w) i ^ 2 := by
  unfold QN
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `|X Xᵀ u|² ≥ c' |Xᵀ u|²` when `|Xᵀ u|² ≥ c' |u|²`. -/
private lemma gc_sq_ge {c' : ℝ} (hc' : 0 < c') (Xm : Matrix (Fin M) (Fin N) ℝ) (u : Fin M → ℝ)
    (hu : c' * (u ⬝ᵥ u) ≤ Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u) :
    c' * (Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u) ≤ Xm *ᵥ (Xmᵀ *ᵥ u) ⬝ᵥ Xm *ᵥ (Xmᵀ *ᵥ u) := by
  set w := Xmᵀ *ᵥ u with hw
  set z := Xm *ᵥ w with hz
  have h1 : u ⬝ᵥ z = w ⬝ᵥ w := by
    rw [hz, dotProduct_mulVec, hw, mulVec_transpose]
  have h2 := gc_dot_self_nonneg (z - c' • u)
  have e : (z - c' • u) ⬝ᵥ (z - c' • u) =
      z ⬝ᵥ z - 2 * c' * (u ⬝ᵥ z) + c' ^ 2 * (u ⬝ᵥ u) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm z u]
    ring
  rw [e, h1] at h2
  have h3 := mul_le_mul_of_nonneg_left hu hc'.le
  nlinarith

/-- If `|Xᵀ u|² ≥ c' |u|²` for all `u` and `σ ≥ s ≥ 0`, then `n(s c') ≥ M`. -/
private lemma gc_count_full {σ : Fin M → ℝ} {s c' : ℝ} (hs : 0 ≤ s) (hσ : ∀ i, s ≤ σ i)
    (hc' : 0 < c') (Xm : Matrix (Fin M) (Fin N) ℝ)
    (hlow : ∀ u : Fin M → ℝ, c' * (u ⬝ᵥ u) ≤ Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u) :
    M ≤ eigCount (QN (diagonal σ) Xm) (s * c') := by
  have hinj : Function.Injective (Xmᵀ.mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h := hlow u
    rw [Matrix.mulVecLin_apply] at hu
    rw [hu, dotProduct_zero] at h
    have h0 : u ⬝ᵥ u ≤ 0 := by
      by_contra hc
      have : 0 < c' * (u ⬝ᵥ u) := mul_pos hc' (lt_of_not_ge hc)
      linarith
    exact dotProduct_self_eq_zero.1 (le_antisymm h0 (gc_dot_self_nonneg u))
  have hrank : Module.finrank ℝ (LinearMap.range Xmᵀ.mulVecLin) = M := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  refine hrank.symm.trans_le (eigCount_ge_of_subspace (gc_QN_herm σ Xm) _ fun w hw => ?_)
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
  rw [Matrix.mulVecLin_apply, gc_quad]
  have h1 := gc_sq_ge hc' Xm u (hlow u)
  have h2 : s * (Xm *ᵥ (Xmᵀ *ᵥ u) ⬝ᵥ Xm *ᵥ (Xmᵀ *ᵥ u)) ≤
      ∑ i, σ i * (Xm *ᵥ (Xmᵀ *ᵥ u)) i ^ 2 := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hσ i, sq_nonneg ((Xm *ᵥ (Xmᵀ *ᵥ u)) i)]
  have h3 := mul_le_mul_of_nonneg_left h1 hs
  nlinarith

/-- If `Σ_{i ∈ B} (X w)_i² ≥ c' |w|²` for all `w` and `σ ≥ s ≥ 0` on `B`, then `n(s c') ≥ N`. -/
private lemma gc_count_rows {σ : Fin M → ℝ} {s c' : ℝ} (B : Finset (Fin M))
    (hσ : ∀ i, 0 ≤ σ i) (hs : 0 ≤ s) (hσB : ∀ i ∈ B, s ≤ σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    (hlow : ∀ w : Fin N → ℝ, c' * (w ⬝ᵥ w) ≤ ∑ i ∈ B, (Xm *ᵥ w) i ^ 2) :
    N ≤ eigCount (QN (diagonal σ) Xm) (s * c') := by
  have h := eigCount_ge_of_subspace (gc_QN_herm σ Xm) (E := s * c')
    (⊤ : Submodule ℝ (Fin N → ℝ)) fun w _ => by
      rw [gc_quad]
      calc s * c' * (w ⬝ᵥ w) = s * (c' * (w ⬝ᵥ w)) := by ring
        _ ≤ s * ∑ i ∈ B, (Xm *ᵥ w) i ^ 2 := mul_le_mul_of_nonneg_left (hlow w) hs
        _ = ∑ i ∈ B, s * (Xm *ᵥ w) i ^ 2 := Finset.mul_sum _ _ _
        _ ≤ ∑ i ∈ B, σ i * (Xm *ᵥ w) i ^ 2 :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hσB i hi) (sq_nonneg _)
        _ ≤ ∑ i, σ i * (Xm *ᵥ w) i ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun i _ _ => mul_nonneg (hσ i) (sq_nonneg _)
  simpa using h

/-- Sums over `Fin |S|` along the enumeration of `S`. -/
private lemma gc_sum_enum (S : Finset (Fin M)) (f : Fin M → ℝ) :
    ∑ a : Fin S.card, f (S.equivFin.symm a) = ∑ i ∈ S, f i := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => f x), Finset.sum_coe_sort S f]

/-- The lower bound for the rows of `X` in `S`, transferred to vectors supported in `S`. -/
private lemma gc_low_top (S : Finset (Fin M)) {c' : ℝ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (Y : Matrix (Fin S.card) (Fin N) ℝ) (hY : ∀ a μ, Y a μ = Xm (S.equivFin.symm a) μ)
    (h : ∀ v : Fin S.card → ℝ, c' * (v ⬝ᵥ v) ≤ Yᵀ *ᵥ v ⬝ᵥ Yᵀ *ᵥ v)
    (u : Fin M → ℝ) (hu : ∀ i, i ∉ S → u i = 0) :
    c' * (u ⬝ᵥ u) ≤ Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u := by
  have hsub : ∀ f : Fin M → ℝ, (∀ i, i ∉ S → f i = 0) → ∑ i ∈ S, f i = ∑ i, f i :=
    fun f hf => Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hf i hi
  set v : Fin S.card → ℝ := fun a => u (S.equivFin.symm a) with hv
  have h1 : v ⬝ᵥ v = u ⬝ᵥ u := by
    simp only [dotProduct, hv]
    rw [gc_sum_enum S (fun i => u i * u i), hsub _ fun i hi => by simp [hu i hi]]
  have h2 : Yᵀ *ᵥ v = Xmᵀ *ᵥ u := by
    funext μ
    simp only [mulVec, dotProduct, transpose_apply, hY, hv]
    rw [gc_sum_enum S (fun i => Xm i μ * u i), hsub _ fun i hi => by simp [hu i hi]]
  have := h v
  rwa [h1, h2] at this

/-- The lower bound for the rescaled transposed rows of `X` in `S`. -/
private lemma gc_low_cols (S : Finset (Fin M)) {c c' : ℝ} (hc : c ^ 2 ≤ 1)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (Y : Matrix (Fin N) (Fin S.card) ℝ)
    (hY : ∀ μ b, Y μ b = c * Xm (S.equivFin.symm b) μ)
    (h : ∀ w : Fin N → ℝ, c' * (w ⬝ᵥ w) ≤ Yᵀ *ᵥ w ⬝ᵥ Yᵀ *ᵥ w) (w : Fin N → ℝ) :
    c' * (w ⬝ᵥ w) ≤ ∑ i ∈ S, (Xm *ᵥ w) i ^ 2 := by
  have h1 : Yᵀ *ᵥ w ⬝ᵥ Yᵀ *ᵥ w = c ^ 2 * ∑ i ∈ S, (Xm *ᵥ w) i ^ 2 := by
    have e : ∀ b, (Yᵀ *ᵥ w) b = c * (Xm *ᵥ w) (S.equivFin.symm b) := by
      intro b
      simp only [mulVec, dotProduct, transpose_apply, hY, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    simp only [dotProduct, e]
    rw [Finset.mul_sum, ← gc_sum_enum S (fun i => c ^ 2 * (Xm *ᵥ w) i ^ 2)]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h2 : 0 ≤ ∑ i ∈ S, (Xm *ᵥ w) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := h w
  rw [h1] at this
  nlinarith

/-! ## The bottom edge `a_{2p}` -/

/-- `Σ_s r_s G(s) = N⁻¹ Σ_i G(σ_i)` when every `σ_i > 0`. -/
private lemma gc_group (N : ℕ) (σ : Fin M → ℝ) (hpos : ∀ i, 0 < σ i) (G : ℝ → ℝ) :
    ∑ s ∈ posVals σ, weight N σ s * G s = (N : ℝ)⁻¹ * ∑ i, G (σ i) := by
  have hP : posVals σ = Finset.univ.image σ := by
    unfold posVals
    apply Finset.filter_true_of_mem
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact hpos i
  rw [Finset.sum_comp (s := Finset.univ) G σ, hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold weight
  rw [nsmul_eq_mul]
  ring

/-- The bottom edge `a_{2p} ≥ τ_g` in the chart `y = y_{2p} = 1/x_{2p}`: either `y < 0`, and then
`M ≤ (1 − τ τ_g) N` and `σ ≥ τ_g`; or `y > 0`, and then at least `(1 + τ² τ_g/2) N` of the `σ_i`
are `≥ τ⁴ τ_g²/2`. The case `y = 0` (which contains `M = N`) gives `a_{2p} = 0`. -/
private lemma gc_bottom_cases {τ τg : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hpos : ∀ i, 0 < σ i) (hτg : 0 < τg) (ha : τg ≤ edgeVal N σ (2 * numBands N σ)) :
    ((M : ℝ) ≤ (1 - τ * τg) * N ∧ ∀ i, τg ≤ σ i) ∨
      (1 + τ ^ 2 * τg / 2) * (N : ℝ) ≤
        ((Finset.univ.filter fun i => τ ^ 4 * τg ^ 2 / 2 ≤ σ i).card : ℝ) := by
  have hτ := hda.pos
  have hφl := hda.phi_lower
  have hφu := hda.phi_upper
  unfold phiRatio at hφl hφu
  have hNr : (0 : ℝ) < N := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hφl; linarith
  have hMr : (0 : ℝ) < M := by
    rcases (Nat.cast_nonneg M : (0 : ℝ) ≤ M).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_div] at hφl; linarith
  have hN : 0 < N := by exact_mod_cast hNr
  have hM : 0 < M := by exact_mod_cast hMr
  have hmem : ∀ i, σ i ∈ posVals σ := fun i =>
    Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hpos i⟩
  have hS : (posVals σ).Nonempty := ⟨_, hmem ⟨0, hM⟩⟩
  obtain ⟨hyc, hy1⟩ := yEdge_spec N σ hda.nonneg hN hS
  set y := yEdge N σ with hydef
  have hae : edgeVal N σ (2 * numBands N σ) = FChart N σ y := by
    unfold edgeVal
    simp [hydef]
  have hyi : ∀ i, 0 < y + σ i := fun i => hyc (σ i) (hmem i)
  have hF : FChart N σ y = -y + (N : ℝ)⁻¹ * ∑ i, σ i * y / (y + σ i) := by
    unfold FChart
    rw [← gc_group N σ hpos (fun s => s * y / (y + s))]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by rwa [div_le_iff₀ hNr] at hφu
  have hσle := hda.bound_Sigma
  have hNi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNr
  set S := ∑ i, σ i * y / (y + σ i) with hSdef
  have haS : τg ≤ -y + (N : ℝ)⁻¹ * S := by rw [← hF, ← hae]; exact ha
  rcases lt_trichotomy y 0 with hy | hy | hy
  · -- `y < 0`: `M < N`
    left
    have hterm : ∀ i, σ i * y / (y + σ i) ≤ y := by
      intro i
      rw [div_le_iff₀ (hyi i)]
      nlinarith [sq_nonneg y]
    have hsum : S ≤ M * y := by
      calc S ≤ ∑ _i : Fin M, y := Finset.sum_le_sum fun i _ => hterm i
        _ = M * y := by simp
    have h1 : (N : ℝ)⁻¹ * S ≤ (N : ℝ)⁻¹ * (M * y) := mul_le_mul_of_nonneg_left hsum hNi.le
    set q := (N : ℝ)⁻¹ * M with hq
    have hq0 : 0 ≤ q := by positivity
    have h2 : τg ≤ -y * (1 - q) := by
      have : (N : ℝ)⁻¹ * (M * y) = q * y := by rw [hq]; ring
      nlinarith
    have hz : -y < τ⁻¹ := by
      have := hyi ⟨0, hM⟩
      linarith [hσle ⟨0, hM⟩]
    have hzτ : -y * τ < 1 := by
      have := mul_lt_mul_of_pos_right hz hτ
      rwa [inv_mul_cancel₀ hτ.ne'] at this
    have h1q : 0 < 1 - q := by
      by_contra hc
      have : -y * (1 - q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    have hzg : τg ≤ -y := by nlinarith
    refine ⟨?_, fun i => by linarith [hyi i]⟩
    have hqb : q ≤ 1 - τ * τg := by nlinarith [mul_le_mul_of_nonneg_left h2 hτ.le]
    have : (M : ℝ) = q * N := by rw [hq]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hqb hNr.le
  · -- `y = 0`: `a_{2p} = 0`
    exfalso
    rw [hy] at haS
    simp [hSdef, hy] at haS
    linarith
  · -- `y > 0`: `M > N`
    right
    set sb := τ ^ 4 * τg ^ 2 / 2 with hsb
    set B := Finset.univ.filter fun i => sb ≤ σ i with hB
    have hsum_le : S ≤ ∑ i, σ i := Finset.sum_le_sum fun i _ => by
      rw [div_le_iff₀ (hyi i)]
      nlinarith [hpos i]
    have hsum_lt : S ≤ M * y := by
      calc S ≤ ∑ _i : Fin M, y := Finset.sum_le_sum fun i _ => by
            rw [div_le_iff₀ (hyi i)]
            nlinarith [hpos i]
        _ = M * y := by simp
    have hσsum : ∑ i, σ i ≤ M * τ⁻¹ := by
      calc ∑ i, σ i ≤ ∑ _i : Fin M, τ⁻¹ := Finset.sum_le_sum fun i _ => hσle i
        _ = M * τ⁻¹ := by simp
    -- `y + τ_g ≤ N⁻¹ S`
    have hyS : (y + τg) * N ≤ S := by
      have : y + τg ≤ (N : ℝ)⁻¹ * S := by linarith
      calc (y + τg) * N ≤ (N : ℝ)⁻¹ * S * N := mul_le_mul_of_nonneg_right this hNr.le
        _ = S := by field_simp
    -- `y ≤ τ⁻²`
    have hyup : y * τ ^ 2 ≤ 1 := by
      have h1 : (y + τg) * N ≤ τ⁻¹ * N * τ⁻¹ := by nlinarith
      have h2 : y * N ≤ τ⁻¹ * τ⁻¹ * N := by nlinarith
      have h3 : y ≤ τ⁻¹ * τ⁻¹ := le_of_mul_le_mul_right (by linarith) hNr
      have h4 : τ⁻¹ * τ⁻¹ * τ ^ 2 = 1 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg τ)]
    -- `y ≥ τ τ_g`
    have hylow : τ * τg ≤ y := by
      have h1 : (y + τg) * N ≤ τ⁻¹ * N * y := by nlinarith
      have h2 : τg * N ≤ τ⁻¹ * N * y := by nlinarith
      have h3 : τg ≤ τ⁻¹ * y := by
        have h2' : τg * N ≤ (τ⁻¹ * y) * N := by linarith
        exact le_of_mul_le_mul_right h2' hNr
      have := mul_le_mul_of_nonneg_left h3 hτ.le
      rwa [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul] at this
    -- splitting the sum at `σ_i ≥ s_b`
    have hsplit : S ≤ B.card * y + M * sb := by
      have hb : ∀ i, σ i * y / (y + σ i) ≤ (if sb ≤ σ i then y else sb) := by
        intro i
        split_ifs with h
        · rw [div_le_iff₀ (hyi i)]; nlinarith [hpos i]
        · rw [div_le_iff₀ (hyi i)]; nlinarith [hpos i]
      have hsb0 : 0 ≤ sb := by positivity
      calc S ≤ ∑ i, (if sb ≤ σ i then y else sb) := Finset.sum_le_sum fun i _ => hb i
        _ = B.card * y + (Finset.univ.filter fun i => ¬ sb ≤ σ i).card * sb := by
            rw [Finset.sum_ite]
            simp [hB]
        _ ≤ B.card * y + M * sb := by
            have : ((Finset.univ.filter fun i => ¬ sb ≤ σ i).card : ℝ) ≤ M := by
              have := Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => ¬ sb ≤ σ i)
              rw [Finset.card_univ, Fintype.card_fin] at this
              exact_mod_cast this
            have := mul_le_mul_of_nonneg_right this hsb0
            linarith
    have hMsb : (M : ℝ) * sb ≤ τ⁻¹ * N * sb := mul_le_mul_of_nonneg_right hMN (by positivity)
    have hkey : (1 + τ ^ 2 * τg / 2) * N * y ≤ B.card * y := by
      have e1 : τ⁻¹ * sb = τ ^ 3 * τg ^ 2 / 2 := by rw [hsb]; field_simp
      have h1 : τ ^ 2 * τg * y * N ≤ τg * N := by
        have := mul_le_mul_of_nonneg_right hyup (mul_nonneg hτg.le hNr.le)
        linarith
      have h2 : τ ^ 3 * τg ^ 2 / 2 * N ≤ τ ^ 2 * τg / 2 * y * N := by
        have := mul_le_mul_of_nonneg_left hylow (by positivity : (0 : ℝ) ≤ τ ^ 2 * τg / 2 * N)
        linarith
      have h3 : τ⁻¹ * N * sb = τ ^ 3 * τg ^ 2 / 2 * N := by rw [← e1]; ring
      linarith
    exact le_of_mul_le_mul_right hkey hy

/-- `N > 0` and `M > 0` under the density assumptions. -/
private lemma gc_pos_NM {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M := by
  have hτ := hda.pos
  have hφl := hda.phi_lower
  unfold phiRatio at hφl
  constructor
  · rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, div_zero] at hφl; linarith
    · exact h
  · rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, Nat.cast_zero, zero_div] at hφl; linarith
    · exact h

/-- Points `E ∈ [w, a_{2p}/2]` are at distance `≥ w` from `supp ϱ` when `w ≤ a_{2p}/2`. -/
private lemma gc_bottom_dist {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hpos : ∀ i, 0 < σ i) (ha : 0 < edgeVal N σ (2 * numBands N σ)) {w E : ℝ} (hw : 0 < w)
    (hwE : w ≤ E) (hw2 : w ≤ edgeVal N σ (2 * numBands N σ) / 2)
    (hE : E ≤ edgeVal N σ (2 * numBands N σ) / 2) :
    w ≤ Metric.infDist E (varrho N σ).support := by
  obtain ⟨hN, hM⟩ := gc_pos_NM hda
  have hσ := hda.nonneg
  have hS : (posVals σ).Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hM⟩), hpos _⟩⟩
  have hp := (card_innerCrit N σ hσ hN hS).2
  set p := numBands N σ with hpdef
  have hne : (varrho N σ).support.Nonempty := by
    refine ⟨edgeVal N σ (2 * p),
      (mem_support_varrho_iff N σ hσ hN hS ha).2 ⟨p, hp, le_rfl, le_rfl, ?_⟩⟩
    have h := gc_edge_chain N σ hσ hN hS 1 (m := 2 * p - 1) (by omega) (by omega)
    rwa [show 2 * p - 1 + 1 = 2 * p by omega] at h
  rw [Metric.le_infDist hne]
  intro s hs
  rw [Real.dist_eq]
  rcases le_or_gt s 0 with hs0 | hs0
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨l, hl1, hlp, hsl⟩ := (mem_support_varrho_iff N σ hσ hN hS hs0).1 hs
    have h := gc_edge_chain N σ hσ hN hS (2 * p - 2 * l) (m := 2 * l) (by omega) (by omega)
    rw [show 2 * l + (2 * p - 2 * l) = 2 * p by omega] at h
    rw [abs_of_nonpos (by linarith [hsl.1])]
    linarith [hsl.1]

/-- `K N^{-(D+2)} ≤ N^{-D}` for `K ≤ N`, `N ≥ 1`. -/
private lemma gc_union {N K : ℕ} (D : ℝ) (hK : K ≤ N) (hN : 1 ≤ N) :
    (K : ℝ) * (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 2)) * ((N : ℝ) * N) := by
    rw [show -D = -(D + 2) + 1 + 1 by ring, Real.rpow_add_one hN0.ne',
      Real.rpow_add_one hN0.ne']
    ring
  have hx := Real.rpow_nonneg hN0.le (-(D + 2))
  have hK' : (K : ℝ) ≤ N := by exact_mod_cast hK
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKN : (K : ℝ) ≤ N * N := by nlinarith
  rw [e, mul_comm (K : ℝ)]
  exact mul_le_mul_of_nonneg_left hKN hx

/-! ## Lemma 10.4: the deterministic chain -/

/-- The deterministic part of Lemma 10.4 for `Σ = diag(σ)`: given `‖XᵀX‖ ≤ C₀`, the lower bound
`|Xᵀu|² ≥ c' |u|²` on the top block, and no eigenvalue `≥ τ_g/4` of `Q(t_j)` at distance
`≥ τ_g/4` from `supp ϱ_{t_j}` along the lattice `t_j = 1 + j (T − 1)/K`, the count at the gap
midpoint is `d_k`. -/
private lemma gc_core {τ τg C₀ c' T R : ℝ} {σ : Fin M → ℝ} {k K : ℕ}
    (hda : DensityAssumptions τ N σ) (hpos : ∀ i, 0 < σ i) (hτg : 0 < τg)
    (hk : 1 ≤ k) (hkp : k < numBands N σ) (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1))
    (hc' : 0 < c') (hT : 1 ≤ T) (hK : 0 < K)
    (hR₁ : τ⁻¹ * C₀ < R) (hR₂ : R ≤ T * (gapCx τ τg)⁻¹ * c') (hRE : deformEmax τ τg ≤ R)
    (hend : ∀ E ∈ Set.Icc (deformE N σ k T) R,
      τg / 4 ≤ Metric.infDist E (varrho N (deformSig N σ k T)).support)
    (hstep : (τ⁻¹ * |C₀| + |deformL τ τg|) * ((T - 1) / K) < τg / 4)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hnorm : ‖Xmᵀ * Xm‖ ≤ C₀)
    (hlow : ∀ u : Fin M → ℝ, (∀ i, ¬ (1 + σ i * xCrit N σ (2 * k) < 0) → u i = 0) →
      c' * (u ⬝ᵥ u) ≤ Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u)
    (hgap : ∀ j ≤ K, ∀ i,
      τg / 4 ≤ specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) Xm) i →
      Metric.infDist (specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) Xm) i)
        (varrho N (specOf (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))))).support
          < τg / 4) :
    eigCount (QN (diagonal σ) Xm) (gapMid N σ k) = cumCount N σ k := by
  have hτ := hda.pos
  have hCx := gc_Cx_pos hτ hτg
  obtain ⟨hθ, -⟩ := gapMid_window hda hτg hk hkp ha hg
  obtain ⟨hE1, hwin, hlip, hEmax⟩ := deform_facts hda hτg hk hkp ha hg
  set t : ℕ → ℝ := fun j => 1 + j * ((T - 1) / K) with ht
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hΔ : 0 ≤ (T - 1) / K := div_nonneg (by linarith) hKr.le
  have ht1 : ∀ j, 1 ≤ t j := fun j => by
    have := mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hΔ
    simp only [ht]
    linarith
  have ht0 : t 0 = 1 := by simp [ht]
  have htK : t K = T := by
    simp only [ht]
    field_simp
    ring
  have hgap' : ∀ j ≤ K, ∀ i, τg / 4 ≤ specOf (QN (diagonal (deformSig N σ k (t j))) Xm) i →
      Metric.infDist (specOf (QN (diagonal (deformSig N σ k (t j))) Xm) i)
        (varrho N (deformSig N σ k (t j))).support < τg / 4 := by
    intro j hj i hi
    have := hgap j hj i hi
    rwa [gc_varrho_specOf_diagonal] at this
  have hlat := eigCount_lattice (fun j => QN (diagonal (deformSig N σ k (t j))) Xm)
    (fun j => gc_QN_herm _ _) (fun j => deformE N σ k (t j)) (δ := τg / 4) K
    (fun j hj => by
      have h1 := QN_deform_lip hpos hτ hda.bound_Sigma k Xm hnorm (ht1 (j + 1)) (ht1 j)
      have h2 := hlip (t (j + 1)) (t j) (ht1 _) (ht1 _)
      have hd : |t (j + 1) - t j| = (T - 1) / K := by
        simp only [ht]
        push_cast
        rw [show 1 + ((j : ℝ) + 1) * ((T - 1) / K) - (1 + j * ((T - 1) / K)) = (T - 1) / K by
          ring]
        exact abs_of_nonneg hΔ
      rw [hd] at h1 h2
      have h3 : τ⁻¹ * C₀ * ((T - 1) / K) ≤ τ⁻¹ * |C₀| * ((T - 1) / K) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 hτ.le)) hΔ
      have h4 : deformL τ τg * ((T - 1) / K) ≤ |deformL τ τg| * ((T - 1) / K) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hΔ
      rw [add_mul] at hstep
      linarith)
    (fun j hj i hi => by
      have h1 := deformE_ge_gapMid hda hτg hk hkp ha hg (ht1 j)
      have h2 := hgap' j hj.le i (by linarith [hi.1])
      have h3 := hwin (t j) (ht1 j) _ hi
      linarith)
  beta_reduce at hlat
  rw [htK, ht0, gc_sig_one, hE1] at hlat
  have hcount : eigCount (QN (diagonal (deformSig N σ k T)) Xm) R = cumCount N σ k := by
    rw [eigCount_deform_end hpos k Xm hc' (inv_pos.2 hCx) hT hlow
      (topBlock_bounds hda hτg hk hkp ha).2 hτ hda.bound_Sigma hnorm hR₁ hR₂,
      topBlock_card hda hk hkp]
  have hgapT : ∀ i, τg / 4 ≤ specOf (QN (diagonal (deformSig N σ k T)) Xm) i →
      Metric.infDist (specOf (QN (diagonal (deformSig N σ k T)) Xm) i)
        (varrho N (deformSig N σ k T)).support < τg / 4 := by
    have := hgap' K le_rfl
    rwa [htK] at this
  have hET : eigCount (QN (diagonal (deformSig N σ k T)) Xm) (deformE N σ k T) =
      eigCount (QN (diagonal (deformSig N σ k T)) Xm) R := by
    refine gc_eigCount_eq _ ((hEmax T hT).trans hRE) fun i hi => ?_
    have h1 := deformE_ge_gapMid hda hτg hk hkp ha hg hT
    have h2 := hgapT i (by linarith [hi.1])
    have h3 := hend _ hi
    linarith
  rw [← hlat, hET, hcount]

/-! ## Lemma 10.4, the bottom count and Proposition 10.2 -/

/-- Lemma 10.4 (`lem:Gaussian counting`) at fixed `N`: for Gaussian `X`, `Υ_k = d_k` with high
probability, for every gap `k` with `a_{2k} ≥ τ_g` and width `≥ τ_g`. -/
theorem gauss_count (τ τg D : ℝ) (hτ : 0 < τ) (hτg : 0 < τg) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
      IsModel τ gaussMoment M N Sig (gaussX M N) → 1 ≤ k → k < numBands N (specOf Sig) →
      τg ≤ edgeVal N (specOf Sig) (2 * k) →
      τg ≤ edgeVal N (specOf Sig) (2 * k) - edgeVal N (specOf Sig) (2 * k + 1) →
      HighProbAt N D {ω | eigCount (QN Sig (gaussX M N ω)) (gapMid N (specOf Sig) k) =
        cumCount N (specOf Sig) k} := by
  by_cases hτ1 : 1 < τ
  · exact ⟨0, fun N _ M Sig k hm => absurd hm.tau_le_one (not_le.2 hτ1)⟩
  replace hτ1 : τ ≤ 1 := not_lt.1 hτ1
  have hCx := gc_Cx_pos hτ hτg
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  obtain ⟨Nn, hNn⟩ := hC₀ gaussMoment (D + 2)
  obtain ⟨c', hc', hlam⟩ := lambdaMin_ge (c := τ / gapCx τ τg) (div_pos hτ hCx)
  obtain ⟨Nl, hNl⟩ := hlam (D + 2)
  set R : ℝ := max (deformEmax τ τg) (τ⁻¹ * C₀ + 1) with hR
  obtain ⟨T₀, hT₀1, hT₀⟩ := deform_end τ τg R hτ hτg
  set T : ℝ := max T₀ (R * gapCx τ τg / c') with hT
  have hT1 : 1 ≤ T := hT₀1.trans (le_max_left _ _)
  set A : ℝ := τ⁻¹ * |C₀| + |deformL τ τg| with hA
  set K : ℕ := ⌈8 * (A * (T - 1)) / τg⌉₊ + 1 with hK
  have hKpos : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hstep : A * ((T - 1) / K) < τg / 4 := by
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ A * (T - 1) := mul_nonneg hA0 (by linarith)
    have hlt : 8 * (A * (T - 1)) / τg < K := by
      rw [hK]
      push_cast
      linarith [Nat.le_ceil (8 * (A * (T - 1)) / τg)]
    rw [div_lt_iff₀ hτg] at hlt
    rw [← mul_div_assoc, div_lt_iff₀ hKr]
    nlinarith
  have hR₁ : τ⁻¹ * C₀ < R := by linarith [le_max_right (deformEmax τ τg) (τ⁻¹ * C₀ + 1)]
  have hR₂ : R ≤ T * (gapCx τ τg)⁻¹ * c' := by
    have h : R * gapCx τ τg / c' ≤ T := le_max_right _ _
    calc R = R * gapCx τ τg / c' * (gapCx τ τg)⁻¹ * c' := by field_simp
      _ ≤ T * (gapCx τ τg)⁻¹ * c' := by gcongr
  have hRE : deformEmax τ τg ≤ R := le_max_left _ _
  have hτT : 0 < min τ (τ / T) := lt_min hτ (div_pos hτ (by linarith))
  obtain ⟨Ng, hNg⟩ := gap_outside (min τ (τ / T)) gaussMoment (τg / 4) (τg / 4) (D + 2) hτT
    (by positivity) (by positivity)
  refine ⟨max (max Nn Nl) (max Ng (K + 3)), fun N hN M Sig k hm hk hkp ha hg => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hNn', hNl'⟩, hNg', hNK⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set σ := specOf Sig with hσ
  have hd : DiagModel τ gaussMoment M N σ (gaussX M N) := hm.diagModel_specOf
  have hda : DensityAssumptions τ N σ := hd.densityAssumptions hτ
  have hmD : IsModel τ gaussMoment M N (diagonal σ) (gaussX M N) := diagModel_iff.mp hd
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rwa [div_le_iff₀ hN0] at this
  unfold HighProbAt
  rw [Set.compl_ofPred]
  have hrot := gc_rotate (N := N) hm.sigma.posDef
    (fun Q => ¬ eigCount Q (gapMid N σ k) = cumCount N σ k)
  rw [hrot]
  -- the lower bound on the top block
  set S := Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0 with hS
  have hScard : (S.card : ℝ) ≤ (1 - τ / gapCx τ τg) * N := by
    rw [hS, topBlock_card hda hk hkp]
    exact (topBlock_bounds hda hτg hk hkp ha).1
  set g : Fin S.card × Fin N → Fin M × Fin N := fun p => ((S.equivFin.symm p.1 : Fin M), p.2)
    with hgdef
  have hginj : Function.Injective g := by
    rintro ⟨a, μ⟩ ⟨b, ν⟩ h
    simp only [hgdef, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have := S.equivFin.symm.injective (Subtype.ext h1)
    rw [this, h2]
  have hYG := gc_sub_gauss g hginj 1 (by simp)
  have hYl := hNl N hNl' S.card _ hYG hScard
  have hXn := hNn N hNn' M (gaussX M N) hm.entries hMN
  -- the gap events along the lattice
  have hGj : ∀ j ∈ Finset.range (K + 1),
      HighProbAt N (D + 2) {ω : GaussSpace M N | ∀ i, τg / 4 ≤
        specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) (gaussX M N ω)) i →
        Metric.infDist
          (specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) (gaussX M N ω)) i)
          (varrho N (specOf (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))))).support
            < τg / 4} := by
    intro j hj
    have hjK : (j : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hΔ : 0 ≤ (T - 1) / K := div_nonneg (by linarith) hKr.le
    have ht1 : 1 ≤ 1 + j * ((T - 1) / K) := by
      have := mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hΔ
      linarith
    have htT : 1 + j * ((T - 1) / K) ≤ T := by
      have : (j : ℝ) * ((T - 1) / K) ≤ K * ((T - 1) / K) := mul_le_mul_of_nonneg_right hjK hΔ
      have e : (K : ℝ) * ((T - 1) / K) = T - 1 := by field_simp
      linarith
    exact hNg N hNg' M _ (gaussX M N) (isModel_deform hmD k ht1 htT)
  -- the failure event is in the union of the failures of the inputs
  have hsub : {ω : GaussSpace M N | ¬ eigCount (QN (diagonal σ) (gaussX M N ω)) (gapMid N σ k) =
      cumCount N σ k} ⊆
      ({ω | ∀ u : Fin S.card → ℝ, c' * (u ⬝ᵥ u) ≤
          (fun i μ => 1 * gaussX M N ω (g (i, μ)).1 (g (i, μ)).2)ᵀ *ᵥ u ⬝ᵥ
          (fun i μ => 1 * gaussX M N ω (g (i, μ)).1 (g (i, μ)).2)ᵀ *ᵥ u}ᶜ ∪
        {ω | ‖(gaussX M N ω)ᵀ * gaussX M N ω‖ ≤ C₀}ᶜ) ∪
      ⋃ j ∈ Finset.range (K + 1), {ω : GaussSpace M N | ∀ i, τg / 4 ≤
        specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) (gaussX M N ω)) i →
        Metric.infDist
          (specOf (QN (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))) (gaussX M N ω)) i)
          (varrho N (specOf (diagonal (deformSig N σ k (1 + j * ((T - 1) / K)))))).support
            < τg / 4}ᶜ := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_exists,
      not_not] at hc
    obtain ⟨⟨hl, hn⟩, hgj⟩ := hc
    apply hω
    refine gc_core hda hd.pos hτg hk hkp ha hg hc' hT1 hKpos hR₁ hR₂ hRE
      (hT₀ T (le_max_left _ _) σ k hda hk hkp ha hg) hstep (gaussX M N ω) hn
      (fun u hu => gc_low_top S (gaussX M N ω) _ (fun a μ => by simp [hgdef]) hl u
        fun i hi => hu i (by simpa [hS] using hi))
      fun j hj => hgj j (Finset.mem_range.2 (by omega))
  unfold HighProbAt at hYl hXn hGj
  set x : ℝ := (N : ℝ) ^ (-(D + 2)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  calc _ ≤ _ := measure_mono hsub
    _ ≤ (ENNReal.ofReal x + ENNReal.ofReal x) + ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal x :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add hYl hXn)) ((measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun j hj => hGj j hj)))
    _ = ENNReal.ofReal (((K + 3 : ℕ) : ℝ) * x) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hx0 hx0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (gc_union D hNK hN1)

/-- The count below the lowest component for Gaussian `X`: no nontrivial eigenvalue below
`a_{2p}/2` when `a_{2p} ≥ τ_g`. -/
theorem gauss_bottom (τ τg D : ℝ) (hτ : 0 < τ) (hτg : 0 < τg) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
      IsModel τ gaussMoment M N Sig (gaussX M N) →
      τg ≤ edgeVal N (specOf Sig) (2 * numBands N (specOf Sig)) →
      HighProbAt N D {ω | eigCount (QN Sig (gaussX M N ω))
        (edgeVal N (specOf Sig) (2 * numBands N (specOf Sig)) / 2) = min M N} := by
  obtain ⟨c₁, hc₁, hlam₁⟩ := lambdaMin_ge (c := τ * τg) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hlam₁ (D + 2)
  set δb : ℝ := τ ^ 2 * τg / 2 with hδb
  have hδb0 : 0 < δb := by positivity
  obtain ⟨c₂, hc₂, hlam₂⟩ := lambdaMin_ge (c := δb / (1 + δb)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hlam₂ (max (D + 2) 0)
  set sb : ℝ := τ ^ 4 * τg ^ 2 / 2 with hsb
  have hsb0 : 0 < sb := by positivity
  set Eb : ℝ := min (τg * c₁) (sb * c₂) with hEbdef
  have hEb : 0 < Eb := lt_min (by positivity) (by positivity)
  set w : ℝ := min Eb (τg / 2) with hwdef
  have hw : 0 < w := lt_min hEb (by positivity)
  obtain ⟨Ng, hNg⟩ := gap_outside τ gaussMoment w Eb (D + 2) hτ hw hEb
  refine ⟨max (max N₁ N₂) (max Ng 2), fun N hN M Sig hm ha => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN₁', hN₂'⟩, hNg', hN2⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set σ := specOf Sig with hσ
  have hd : DiagModel τ gaussMoment M N σ (gaussX M N) := hm.diagModel_specOf
  have hda : DensityAssumptions τ N σ := hd.densityAssumptions hτ
  have hmD : IsModel τ gaussMoment M N (diagonal σ) (gaussX M N) := diagModel_iff.mp hd
  set a := edgeVal N σ (2 * numBands N σ) with hadef
  have ha0 : 0 < a := lt_of_lt_of_le hτg ha
  unfold HighProbAt
  rw [Set.compl_ofPred]
  have hrot := gc_rotate (N := N) hm.sigma.posDef (fun Q => ¬ eigCount Q (a / 2) = min M N)
  rw [hrot]
  set x : ℝ := (N : ℝ) ^ (-(D + 2)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  -- `n(E_b) ≥ M ∧ N` with high probability
  have hlow : ℙ {ω : GaussSpace M N |
      ¬ min M N ≤ eigCount (QN (diagonal σ) (gaussX M N ω)) Eb} ≤ ENNReal.ofReal x := by
    rcases gc_bottom_cases hda hd.pos hτg ha with ⟨hMN, hσg⟩ | hB
    · -- `M < N`: the smallest singular value of `X`
      have h := hN₁ N hN₁' M (gaussX M N) (gaussX_isGaussianEnsemble M N) hMN
      unfold HighProbAt at h
      refine le_trans (measure_mono fun ω hω => ?_) h
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hω ⊢
      intro hl
      apply hω
      have := gc_count_full hτg.le hσg hc₁ (gaussX M N ω) hl
      exact (min_le_left _ _).trans (this.trans (eigCount_antitone _ (min_le_left _ _)))
    · -- `M > N`: the rows with `σ_i ≥ s_b`
      rw [← hδb, ← hsb] at hB
      set B := Finset.univ.filter fun i => sb ≤ σ i with hBdef
      have hBr : (0 : ℝ) < B.card := by nlinarith
      have hBN : (N : ℝ) ≤ (1 - δb / (1 + δb)) * B.card := by
        rw [show 1 - δb / (1 + δb) = (1 + δb)⁻¹ by field_simp; ring, inv_mul_eq_div,
          le_div_iff₀ (by positivity)]
        linarith
      have hNB : N ≤ B.card := by
        have : (N : ℝ) ≤ B.card := by nlinarith
        exact_mod_cast this
      set c : ℝ := √((N : ℝ) / B.card) with hcdef
      have hc2 : c ^ 2 * (N : ℝ)⁻¹ = (B.card : ℝ)⁻¹ := by
        rw [hcdef, Real.sq_sqrt (by positivity)]
        field_simp
      have hc1 : c ^ 2 ≤ 1 := by
        rw [hcdef, Real.sq_sqrt (by positivity), div_le_one hBr]
        exact_mod_cast hNB
      set g : Fin N × Fin B.card → Fin M × Fin N :=
        fun p => ((B.equivFin.symm p.2 : Fin M), p.1) with hgdef
      have hginj : Function.Injective g := by
        rintro ⟨μ, a⟩ ⟨ν, b⟩ h
        simp only [hgdef, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have := B.equivFin.symm.injective (Subtype.ext h1)
        rw [this, h2]
      have hYG := gc_sub_gauss g hginj c hc2
      have h := hN₂ B.card (hN₂'.trans hNB) N _ hYG hBN
      unfold HighProbAt at h
      refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
      · simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hω ⊢
        intro hl
        apply hω
        have := gc_count_rows B (fun i => (hd.pos i).le) hsb0.le
          (fun i hi => (Finset.mem_filter.1 hi).2) (gaussX M N ω)
          (fun v => gc_low_cols B hc1 (gaussX M N ω) _ (fun μ b => by simp [hgdef]) hl v)
        exact (min_le_right _ _).trans (this.trans (eigCount_antitone _ (min_le_right _ _)))
      · have hNB' : (N : ℝ) ≤ B.card := by exact_mod_cast hNB
        calc (B.card : ℝ) ^ (-max (D + 2) 0) ≤ (N : ℝ) ^ (-max (D + 2) 0) :=
              Real.rpow_le_rpow_of_nonpos hN0 hNB' (neg_nonpos.2 (le_max_right _ _))
          _ ≤ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
              (neg_le_neg (le_max_left _ _))
  -- no eigenvalue in `[E_b, a_{2p}/2]` with high probability
  have hgap := hNg N hNg' M (diagonal σ) (gaussX M N) hmD
  unfold HighProbAt at hgap
  have hsub : {ω : GaussSpace M N |
      ¬ eigCount (QN (diagonal σ) (gaussX M N ω)) (a / 2) = min M N} ⊆
      {ω | ¬ min M N ≤ eigCount (QN (diagonal σ) (gaussX M N ω)) Eb} ∪
        {ω : GaussSpace M N | ∀ j, Eb ≤ specOf (QN (diagonal σ) (gaussX M N ω)) j →
          Metric.infDist (specOf (QN (diagonal σ) (gaussX M N ω)) j)
            (varrho N (specOf (diagonal σ))).support < w}ᶜ := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hc
    obtain ⟨hl, hgω⟩ := hc
    apply hω
    refine le_antisymm (eigCount_QN_le (posDef_diagonal_iff.2 hd.pos) _ (by positivity)) ?_
    by_cases hEa : Eb ≤ a / 2
    · rw [← gc_eigCount_eq _ hEa fun i hi => ?_]
      · exact hl
      have h1 := hgω i hi.1
      rw [gc_varrho_specOf_diagonal] at h1
      have h2 := gc_bottom_dist hda hd.pos ha0 hw ((min_le_left _ _).trans hi.1)
        ((min_le_right _ _).trans (by linarith)) hi.2
      linarith
    · exact hl.trans (eigCount_antitone _ (le_of_lt (not_le.1 hEa)))
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal x + ENNReal.ofReal x := (measure_union_le _ _).trans (add_le_add hlow hgap)
    _ = ENNReal.ofReal ((2 : ℕ) * x) := by
        rw [← ENNReal.ofReal_add hx0 hx0]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (gc_union D hN2 hN1)

/-- Proposition 10.2 (`prop:counting`) at fixed `N`: `Υ_k = d_k` with high probability. -/
theorem prop_counting (τ : ℝ) (C : ℕ → ℝ) (τg D : ℝ) (hτ : 0 < τ) (hτg : 0 < τg) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → 1 ≤ k → k < numBands N (specOf Sig) →
      τg ≤ edgeVal N (specOf Sig) (2 * k) →
      τg ≤ edgeVal N (specOf Sig) (2 * k) - edgeVal N (specOf Sig) (2 * k + 1) →
      HighProbAt N D {ω | eigCount (QN Sig (X ω)) (gapMid N (specOf Sig) k) =
        cumCount N (specOf Sig) k} := by
  obtain ⟨N₁, h₁⟩ := interp_count τ C (τg / 4) (τg / 4) (τg / 4) D hτ (by positivity)
    (by positivity) (by positivity)
  obtain ⟨N₂, h₂⟩ := gauss_count τ τg (D + 1) hτ hτg
  refine ⟨max (max N₁ N₂) 1, fun N hN Ω _ _ M Sig X k hm hk hkp ha hg => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨hθ, hwin⟩ := gapMid_window hda hτg hk hkp ha hg
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  exact h₁ N (le_of_max_le_left (le_of_max_le_left hN)) M Sig X _ _ hm (by linarith) hwin
    (h₂ N (le_of_max_le_right (le_of_max_le_left hN)) M Sig k hgm hk hkp ha hg)

/-- The bottom count for general `X`. -/
theorem bottom_count (τ : ℝ) (C : ℕ → ℝ) (τg D : ℝ) (hτ : 0 < τ) (hτg : 0 < τg) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X → τg ≤ edgeVal N (specOf Sig) (2 * numBands N (specOf Sig)) →
      HighProbAt N D {ω | eigCount (QN Sig (X ω))
        (edgeVal N (specOf Sig) (2 * numBands N (specOf Sig)) / 2) = min M N} := by
  obtain ⟨N₁, h₁⟩ := interp_count τ C (τg / 4) (τg / 4) (τg / 4) D hτ (by positivity)
    (by positivity) (by positivity)
  obtain ⟨N₂, h₂⟩ := gauss_bottom τ τg (D + 1) hτ hτg
  refine ⟨max (max N₁ N₂) 1, fun N hN Ω _ _ M Sig X hm ha => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hwin := bottom_window hda hτg ha
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  exact h₁ N (le_of_max_le_left (le_of_max_le_left hN)) M Sig X _ _ hm (by linarith) hwin
    (h₂ N (le_of_max_le_right (le_of_max_le_left hN)) M Sig hgm ha)

/-! ## Instances

Marchenko–Pastur: Gaussian `X` (`M = n`, `N = 2n`, `φ = 1/2`), `Σ = I_n`, `τ = 1/5`; here `p = 1`
and `a_2 = (1 − √(1/2))² ≥ 1/20`, so the hypotheses of `gauss_bottom` and `bottom_count` are
discharged for every `n ≥ 1`. -/

/-- `gauss_count` at `τ = 1/40`, `τ_g = 1/2`, `D = 1`, `k = 1`. Conditional: the model and edge
hypotheses are binders. They hold together, for instance, for `M = 2n`, `N = 20n` and
`σ = (10, …, 10, 1, …, 1)` (`n` copies of each), whose `f` is that of `σ = (10, 1)`, `N = 20`:
there `p = 2`, `a_2 ≥ 5.9`, `a_3 ≤ 1.5`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 40) gaussMoment M N Sig (gaussX M N) → 1 < numBands N (specOf Sig) →
    1 / 2 ≤ edgeVal N (specOf Sig) 2 →
    1 / 2 ≤ edgeVal N (specOf Sig) 2 - edgeVal N (specOf Sig) 3 →
    HighProbAt N 1 {ω | eigCount (QN Sig (gaussX M N ω)) (gapMid N (specOf Sig) 1) =
      cumCount N (specOf Sig) 1} := by
  obtain ⟨N₀, h⟩ := gauss_count (1 / 40) (1 / 2) 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm hp ha hg => h N hN M Sig 1 hm le_rfl hp ha hg⟩

/-- `prop_counting` at `τ = 1/40`, `C = gaussMoment`, `τ_g = 1/2`, `D = 1`, `k = 1`. Conditional:
the model and edge hypotheses are binders; they hold together for the data of the previous
example. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    IsModel (1 / 40) gaussMoment M N Sig X → 1 < numBands N (specOf Sig) →
    1 / 2 ≤ edgeVal N (specOf Sig) 2 →
    1 / 2 ≤ edgeVal N (specOf Sig) 2 - edgeVal N (specOf Sig) 3 →
    HighProbAt N 1 {ω | eigCount (QN Sig (X ω)) (gapMid N (specOf Sig) 1) =
      cumCount N (specOf Sig) 1} := by
  obtain ⟨N₀, h⟩ := prop_counting (1 / 40) gaussMoment (1 / 2) 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN Ω _ _ M Sig X hm hp ha hg => h N hN M Sig X 1 hm le_rfl hp ha hg⟩

end Anisotropic

#print axioms Anisotropic.gauss_count
#print axioms Anisotropic.gauss_bottom
#print axioms Anisotropic.prop_counting
#print axioms Anisotropic.bottom_count
