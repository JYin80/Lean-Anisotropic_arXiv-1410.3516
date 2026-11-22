module

public import Anisotropic.Density.Basic
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.GeneralT.Model
public import Anisotropic.LinAlg.Basic
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.MinMax

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The centred sample covariance `Q̇`, its band relabelling, the dot laws, and the deterministic facts (`λ̇_N = 0`, subordination, interlacing, the secular count) -/

/-- `π̄ = I_N − e eᵀ`, `e = N^{−1/2}(1, …, 1)` (§11.2). -/
def piBar (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := 1 - (N : ℝ)⁻¹ • Matrix.of (fun _ _ => 1)

/-- `Ẋ = X(1 − e eᵀ)` (§11.2). -/
def Xdot {K : ℕ} (Xm : Matrix (Fin K) (Fin N) ℝ) : Matrix (Fin K) (Fin N) ℝ := Xm * piBar N

/-- The `N × N` companion `(N/(N−1)) π̄ XᵀΣX π̄` of `Q̇` (def_Q); its nonzero eigenvalues are those
of `Q̇`. -/
def QdotN (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((N : ℝ) / (N - 1)) • QN Sig (Xdot Xm)

/-- `π̄ 1 = 0`. -/
theorem piBar_mulVec_one (hN : 0 < N) : piBar N *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  ext i
  simp [piBar, Matrix.mulVec, dotProduct, Matrix.one_apply]
  field_simp
  norm_num

/-- A positive semidefinite singular `K × K` matrix has `λ_K = 0`. -/
theorem sortedEig_last_eq_zero {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.PosSemidef)
    (hdet : A.det = 0) (hK : 1 ≤ K) : sortedEig A K = 0 := by
  have hH : A.IsHermitian := hA.1
  have hcard : Fintype.card (Fin K) = K := Fintype.card_fin K
  unfold sortedEig
  rw [dite_eq_left_of_eq_true (eq_true ⟨hH, hK, hcard.ge⟩)]
  rw [hH.det_eq_prod_eigenvalues] at hdet
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hdet
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin K)))
  have hi' : hH.eigenvalues₀ (e.symm i) = 0 := by
    have : hH.eigenvalues i = hH.eigenvalues₀ (e.symm i) := rfl
    exact_mod_cast (this ▸ hi)
  apply le_antisymm
  · rw [← hi']
    apply hH.eigenvalues₀_antitone
    show ((e.symm i : Fin _) : ℕ) ≤ K - 1
    have := (e.symm i).isLt
    omega
  · have h0 := hA.eigenvalues_nonneg (e ⟨K - 1, by omega⟩)
    have : hH.eigenvalues (e ⟨K - 1, by omega⟩) = hH.eigenvalues₀ ⟨K - 1, by omega⟩ := by
      simp [Matrix.IsHermitian.eigenvalues, e]
    rw [this] at h0
    exact h0

/-- `Q̇`'s companion is positive semidefinite for `Σ ≥ 0`. -/
theorem QdotN_posSemidef {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QdotN Sig Xm).PosSemidef := by
  unfold QdotN QN
  have h := hSig.conjTranspose_mul_mul_same (Xdot Xm)
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  have hc : (0 : ℝ) ≤ (N : ℝ) / (N - 1) := by
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · interval_cases N <;> norm_num
    · have : (1 : ℝ) < N := by exact_mod_cast h2
      exact div_nonneg (by linarith) (by linarith)
  exact h.smul hc

/-- `Q̇`'s companion annihilates `1`, so it is singular. -/
theorem QdotN_det (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 0 < N) :
    (QdotN Sig Xm).det = 0 := by
  have hv : QdotN Sig Xm *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    have h2 : (Xm * piBar N) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
      rw [← Matrix.mulVec_mulVec, piBar_mulVec_one hN, Matrix.mulVec_zero]
    unfold QdotN QN Xdot
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
    simp
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun _ => 1, ?_, hv⟩
  intro h
  have := congrFun h ⟨0, hN⟩
  simp at this

/-- `λ̇_N = 0` for every `X` (rank `Q̇ ≤ N − 1`). -/
theorem sortedEig_QdotN_last {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 1 ≤ N) : sortedEig (QdotN Sig Xm) N = 0 :=
  sortedEig_last_eq_zero (QdotN_posSemidef hSig Xm) (QdotN_det Sig Xm hN) hN

/-- `(N − 1) f_{N−1}(w) = N f_N(w) + w⁻¹`, written as `f_N = f_{N−1} − (f_{N−1} + w⁻¹)/N`. -/
theorem fC_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (w : ℂ) :
    fC N σ w = fC (N - 1) σ w - (fC (N - 1) σ w + w⁻¹) / N := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : ((N - 1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hN1' : (N : ℂ) - 1 ≠ 0 := by
    rw [← hN1]; exact_mod_cast (show N - 1 ≠ 0 by omega)
  unfold fC
  rw [hN1]
  have h1 : ∀ K : ℂ, K ≠ 0 → ∑ i, (σ i : ℂ) / (K * (1 + σ i * w)) =
      K⁻¹ * ∑ i, (σ i : ℂ) / (1 + σ i * w) := by
    intro K hK
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm K, ← div_div, div_eq_inv_mul]
  rw [h1 _ hN0, h1 _ hN1']
  field_simp
  ring

/-- Subordination: `m_{N−1}(z) = m_N(z − (z + m_{N−1}(z)⁻¹)/N)` on `ℂ₊`. -/
theorem mFun_pred_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 2 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    mFun (N - 1) σ z = mFun N σ (z - (z + (mFun (N - 1) σ z)⁻¹) / N) := by
  obtain ⟨hw, hf⟩ := mFun_spec (N - 1) σ hσ hz
  set w := mFun (N - 1) σ z
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have him : 0 < (z - (z + w⁻¹) / N).im := by
    have hn2 : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have : (z - (z + w⁻¹) / N).im = z.im * (1 - 1 / N) + w.im / (Complex.normSq w * N) := by
      simp [Complex.sub_im, Complex.div_im, Complex.add_im, Complex.inv_im]
      field_simp
      ring
    rw [this]
    have h1 : 0 < 1 - 1 / (N : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    positivity
  refine (mFun_eq_of_fC_eq N σ hσ him hw ?_).symm
  rw [fC_pred σ hN, hf]

/-- `Q̇` for a general `M × K` matrix `T`, through its `N × N` companion
`(N/(N−1)) π̄ Xᵀ Tᵀ T X π̄` (def_Q); its nonzero eigenvalues are those of `Q̇`. -/
def QdotNT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((N : ℝ) / (N - 1)) • QN (Tᵀ * T) (Xdot Xm)

/-- `λ̇_{k,i} = λ̇_{i + Ṅ_1 + ⋯ + Ṅ_{k−1}}`, with the band counts `Ṅ_l` of `N − 1` samples. -/
def lamDotBand (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (k i : ℕ) : ℝ :=
  sortedEig (QdotN Sig Xm) (cumCount (N - 1) (specOf Sig) (k - 1) + i)

/-- `λ̇_{k,i}` for a general `T`, relabelled with the band counts of `Σ = T Tᵀ` at `N − 1`. -/
def lamDotBandT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ)
    (k i : ℕ) : ℝ :=
  sortedEig (QdotNT T Xm) (cumCount (N - 1) (specOf (T * Tᵀ)) (k - 1) + i)

/-- `Π̇ = Π − (m + z⁻¹) e eᵀ` (§11.2), with `e eᵀ = 1 − π̄` in the `𝓘_N × 𝓘_N` block. -/
def piMatDot {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (w z : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  piMat Sig w - (w + z⁻¹) • fromBlocks 0 0 0 (cplx (1 - piBar N))

/-- `Σ̲⁻¹ (Ġ − Π̇) Σ̲⁻¹`, with `m` and `Π` at `φ = M/N`. -/
def lawMatDot {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  (ulSigma N Sig)⁻¹ * (G Sig (Xdot Xm) z - piMatDot Sig (mFun N (specOf Sig) z) z) *
    (ulSigma N Sig)⁻¹

section LawsDot

variable {Ω : Type*} [MeasureSpace Ω]

/-- (isotropic law dot) at fixed `N, ε, D` on `S`. -/
def AnisotropicLawDotAt (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomMatAt N ε D (fun ω => lawMatDot Sig (X ω) z) (fun _ => Psi N (specOf Sig) z)

/-- (averaged law dot) at fixed `N, ε, D` on `S`: `ṁ_N − m = O_≺((Nη)⁻¹)`. -/
def AveragedLawDotAt (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mN Sig (Xdot (X ω)) z - mFun N (specOf Sig) z)
    (fun _ => 1 / (N * z.im))

/-- (isotropic law dot) for a general `T`, in the weighted form of (def_block_G). -/
def AnisotropicLawDotTAt (N : ℕ) (ε D : ℝ) {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ v w : Fin M ⊕ Fin N → ℝ,
    DomAt N ε D
      (fun ω => ‖testBilin v (blockG T (Xdot (X ω)) z -
        piMatDot (T * Tᵀ) (mFun N (specOf (T * Tᵀ)) z) z) w‖)
      (fun _ => Psi N (specOf (T * Tᵀ)) z * testNorm (SigU (T * Tᵀ) *ᵥ v) *
        testNorm (SigU (T * Tᵀ) *ᵥ w))

/-- (averaged law dot) for a general `T`. -/
def AveragedLawDotTAt (N : ℕ) (ε D : ℝ) {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mNT T (Xdot (X ω)) z - mFun N (specOf (T * Tᵀ)) z)
    (fun _ => 1 / (N * z.im))

end LawsDot

section SpecSub

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- The orthogonal matrix whose columns are the eigenvectors of `A`. -/
private def qdU (hA : A.IsHermitian) : Matrix (Fin K) (Fin K) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)

/-- The coordinates of `w` in the eigenbasis of `A`. -/
private def qdC (hA : A.IsHermitian) (w : Fin K → ℝ) : Fin K → ℝ :=
  star (qdU hA) *ᵥ w

private lemma qdU_star_mul (hA : A.IsHermitian) : star (qdU hA) * qdU hA = 1 :=
  Unitary.coe_star_mul_self _

private lemma qdU_mul_star (hA : A.IsHermitian) : qdU hA * star (qdU hA) = 1 :=
  Unitary.coe_mul_star_self _

private lemma qdU_mulVec_qdC (hA : A.IsHermitian) (w : Fin K → ℝ) : qdU hA *ᵥ qdC hA w = w := by
  unfold qdC
  rw [mulVec_mulVec, qdU_mul_star, one_mulVec]

private lemma qdU_orth_dot (hA : A.IsHermitian) (x y : Fin K → ℝ) :
    (qdU hA *ᵥ x) ⬝ᵥ (qdU hA *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, mulVec_mulVec]
  have : (qdU hA)ᵀ * qdU hA = 1 := by
    have h := qdU_star_mul hA
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [this, one_mulVec]

private lemma qdU_decomp (hA : A.IsHermitian) :
    A = qdU hA * diagonal hA.eigenvalues * star (qdU hA) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [qdU] using this

private lemma qd_dot_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ w = ∑ j, (qdC hA w j) ^ 2 := by
  conv_lhs => rw [← qdU_mulVec_qdC hA w]
  rw [qdU_orth_dot]
  simp [dotProduct, sq]

private lemma qd_quad_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ (A *ᵥ w) = ∑ j, hA.eigenvalues j * (qdC hA w j) ^ 2 := by
  have h1 : A *ᵥ w = qdU hA *ᵥ (diagonal hA.eigenvalues *ᵥ qdC hA w) := by
    conv_lhs => rw [qdU_decomp hA]
    unfold qdC
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1]
  nth_rewrite 1 [← qdU_mulVec_qdC hA w]
  rw [qdU_orth_dot]
  simp only [dotProduct, mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The linear map recording the eigencoordinates of `w` indexed by `s`. -/
private def qdMap (hA : A.IsHermitian) (s : Finset (Fin K)) : (Fin K → ℝ) →ₗ[ℝ] (s → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : s → Fin K)) ∘ₗ Matrix.mulVecLin (star (qdU hA))

private lemma mem_ker_qdMap (hA : A.IsHermitian) (s : Finset (Fin K)) (w : Fin K → ℝ) :
    w ∈ LinearMap.ker (qdMap hA s) ↔ ∀ j ∈ s, qdC hA w j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 j.2

private lemma le_finrank_ker_qdMap (hA : A.IsHermitian) (s : Finset (Fin K)) :
    K ≤ Module.finrank ℝ (LinearMap.ker (qdMap hA s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (qdMap hA s)
  have h1 : Module.finrank ℝ (LinearMap.range (qdMap hA s)) ≤ s.card := by
    calc Module.finrank ℝ (LinearMap.range (qdMap hA s)) ≤ Module.finrank ℝ (s → ℝ) :=
          Submodule.finrank_le _
      _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℝ (Fin K → ℝ) = K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

private lemma qd_eigCount_eq_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E = (Finset.univ.filter fun j => E ≤ hA.eigenvalues j).card := by
  unfold eigCount
  rw [specOf_eq hA]

private lemma qd_eigCount_add_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E + (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j).card = K := by
  rw [qd_eigCount_eq_card hA, Finset.card_filter_add_card_filter_not]
  simp

/-- A spectral subspace: it has dimension at least `n_A(E)`, the form `⟨w, A w⟩ ≥ E |w|²` holds
on it, and for `E > 0` it lies in the range of `A`. -/
private lemma exists_spectral_subspace (hA : A.IsHermitian) (E : ℝ) :
    ∃ W : Submodule ℝ (Fin K → ℝ), eigCount A E ≤ Module.finrank ℝ W ∧
      (∀ w ∈ W, E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w)) ∧
      (0 < E → ∀ w ∈ W, ∃ y, w = A *ᵥ y) := by
  set s := Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j with hs
  have hz : ∀ w ∈ LinearMap.ker (qdMap hA s), ∀ j, hA.eigenvalues j < E → qdC hA w j = 0 := by
    intro w hw j hj
    exact (mem_ker_qdMap hA s w).mp hw j (by simpa [hs] using hj)
  refine ⟨LinearMap.ker (qdMap hA s), ?_, ?_, ?_⟩
  · have h1 := le_finrank_ker_qdMap hA s
    have h2 : eigCount A E + s.card = K := qd_eigCount_add_card hA E
    omega
  · intro w hw
    rw [qd_quad_eq_sum hA, qd_dot_eq_sum hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : hA.eigenvalues j < E
    · rw [hz w hw j hj]; simp
    · exact mul_le_mul_of_nonneg_right (not_lt.mp hj) (sq_nonneg _)
  · intro hE w hw
    refine ⟨qdU hA *ᵥ (fun j => qdC hA w j / hA.eigenvalues j), ?_⟩
    have hpos : ∀ j, qdC hA w j ≠ 0 → 0 < hA.eigenvalues j := by
      intro j hj
      by_contra hneg
      exact hj (hz w hw j (by linarith [not_lt.mp hneg]))
    have : diagonal hA.eigenvalues *ᵥ (fun j => qdC hA w j / hA.eigenvalues j) = qdC hA w := by
      funext j
      rw [mulVec_diagonal]
      by_cases hj : qdC hA w j = 0
      · simp [hj]
      · have := (hpos j hj).ne'
        field_simp
    have key : A *ᵥ (qdU hA *ᵥ (fun j => qdC hA w j / hA.eigenvalues j)) =
        qdU hA *ᵥ (diagonal hA.eigenvalues *ᵥ (fun j => qdC hA w j / hA.eigenvalues j)) := by
      have hd := congrArg (fun B : Matrix (Fin K) (Fin K) ℝ =>
        B *ᵥ (qdU hA *ᵥ (fun j => qdC hA w j / hA.eigenvalues j))) (qdU_decomp hA)
      rw [hd, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec _ (star (qdU hA)) (qdU hA),
        qdU_star_mul hA, one_mulVec]
    rw [key, this, qdU_mulVec_qdC]

end SpecSub

section Compress

variable {Sig : Matrix (Fin M) (Fin M) ℝ}

private lemma qd_piBar_symm : (piBar N)ᵀ = piBar N := by
  ext i j
  simp [piBar, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

private lemma qd_piBar_mulVec (w : Fin N → ℝ) :
    piBar N *ᵥ w = fun i => w i - (N : ℝ)⁻¹ * ∑ j, w j := by
  ext i
  simp [piBar, Matrix.mulVec, dotProduct, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum]

private lemma qd_one_dot (w : Fin N → ℝ) : (fun _ => (1 : ℝ)) ⬝ᵥ w = ∑ j, w j := by
  simp [dotProduct]

private lemma qd_piBar_mulVec_self {w : Fin N → ℝ} (hw : (fun _ => (1 : ℝ)) ⬝ᵥ w = 0) :
    piBar N *ᵥ w = w := by
  rw [qd_one_dot] at hw
  rw [qd_piBar_mulVec]
  ext i
  simp [hw]

private lemma qd_one_dot_piBar (w : Fin N → ℝ) :
    (fun _ => (1 : ℝ)) ⬝ᵥ (piBar N *ᵥ w) = 0 := by
  rw [qd_one_dot, qd_piBar_mulVec]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    field_simp
    ring

private lemma qd_piBar_idem (w : Fin N → ℝ) : piBar N *ᵥ (piBar N *ᵥ w) = piBar N *ᵥ w :=
  qd_piBar_mulVec_self (qd_one_dot_piBar w)

private lemma qd_dot_piBar (x y : Fin N → ℝ) :
    x ⬝ᵥ (piBar N *ᵥ y) = (piBar N *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, qd_piBar_symm]

private lemma qd_QN_Xdot (Xm : Matrix (Fin M) (Fin N) ℝ) :
    QN Sig (Xdot Xm) = piBar N * QN Sig Xm * piBar N := by
  unfold QN Xdot
  rw [Matrix.transpose_mul, qd_piBar_symm]
  simp only [Matrix.mul_assoc]

private lemma qd_QN_Xdot_mulVec (Xm : Matrix (Fin M) (Fin N) ℝ) (y : Fin N → ℝ) :
    QN Sig (Xdot Xm) *ᵥ y = piBar N *ᵥ (QN Sig Xm *ᵥ (piBar N *ᵥ y)) := by
  rw [qd_QN_Xdot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private lemma qd_quad_Xdot (Xm : Matrix (Fin M) (Fin N) ℝ) (w : Fin N → ℝ) :
    w ⬝ᵥ (QN Sig (Xdot Xm) *ᵥ w) = (piBar N *ᵥ w) ⬝ᵥ (QN Sig Xm *ᵥ (piBar N *ᵥ w)) := by
  rw [qd_QN_Xdot_mulVec, qd_dot_piBar]

/-- Interlacing for the compression `π̄ B π̄`, `B = Xᵀ Σ X`, counting form, `E > 0`. -/
theorem eigCount_compress_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {E : ℝ} (hE : 0 < E) :
    eigCount (QN Sig (Xdot Xm)) E ≤ eigCount (QN Sig Xm) E := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  obtain ⟨W, hW1, hW2, hW3⟩ := exists_spectral_subspace hB' E
  refine hW1.trans (eigCount_ge_of_subspace hB W fun w hw => ?_)
  obtain ⟨y, hy⟩ := hW3 hE w hw
  have hPw : piBar N *ᵥ w = w := by
    rw [hy, qd_QN_Xdot_mulVec, qd_piBar_idem]
  have := hW2 w hw
  rwa [qd_quad_Xdot, hPw] at this

/-- Interlacing for the compression `π̄ B π̄`, the other side (rank-one loss). -/
theorem eigCount_le_compress_add_one {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (E : ℝ) :
    eigCount (QN Sig Xm) E ≤ eigCount (QN Sig (Xdot Xm)) E + 1 := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  obtain ⟨W, hW1, hW2, -⟩ := exists_spectral_subspace hB E
  let f : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => (fun _ => (1 : ℝ)) ⬝ᵥ w
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hr : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  have h3 : Module.finrank ℝ ↥(W ⊔ LinearMap.ker f) ≤ N := by
    calc Module.finrank ℝ ↥(W ⊔ LinearMap.ker f) ≤ Module.finrank ℝ (Fin N → ℝ) :=
          Submodule.finrank_le _
      _ = N := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h4 : Module.finrank ℝ (Fin N → ℝ) = N := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h5 : Module.finrank ℝ ↥(W ⊓ LinearMap.ker f) ≤ eigCount (QN Sig (Xdot Xm)) E := by
    refine eigCount_ge_of_subspace hB' _ fun w hw => ?_
    have hP : piBar N *ᵥ w = w := qd_piBar_mulVec_self (LinearMap.mem_ker.mp hw.2)
    have := hW2 w hw.1
    rwa [qd_quad_Xdot, hP]
  omega

/-- The secular count: if `E > 0` is not an eigenvalue of `B = Xᵀ Σ X` and
`1ᵀ (B − E)⁻¹ 1 < 0`, then `π̄ B π̄` and `B` have the same number of eigenvalues `≥ E`. -/
theorem eigCount_compress_secular {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {E : ℝ} (hE : 0 < E)
    (hinv : IsUnit (QN Sig Xm - E • (1 : Matrix (Fin N) (Fin N) ℝ)))
    (hneg : (fun _ => (1 : ℝ)) ⬝ᵥ ((QN Sig Xm - E • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ *ᵥ
      fun _ => 1) < 0) :
    eigCount (QN Sig (Xdot Xm)) E = eigCount (QN Sig Xm) E := by
  refine le_antisymm (eigCount_compress_le hSig Xm hE) ?_
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  obtain ⟨W, hW1, hW2, -⟩ := exists_spectral_subspace hB E
  set C : Matrix (Fin N) (Fin N) ℝ := QN Sig Xm - E • (1 : Matrix (Fin N) (Fin N) ℝ) with hC
  have hCs : Cᵀ = C := by
    have := hB
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    rw [hC, transpose_sub, transpose_smul, transpose_one, this]
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).mp hinv
  set one : Fin N → ℝ := fun _ => 1 with hone
  set b : Fin N → ℝ := C⁻¹ *ᵥ one with hb
  set r : ℝ := one ⬝ᵥ b with hr
  have hrneg : r < 0 := hneg
  have hr0 : r ≠ 0 := hrneg.ne
  have hCb : C *ᵥ b = one := by
    rw [hb, mulVec_mulVec, Matrix.mul_nonsing_inv _ hCdet, one_mulVec]
  have hsymm : ∀ x y : Fin N → ℝ, x ⬝ᵥ (C *ᵥ y) = (C *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hCs]
  have hquadC : ∀ x : Fin N → ℝ, x ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ (QN Sig Xm *ᵥ x) - E * (x ⬝ᵥ x) := by
    intro x
    rw [hC, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  let Φ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun u => u - ((one ⬝ᵥ u) / r) • b
      map_add' := fun x y => by
        simp only [dotProduct_add, add_div, add_smul]; abel
      map_smul' := fun c x => by
        simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
        congr 2; ring }
  have hΦ : ∀ u, Φ u = u - ((one ⬝ᵥ u) / r) • b := fun u => rfl
  have h1 : ∀ u, one ⬝ᵥ Φ u = 0 := by
    intro u
    rw [hΦ, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hr]
    field_simp
    ring
  have h2 : ∀ u, Φ u ⬝ᵥ (C *ᵥ Φ u) = u ⬝ᵥ (C *ᵥ u) - (one ⬝ᵥ u) ^ 2 / r := by
    intro u
    set c := (one ⬝ᵥ u) / r with hc
    have hcr : one ⬝ᵥ u = c * r := by rw [hc]; field_simp
    rw [hΦ, Matrix.mulVec_sub, Matrix.mulVec_smul, hCb, dotProduct_sub, sub_dotProduct,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have e1 : b ⬝ᵥ (C *ᵥ u) = one ⬝ᵥ u := by rw [hsymm, hCb]
    have e2 : u ⬝ᵥ one = one ⬝ᵥ u := dotProduct_comm _ _
    have e3 : b ⬝ᵥ one = r := by rw [dotProduct_comm]
    rw [e1, e2, e3]
    field_simp
    ring
  have hWC : ∀ u ∈ W, 0 ≤ u ⬝ᵥ (C *ᵥ u) := by
    intro u hu
    rw [hquadC]
    linarith [hW2 u hu]
  have hinj : Function.Injective (Φ.domRestrict W) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx0 : Φ x = 0 := hx
    have hu := hWC x x.2
    have h3 := h2 x
    rw [hx0, Matrix.mulVec_zero, dotProduct_zero] at h3
    have hsq : (one ⬝ᵥ (x : Fin N → ℝ)) ^ 2 / r ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hrneg.le
    have hz : one ⬝ᵥ (x : Fin N → ℝ) = 0 := by
      have : (one ⬝ᵥ (x : Fin N → ℝ)) ^ 2 / r = 0 := by linarith
      have h4 := (div_eq_zero_iff.mp this).resolve_right hr0
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h4
    have : (x : Fin N → ℝ) = Φ x + ((one ⬝ᵥ (x : Fin N → ℝ)) / r) • b := by
      rw [hΦ]; abel
    apply Subtype.ext
    rw [this, hx0, hz]
    simp
  have hfin : Module.finrank ℝ (LinearMap.range (Φ.domRestrict W)) = Module.finrank ℝ W :=
    LinearMap.finrank_range_of_inj hinj
  have hmem : ∀ v ∈ LinearMap.range (Φ.domRestrict W),
      E * (v ⬝ᵥ v) ≤ v ⬝ᵥ (QN Sig (Xdot Xm) *ᵥ v) := by
    intro v hv
    obtain ⟨x, rfl⟩ := hv
    have hxv : (Φ.domRestrict W) x = Φ x := rfl
    rw [hxv]
    have hP : piBar N *ᵥ Φ x = Φ x := qd_piBar_mulVec_self (h1 x)
    rw [qd_quad_Xdot, hP]
    have := h2 x
    have h5 := hquadC (Φ x)
    have h6 := hWC x x.2
    have h7 : (one ⬝ᵥ (x : Fin N → ℝ)) ^ 2 / r ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hrneg.le
    linarith
  exact hW1.trans (hfin ▸ eigCount_ge_of_subspace hB' _ hmem)

end Compress

section Resolvent

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- Completeness of a real orthonormal eigenbasis: `∑_k ζ_k ζ_kᵀ = 1`, entrywise. -/
private lemma qd_sum_eig_mul (hA : A.IsHermitian) (μ ν : Fin K) :
    ∑ k, (hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp ν
      = (1 : Matrix (Fin K) (Fin K) ℝ) μ ν := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) μ) ν
  rw [Unitary.coe_star, Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_apply, hA.eigenvectorUnitary_apply, hA.eigenvectorUnitary_apply, star_trivial]

/-- The shifted real inverse as a sum over the eigenbasis. -/
private lemma qd_inv_real (hA : A.IsHermitian) {E : ℝ} (hne : ∀ k, hA.eigenvalues k - E ≠ 0) :
    (A - E • (1 : Matrix (Fin K) (Fin K) ℝ))⁻¹ = ∑ k, (hA.eigenvalues k - E)⁻¹ •
      vecMulVec (hA.eigenvectorBasis k).ofLp (hA.eigenvectorBasis k).ofLp := by
  refine Matrix.inv_eq_right_inv ?_
  have hev : ∀ k, (A - E • (1 : Matrix (Fin K) (Fin K) ℝ)) *ᵥ (hA.eigenvectorBasis k).ofLp
      = (hA.eigenvalues k - E) • (hA.eigenvectorBasis k).ofLp := by
    intro k
    funext μ
    have h := congrFun (hA.mulVec_eigenvectorBasis k) μ
    rw [sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [h]
    ring
  rw [Matrix.mul_sum]
  calc ∑ k, (A - E • (1 : Matrix (Fin K) (Fin K) ℝ)) * ((hA.eigenvalues k - E)⁻¹ •
        vecMulVec (hA.eigenvectorBasis k).ofLp (hA.eigenvectorBasis k).ofLp)
      = ∑ k, vecMulVec (hA.eigenvectorBasis k).ofLp (hA.eigenvectorBasis k).ofLp := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_smul, mul_vecMulVec, hev, smul_vecMulVec, smul_smul,
          inv_mul_cancel₀ (hne k), one_smul]
    _ = 1 := by
        ext μ ν
        simp only [Matrix.sum_apply, vecMulVec_apply]
        exact qd_sum_eig_mul hA μ ν

/-- The complex resolvent as a sum over the eigenbasis. -/
private lemma qd_inv_cplx (hA : A.IsHermitian) {z : ℂ} (hne : ∀ k, (hA.eigenvalues k : ℂ) - z ≠ 0) :
    (cplx A - z • (1 : Matrix (Fin K) (Fin K) ℂ))⁻¹ = ∑ k, ((hA.eigenvalues k : ℂ) - z)⁻¹ •
      vecMulVec (cvec (hA.eigenvectorBasis k).ofLp) (cvec (hA.eigenvectorBasis k).ofLp) := by
  refine Matrix.inv_eq_right_inv ?_
  have hev : ∀ k, (cplx A - z • (1 : Matrix (Fin K) (Fin K) ℂ)) *ᵥ
      cvec (hA.eigenvectorBasis k).ofLp
      = ((hA.eigenvalues k : ℂ) - z) • cvec (hA.eigenvectorBasis k).ofLp := by
    intro k
    funext μ
    have h := congrFun (hA.mulVec_eigenvectorBasis k) μ
    have h' := congrArg (algebraMap ℝ ℂ) h
    rw [RingHom.map_mulVec] at h'
    rw [sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul] at h' ⊢
    rw [show cvec (hA.eigenvectorBasis k).ofLp
      = ⇑(algebraMap ℝ ℂ) ∘ (hA.eigenvectorBasis k).ofLp from rfl, h']
    simp only [Complex.coe_algebraMap, Complex.ofReal_mul, Function.comp_apply]
    ring
  rw [Matrix.mul_sum]
  calc ∑ k, (cplx A - z • (1 : Matrix (Fin K) (Fin K) ℂ)) * (((hA.eigenvalues k : ℂ) - z)⁻¹ •
        vecMulVec (cvec (hA.eigenvectorBasis k).ofLp) (cvec (hA.eigenvectorBasis k).ofLp))
      = ∑ k, vecMulVec (cvec (hA.eigenvectorBasis k).ofLp)
          (cvec (hA.eigenvectorBasis k).ofLp) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_smul, mul_vecMulVec, hev, smul_vecMulVec, smul_smul,
          inv_mul_cancel₀ (hne k), one_smul]
    _ = 1 := by
        ext μ ν
        simp only [Matrix.sum_apply, vecMulVec_apply, cvec]
        have h := congrArg (fun x : ℝ => (x : ℂ)) (qd_sum_eig_mul hA μ ν)
        simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
        rw [h]
        by_cases hμν : μ = ν <;> simp [one_apply, hμν]

/-- The termwise comparison `d⁻¹ ≤ Re (d − iδ)⁻¹ + Im (d − iδ)⁻¹` for `|d| ≥ δ > 0`. -/
private lemma qd_term_le {d δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ |d|) :
    d⁻¹ ≤ (((d : ℂ) - δ * Complex.I)⁻¹).re + (((d : ℂ) - δ * Complex.I)⁻¹).im := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
    linarith
  have hz : (d : ℂ) - δ * Complex.I = ⟨d, -δ⟩ := by
    apply Complex.ext <;> simp
  rw [hz, Complex.inv_re, Complex.inv_im, Complex.normSq_mk]
  have hpos : 0 < d * d + -δ * -δ := by nlinarith [mul_pos hδ hδ, mul_self_nonneg d]
  have key : d / (d * d + -δ * -δ) + -(-δ) / (d * d + -δ * -δ) - d⁻¹ =
      δ * (d - δ) / (d * (d * d + δ * δ)) := by
    field_simp
    ring
  have hnn : 0 ≤ δ * (d - δ) / (d * (d * d + δ * δ)) := by
    rcases lt_or_gt_of_ne hd0 with h | h
    · have h1 : d ≤ -δ := by
        rw [abs_of_neg h] at hd; linarith
      apply div_nonneg_of_nonpos
      · nlinarith
      · nlinarith [mul_pos hδ hδ]
    · have h1 : δ ≤ d := by
        rw [abs_of_pos h] at hd; exact hd
      apply div_nonneg
      · nlinarith
      · positivity
  linarith

/-- Real-axis comparison: if every eigenvalue of `A` is at distance `≥ δ` from `E`, then
`⟨v, (A − E)⁻¹ v⟩ ≤ Re⟨v, (A − E − iδ)⁻¹ v⟩ + Im⟨v, (A − E − iδ)⁻¹ v⟩`. -/
theorem resolvent_real_le {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (v : Fin K → ℝ) {E δ : ℝ} (hδ : 0 < δ) (hgap : ∀ j, δ ≤ |specOf A j - E|) :
    v ⬝ᵥ ((A - E • (1 : Matrix (Fin K) (Fin K) ℝ))⁻¹ *ᵥ v) ≤
      (testBilin v ((cplx A - ((E : ℂ) + δ * Complex.I) • (1 : Matrix (Fin K) (Fin K) ℂ))⁻¹)
          v).re +
        (testBilin v ((cplx A - ((E : ℂ) + δ * Complex.I) • (1 : Matrix (Fin K) (Fin K) ℂ))⁻¹)
          v).im := by
  rw [specOf_eq hA] at hgap
  have hne : ∀ k, hA.eigenvalues k - E ≠ 0 := by
    intro k h
    have := hgap k
    rw [h, abs_zero] at this
    linarith
  have hnec : ∀ k, (hA.eigenvalues k : ℂ) - ((E : ℂ) + δ * Complex.I) ≠ 0 := by
    intro k h
    have := congrArg Complex.im h
    simp at this
    linarith
  set u : Fin K → Fin K → ℝ := fun k => (hA.eigenvectorBasis k).ofLp with hu
  have hreal : v ⬝ᵥ ((A - E • (1 : Matrix (Fin K) (Fin K) ℝ))⁻¹ *ᵥ v) =
      ∑ k, (hA.eigenvalues k - E)⁻¹ * (u k ⬝ᵥ v) ^ 2 := by
    rw [qd_inv_real hA hne, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, vecMulVec_mulVec]
    simp [sq, hu]
    exact Or.inl (Or.inl (dotProduct_comm _ _))
  have hcplx : testBilin v ((cplx A - ((E : ℂ) + δ * Complex.I) •
      (1 : Matrix (Fin K) (Fin K) ℂ))⁻¹) v =
      ∑ k, (((hA.eigenvalues k : ℂ) - ((E : ℂ) + δ * Complex.I))⁻¹) * ((u k ⬝ᵥ v : ℝ) : ℂ) ^ 2 := by
    rw [qd_inv_cplx hA hnec]
    unfold testBilin
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, vecMulVec_mulVec]
    simp [sq, hu, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [cvec]
    ring
  rw [hreal, hcplx, Complex.re_sum, Complex.im_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := qd_term_le hδ (hgap k)
  have h2 : (hA.eigenvalues k : ℂ) - ((E : ℂ) + δ * Complex.I) =
      ((hA.eigenvalues k - E : ℝ) : ℂ) - δ * Complex.I := by push_cast; ring
  rw [h2]
  rw [← Complex.ofReal_pow]
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal]
  nlinarith [sq_nonneg (u k ⬝ᵥ v)]

end Resolvent

/-! ### Instances -/

/-- `π̄ 1 = 0` at `N = 2`. -/
example : piBar 2 *ᵥ (fun _ => (1 : ℝ)) = 0 := piBar_mulVec_one (by norm_num)

/-- `A = diag(1, 0)` is positive semidefinite and singular, and `λ_2 = 0`. -/
example : sortedEig (diagonal ![(1 : ℝ), 0]) 2 = 0 :=
  sortedEig_last_eq_zero
    (Matrix.posSemidef_diagonal_iff.mpr fun i => by fin_cases i <;> simp)
    (by simp [Matrix.det_diagonal, Fin.prod_univ_two]) (by norm_num)

/-- `Σ = I₂`, `X = I₂`, `N = 2`: `Q̇`'s companion is positive semidefinite, singular, and has
last eigenvalue `0`. -/
example : (QdotN (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef :=
  QdotN_posSemidef Matrix.PosSemidef.one _

example : (QdotN (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 :=
  QdotN_det _ _ (by norm_num)

example : sortedEig (QdotN (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)) 2 = 0 :=
  sortedEig_QdotN_last Matrix.PosSemidef.one _ (by norm_num)

/-- `M = 1`, `σ = 1`, `N = 2`, `w = i`. -/
example : fC 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I =
    fC (2 - 1) (fun _ : Fin 1 => (1 : ℝ)) Complex.I -
      (fC (2 - 1) (fun _ : Fin 1 => (1 : ℝ)) Complex.I + Complex.I⁻¹) / (2 : ℕ) :=
  fC_pred _ (le_refl 2) _

/-- `M = 1`, `σ = 1`, `N = 2`, `z = i`. -/
example : mFun (2 - 1) (fun _ : Fin 1 => (1 : ℝ)) Complex.I =
    mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (Complex.I - (Complex.I +
      (mFun (2 - 1) (fun _ : Fin 1 => (1 : ℝ)) Complex.I)⁻¹) / (2 : ℕ)) :=
  mFun_pred_eq _ (fun _ => zero_le_one) (le_refl 2) (by simp)

/-- `Σ = 1` (`M = 1`), `N = 2`, `X = (1 0)`: `B = diag(1, 0)`, `E = 1/4`. -/
example : eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (Xdot (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)))
      (1 / 4) ≤ eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ))
      (1 / 4) :=
  eigCount_compress_le Matrix.isHermitian_one _ (by norm_num)

example : eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ))
      (3 / 4) ≤ eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (Xdot (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ))) (3 / 4) + 1 :=
  eigCount_le_compress_add_one Matrix.isHermitian_one _ _

/-- The secular count at `B = diag(1, 0)`, `E = 1/4`: `B − E` is invertible and
`1ᵀ (B − E)⁻¹ 1 = 4/3 − 4 < 0`. -/
example : eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (Xdot (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)))
      (1 / 4) = eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)) (1 / 4) := by
  have hB : QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) =
      !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QN, Matrix.mul_apply]
  have hC : QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) -
      (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![3 / 4, 0; 0, -1 / 4] := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have hinv : (!![3 / 4, 0; 0, -1 / 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![4 / 3, 0; 0, -4] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine eigCount_compress_secular Matrix.isHermitian_one _ (by norm_num) ?_ ?_
  · rw [hC]
    refine isUnit_iff_exists_inv.mpr ⟨!![4 / 3, 0; 0, -4], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hC, hinv]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
    norm_num

/-- `A = diag(0, 3)`, `E = 1`, `δ = 1`, `v = (1, 1)`: the gaps are `1` and `2`. -/
example : ![(1 : ℝ), 1] ⬝ᵥ ((diagonal ![(0 : ℝ), 3] - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ
      ![(1 : ℝ), 1]) ≤
    (testBilin ![(1 : ℝ), 1] ((cplx (diagonal ![(0 : ℝ), 3]) -
      (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹)
        ![(1 : ℝ), 1]).re +
    (testBilin ![(1 : ℝ), 1] ((cplx (diagonal ![(0 : ℝ), 3]) -
      (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹)
        ![(1 : ℝ), 1]).im := by
  refine resolvent_real_le (isHermitian_diagonal _) _ (by norm_num) fun j => ?_
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal ![(0 : ℝ), 3]
  rw [he]
  simp only [Function.comp]
  generalize e j = i
  fin_cases i <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- `Σ_k Ṅ_k = (N − 1) ∧ rank Σ` is Lemma A.1 at `N − 1`. -/
example (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 2 ≤ N) (hS : (posVals σ).Nonempty) :
    ∑ k ∈ Finset.Icc 1 (numBands (N - 1) σ), bandCount (N - 1) σ k =
      min ((N - 1 : ℕ) : ℝ) (Finset.univ.filter fun i => 0 < σ i).card :=
  sum_bandCount (N - 1) σ hσ (by omega) hS

#print axioms piBar_mulVec_one
#print axioms sortedEig_last_eq_zero
#print axioms QdotN_posSemidef
#print axioms QdotN_det
#print axioms sortedEig_QdotN_last
#print axioms fC_pred
#print axioms mFun_pred_eq
#print axioms eigCount_compress_le
#print axioms eigCount_le_compress_add_one
#print axioms eigCount_compress_secular
#print axioms resolvent_real_le

end Anisotropic
