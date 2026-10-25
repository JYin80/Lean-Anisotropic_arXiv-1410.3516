import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.LinAlg.Basic
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistent
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # `G^W`, `Π^W`, the standing bound, the domain `𝐃^W` and Definition 12.1 (the four laws) -/

/-- `G^W(z) = (W + A − z)⁻¹`. -/
def GW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `Π^W(z) = (−m^W(z) + A − z)⁻¹`. -/
def piW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (cplx A - (mW (specOf A) z + z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `N⁻¹ tr G^W(z)`. -/
def mNW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * trace (GW A Wm z)

/-- The eigenvalues of a real symmetric `A` are bounded by `‖A‖`. -/
theorem abs_specOf_le_norm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (i : Fin N) : |specOf A i| ≤ ‖A‖ := by
  rw [specOf_eq hA]
  have h := Matrix.l2_opNorm_mulVec A (hA.eigenvectorBasis i)
  have hv : (EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ ⇑(hA.eigenvectorBasis i))
      = hA.eigenvalues i • hA.eigenvectorBasis i := by
    rw [hA.mulVec_eigenvectorBasis i]
    rfl
  rw [hv, norm_smul, (hA.eigenvectorBasis).orthonormal.1 i, mul_one] at h
  simpa using h

/-- The standing bound of §12.1: `|−m^W(z) + aᵢ − z| ≥ τ` on `S`. -/
def StandingBoundW {N : ℕ} (τ : ℝ) (a : Fin N → ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ i, τ ≤ ‖-(mW a z) + (a i : ℂ) - z‖

/-- Conjugating a bilinear form by a real matrix `Q` rotates the test vectors by `Q`. -/
private lemma defs_testBilin_conj {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (B : Matrix ι ι ℂ)
    (v w : ι → ℝ) : testBilin v ((cplx Q)ᵀ * B * cplx Q) w = testBilin (Q *ᵥ v) B (Q *ᵥ w) := by
  have hc : ∀ u : ι → ℝ, cplx Q *ᵥ (fun t => (u t : ℂ)) = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    ext s
    simp [cplx, Matrix.mulVec, dotProduct]
  have hv : ∀ u : ι → ℝ, (fun s => (u s : ℂ)) ᵥ* (cplx Q)ᵀ = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    rw [Matrix.vecMul_transpose]
    exact hc u
  unfold testBilin
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hv, hc]

/-- A real matrix `Q` with `Qᵀ Q = 1` preserves the Euclidean norm of a test vector. -/
private lemma defs_testNorm_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) (v : ι → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`, with `U Uᵀ = 1`, `Uᵀ U = 1`
and `A = U diag(λ) Uᵀ`. -/
private lemma defs_eig_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- For `A = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w` bounded below in modulus by `τ`,
`(A − w)⁻¹` is the rotated diagonal `(λₖ − w)⁻¹`. -/
private lemma defs_resolvent_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx A = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hAU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - w) =
        diagonal (fun k => (l k : ℂ)) - w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  refine Matrix.inv_eq_right_inv ?_
  rw [hM]
  calc cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ *
        (cplx U * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ)
      = cplx U * diagonal (fun k => (l k : ℂ) - w) * ((cplx U)ᵀ * cplx U) *
        diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
        have : (fun k => ((l k : ℂ) - w) * ((l k : ℂ) - w)⁻¹) = fun _ => 1 := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]

/-- The standing bound gives `‖Π^W‖ ≤ τ⁻¹` (§12.1). -/
theorem norm_piW_le {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S) {z : ℂ} (hz : z ∈ S)
    (v w : Fin N → ℝ) : ‖testBilin v (piW A z) w‖ ≤ τ⁻¹ * testNorm v * testNorm w := by
  obtain ⟨U, hUU, hUU', hAU⟩ := defs_eig_decomp hA
  have hd : ∀ k, τ ≤ ‖(hA.eigenvalues k : ℂ) - (mW (specOf A) z + z)‖ := by
    intro k
    have h := hS z hz k
    rw [specOf_eq hA] at h
    have e : -(mW hA.eigenvalues z) + (hA.eigenvalues k : ℂ) - z
        = (hA.eigenvalues k : ℂ) - (mW hA.eigenvalues z + z) := by ring
    rw [e] at h
    rwa [specOf_eq hA]
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - (mW (specOf A) z + z) ≠ 0 := fun k h0 => by
    have := hd k
    rw [h0, norm_zero] at this
    linarith
  have hpi : piW A z = (cplx U) * diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹) * (cplx U)ᵀ :=
    defs_resolvent_eq hUU hUU' hAU hne
  have hQ : (cplx Uᵀ)ᵀ = cplx U := by simp [cplx, Matrix.transpose_map]
  have hQ' : cplx Uᵀ = (cplx U)ᵀ := by simp [cplx, Matrix.transpose_map]
  have hrot : testBilin v (piW A z) w = testBilin (Uᵀ *ᵥ v) (diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹)) (Uᵀ *ᵥ w) := by
    rw [hpi, ← defs_testBilin_conj Uᵀ, hQ, hQ']
  have hnv : testNorm (Uᵀ *ᵥ v) = testNorm v := defs_testNorm_orth (by simpa using hUU) v
  have hnw : testNorm (Uᵀ *ᵥ w) = testNorm w := defs_testNorm_orth (by simpa using hUU) w
  rw [hrot, ← hnv, ← hnw]
  set x := Uᵀ *ᵥ v
  set y := Uᵀ *ᵥ w
  have hdiag : testBilin x (diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹)) y =
      ∑ k, ((x k : ℂ) * (((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹ * (y k : ℂ))) := by
    simp [testBilin, dotProduct, Matrix.mulVec_diagonal]
  rw [hdiag]
  have hτi : ∀ k, ‖((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹‖ ≤ τ⁻¹ := by
    intro k
    rw [norm_inv]
    exact inv_anti₀ hτ (hd k)
  calc ‖∑ k, ((x k : ℂ) * (((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹ * (y k : ℂ)))‖
      ≤ ∑ k, ‖(x k : ℂ) * (((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹ * (y k : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, τ⁻¹ * (|x k| * |y k|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have := hτi k
        have h0 : 0 ≤ |x k| := abs_nonneg _
        have h1 : 0 ≤ |y k| := abs_nonneg _
        nlinarith [mul_nonneg h0 h1]
    _ = τ⁻¹ * ∑ k, |x k| * |y k| := by rw [Finset.mul_sum]
    _ ≤ τ⁻¹ * (testNorm x * testNorm y) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hτ.le)
        have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |x k|) (fun k => |y k|)
        simpa [testNorm, sq_abs] using h
    _ = τ⁻¹ * testNorm x * testNorm y := by ring

/-- At a solution `m` of `m = m_A(z + m)` with `Im m > 0` and `Im z > 0`,
`N⁻¹ ∑ᵢ |aᵢ − (z + m)|⁻² < 1`. -/
private lemma defs_S_lt_one {N : ℕ} (a : Fin N → ℝ) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (heq : m = stieltjesA a (z + m)) :
    (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - (z + m)))⁻¹ < 1 := by
  have him := congrArg Complex.im heq
  have h : (stieltjesA a (z + m)).im =
      (z + m).im * ((N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - (z + m)))⁻¹) := by
    unfold stieltjesA
    rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
      Complex.im_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inv_im]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    ring
  rw [h] at him
  simp only [Complex.add_im] at him
  set S := (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - (z + m)))⁻¹
  by_contra hS
  push Not at hS
  nlinarith

/-- If `Im w > 0` and `N⁻¹ ∑ᵢ |aᵢ − w|⁻² < 1` with `N ≥ 1`, some `|aᵢ − w|` exceeds `1`. -/
private lemma defs_exists_norm_gt_one {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ}
    (hw : 0 < w.im) (hS : (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ < 1) :
    ∃ i, 1 < ‖(a i : ℂ) - w‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hcon
  push Not at hcon
  have hall : ∀ i, 1 ≤ (Complex.normSq ((a i : ℂ) - w))⁻¹ := by
    intro i
    by_cases h0 : (a i : ℂ) - w = 0
    · exfalso
      have := congrArg Complex.im h0
      simp at this
      linarith
    · have hpos : 0 < Complex.normSq ((a i : ℂ) - w) := Complex.normSq_pos.2 h0
      have hle : Complex.normSq ((a i : ℂ) - w) ≤ 1 := by
        rw [← Complex.sq_norm]
        have := hcon i
        nlinarith [norm_nonneg ((a i : ℂ) - w)]
      exact one_le_inv_iff₀.2 ⟨hpos, hle⟩
  have hsum : (N : ℝ) ≤ ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ := by
    calc (N : ℝ) = ∑ _i : Fin N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hall i
  have : 1 ≤ (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ := by
    rw [inv_mul_eq_div, le_div_iff₀ hNpos]
    linarith
  linarith

/-- A sufficient condition for the standing bound: `|aᵢ| ≤ r < 1/2` gives it on all of `ℂ₊`
with constant `1 − 2r` (`S(w) < 1` forces `maxᵢ |aᵢ − w| > 1`). -/
theorem standingBoundW_of_lt {N : ℕ} (hN : 1 ≤ N) {a : Fin N → ℝ} {r : ℝ}
    (ha : ∀ i, |a i| ≤ r) (hr : r < 1 / 2) :
    StandingBoundW (1 - 2 * r) a {z | 0 < z.im} := by
  intro z hz j
  have hz : 0 < z.im := hz
  obtain ⟨hm, heq⟩ := mW_spec hN a hz
  set m := mW a z
  have hS := defs_S_lt_one a hz hm heq
  obtain ⟨i₀, hi₀⟩ := defs_exists_norm_gt_one hN a (by simp only [Complex.add_im]; linarith) hS
  have e : -m + (a j : ℂ) - z = (a j : ℂ) - (z + m) := by ring
  rw [e]
  have h1 : ‖(a i₀ : ℂ) - (z + m)‖ ≤ ‖(a j : ℂ) - (z + m)‖ + 2 * r := by
    have h2 : (a i₀ : ℂ) - (z + m) = ((a j : ℂ) - (z + m)) + ((a i₀ : ℂ) - (a j : ℂ)) := by ring
    rw [h2]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h3 := abs_le.1 (ha i₀)
    have h4 := abs_le.1 (ha j)
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  linarith

/-- `𝐃^W(τ, N) = {|E| ≤ τ⁻¹, N^{−1+τ} ≤ η ≤ τ⁻¹}`. -/
def domW (τ : ℝ) (N : ℕ) : Set ℂ :=
  {z | 0 < z.im ∧ |z.re| ≤ τ⁻¹ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ τ⁻¹}

/-- Definition 12.1: `S ⊆ 𝐃^W` closed under increasing `η` at fixed `E` inside `𝐃^W`. -/
def SpectralDomainW (τ : ℝ) (N : ℕ) (S : Set ℂ) : Prop :=
  S ⊆ domW τ N ∧ ∀ z ∈ S, ∀ w ∈ domW τ N, w.re = z.re → z.im ≤ w.im → w ∈ S

section Laws

variable {Ω : Type*} [MeasureSpace Ω]

/-- Definition 12.1 (i) at fixed `N, ε, D`: `(G^W − Π^W)_{st} = O_≺(Ψ^W)` on `S`. -/
def EntrywiseLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ s t, ODomAt N ε D (fun ω => (GW A (W ω) z - piW A z) s t)
    (fun _ => PsiW (specOf A) z)

/-- Definition 12.1 (ii) at fixed `N, ε, D`: `G^W − Π^W = O_≺(Ψ^W)` on `S`. -/
def AnisotropicLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomMatAt N ε D (fun ω => GW A (W ω) z - piW A z) (fun _ => PsiW (specOf A) z)

/-- Definition 12.1 (iii) at fixed `N, ε, D`: `N⁻¹ tr G^W − m^W = O_≺((Nη)⁻¹)` on `S`. -/
def AveragedLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mNW A (W ω) z - mW (specOf A) z) (fun _ => 1 / (N * z.im))

/-- The averaged law with control `Φ`: `N⁻¹ tr G^W − m^W = O_≺(Φ)` on `S`. -/
def AveragedPhiLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mNW A (W ω) z - mW (specOf A) z) (fun _ => Φ z)

end Laws

/-- `ϱ^W(E) = lim_{η↓0} π⁻¹ Im m^W(E + iη)` (§12.1). -/
def rhoW {N : ℕ} (a : Fin N → ℝ) (E : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun η => (mW a ⟨E, η⟩).im / Real.pi

/-- The interval-support condition of §12.1: the support of `ϱ^W` is an interval `[Lm, Lp]`. -/
def IntervalSupportW {N : ℕ} (a : Fin N → ℝ) (Lm Lp : ℝ) : Prop :=
  Lm < Lp ∧ tsupport (rhoW a) = Set.Icc Lm Lp

/-- (b) of Theorem 12.2 on `S`: `Ψ^W ≤ N^{−1/4−c₀}`. -/
def PsiSmallW {N : ℕ} (c₀ : ℝ) (a : Fin N → ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, PsiW a z ≤ (N : ℝ) ^ (-1 / 4 - c₀)

/-- `𝐃^W(τ, N)` is itself a spectral domain. -/
theorem spectralDomainW_domW (τ : ℝ) (N : ℕ) : SpectralDomainW τ N (domW τ N) :=
  ⟨le_rfl, fun _ _ _ hw _ _ => hw⟩

/-- The standing bound for `aEx N` on `𝐃^W(1/2, N)` (`|aᵢ| ≤ 1/4`, constant `1 − 2/4`). -/
theorem standingBoundW_aEx {N : ℕ} (hN : 1 ≤ N) :
    StandingBoundW (1 / 2) (specOf (aEx N)) (domW (1 / 2) N) := by
  intro z hz i
  have h := standingBoundW_of_lt hN
    (fun k => (abs_specOf_le_norm (aEx_isHermitian N) k).trans (norm_aEx_le hN))
    (by norm_num) z hz.1 i
  norm_num at h ⊢
  exact h

/-! ## Nondegenerate instance `A = aEx 4`, `z = i`, `τ = 1/2` -/

/-- The eigenvalues of `aEx 4` (a nonzero matrix) are bounded by its norm. -/
example (i : Fin 4) : |specOf (aEx 4) i| ≤ ‖aEx 4‖ :=
  abs_specOf_le_norm (aEx_isHermitian 4) i

/-- `|aᵢ| ≤ 1/4 < 1/2` for the eigenvalues of `aEx 4`, hence the standing bound on `ℂ₊`. -/
example : StandingBoundW (1 - 2 * (1 / 4)) (specOf (aEx 4)) {z | 0 < z.im} :=
  standingBoundW_of_lt (by norm_num)
    (fun i => (abs_specOf_le_norm (aEx_isHermitian 4) i).trans (norm_aEx_le (by norm_num)))
    (by norm_num)

#print axioms abs_specOf_le_norm
#print axioms norm_piW_le
#print axioms standingBoundW_of_lt
#print axioms standingBoundW_aEx
#print axioms spectralDomainW_domW
#print axioms GW
#print axioms piW
#print axioms mNW
#print axioms StandingBoundW
#print axioms domW
#print axioms SpectralDomainW
#print axioms EntrywiseLawWAt
#print axioms AnisotropicLawWAt
#print axioms AveragedLawWAt
#print axioms AveragedPhiLawWAt
#print axioms rhoW
#print axioms IntervalSupportW
#print axioms PsiSmallW

end Anisotropic
