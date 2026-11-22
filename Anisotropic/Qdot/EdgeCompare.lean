module

public import Anisotropic.Comparison.Ensemble
public import Anisotropic.Comparison.Interpolation
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.Reduction
public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.EdgeUniv.Swap
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Qdot.Defs
public import Anisotropic.Qdot.EdgeDefs
public import Anisotropic.Qdot.LocalLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The reflection `R_μ`, the entry derivatives of the smoothed count of `Q_N(Ẋ)`, and the entry bounds for `G(Ẋ R_μ)` -/

/-! ## The unit vector `π̄ e_μ / |π̄ e_μ|` and the reflection exchanging it with `e_μ` -/

/-- `|π̄ e_μ| = (1 - 1/N)^{1/2}` (§11.2). -/
def dotLen (N : ℕ) : ℝ := √(1 - (N : ℝ)⁻¹)

/-- The unit vector `v̂_μ = π̄ e_μ / |π̄ e_μ|`; `∂Ẋ/∂X_{iμ} = e_i (π̄ e_μ)ᵀ` (§11.2). -/
def dotVec (N : ℕ) (μ : Fin N) : Fin N → ℝ := fun ν => piBar N ν μ / dotLen N

/-- The reflection `R_μ = 1 - (1 - |π̄ e_μ|)⁻¹ w wᵀ`, `w = e_μ - v̂_μ`; for `N ≥ 2` it is
orthogonal and exchanges `e_μ` and `v̂_μ`. -/
def dotRefl (N : ℕ) (μ : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  1 - (1 - dotLen N)⁻¹ • vecMulVec (Pi.single μ 1 - dotVec N μ) (Pi.single μ 1 - dotVec N μ)

private lemma ec_piBar_apply (a b : Fin N) :
    piBar N a b = (if a = b then 1 else 0) - (N : ℝ)⁻¹ := by
  simp [piBar, Matrix.one_apply]

private lemma ec_piBar_symm (a b : Fin N) : piBar N a b = piBar N b a := by
  by_cases h : a = b
  · rw [h]
  · simp [ec_piBar_apply, h, Ne.symm h]

private lemma ec_sum_piBar (hN : 0 < N) (μ : Fin N) : ∑ ν, piBar N ν μ = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [ec_piBar_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  simp

private lemma ec_sum_piBar_mul (hN : 0 < N) (κ μ : Fin N) :
    ∑ ν, piBar N κ ν * piBar N ν μ = piBar N κ μ := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∀ ν, piBar N κ ν * piBar N ν μ =
      (if κ = ν then piBar N ν μ else 0) - (N : ℝ)⁻¹ * piBar N ν μ := fun ν => by
    rw [ec_piBar_apply κ ν]
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.mul_sum, ec_sum_piBar hN, mul_zero, sub_zero]

private lemma ec_dotLen_sq (hN : 0 < N) : dotLen N ^ 2 = 1 - (N : ℝ)⁻¹ := by
  unfold dotLen
  rw [Real.sq_sqrt]
  have : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  linarith

private lemma ec_inv_le_half (hN : 2 ≤ N) : (N : ℝ)⁻¹ ≤ 1 / 2 := by
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- `1/2 ≤ |π̄ e_μ| < 1` for `N ≥ 2`. -/
theorem dot_dotLen_bounds (hN : 2 ≤ N) : 1 / 2 ≤ dotLen N ∧ dotLen N < 1 := by
  have h2 := ec_inv_le_half hN
  have hpos : 0 < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hsq := ec_dotLen_sq (N := N) (by omega)
  have h0 : 0 ≤ dotLen N := Real.sqrt_nonneg _
  constructor
  · nlinarith
  · nlinarith

private lemma ec_dotLen_pos (hN : 2 ≤ N) : 0 < dotLen N := by
  linarith [(dot_dotLen_bounds hN).1]

private lemma ec_piBar_eq (hN : 2 ≤ N) (μ ν : Fin N) :
    piBar N ν μ = dotLen N * dotVec N μ ν := by
  unfold dotVec
  field_simp [(ec_dotLen_pos hN).ne']

private lemma ec_dotVec_self (hN : 2 ≤ N) (μ : Fin N) : dotVec N μ μ = dotLen N := by
  have hL := ec_dotLen_pos hN
  have hsq := ec_dotLen_sq (N := N) (by omega)
  unfold dotVec
  rw [ec_piBar_apply]
  simp only [ite_true]
  rw [← hsq]
  field_simp

private lemma ec_sum_dotVec_sq (hN : 2 ≤ N) (μ : Fin N) : ∑ ν, dotVec N μ ν ^ 2 = 1 := by
  have hL := ec_dotLen_pos hN
  have hsq := ec_dotLen_sq (N := N) (by omega)
  have hm := ec_sum_piBar_mul (N := N) (by omega) μ μ
  unfold dotVec
  have e : ∀ ν, (piBar N ν μ / dotLen N) ^ 2 = piBar N μ ν * piBar N ν μ / dotLen N ^ 2 :=
    fun ν => by rw [ec_piBar_symm μ ν]; ring
  rw [Finset.sum_congr rfl fun ν _ => e ν, ← Finset.sum_div, hm, ec_piBar_apply]
  simp only [ite_true]
  rw [← hsq]
  field_simp

private lemma ec_piBar_dotVec (hN : 2 ≤ N) (κ μ : Fin N) :
    ∑ ν, piBar N κ ν * dotVec N μ ν = dotVec N μ κ := by
  have hm := ec_sum_piBar_mul (N := N) (by omega) κ μ
  unfold dotVec
  simp only [mul_div_assoc', ← Finset.sum_div, hm]

/-- `w = e_μ - v̂_μ`. -/
private def ecW (N : ℕ) (μ : Fin N) : Fin N → ℝ := Pi.single μ 1 - dotVec N μ

private lemma ec_W_dot_W (hN : 2 ≤ N) (μ : Fin N) :
    ecW N μ ⬝ᵥ ecW N μ = 2 * (1 - dotLen N) := by
  have e : ∀ ν, ecW N μ ν * ecW N μ ν =
      (if ν = μ then 1 - 2 * dotVec N μ μ else 0) + dotVec N μ ν ^ 2 := fun ν => by
    unfold ecW
    by_cases h : ν = μ
    · subst h; simp; ring
    · simp [h]; ring
  simp only [dotProduct, e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ec_sum_dotVec_sq hN, ec_dotVec_self hN]
  ring

private lemma ec_W_dot_v (hN : 2 ≤ N) (μ : Fin N) :
    ecW N μ ⬝ᵥ dotVec N μ = dotLen N - 1 := by
  have e : ∀ ν, ecW N μ ν * dotVec N μ ν =
      (if ν = μ then dotVec N μ μ else 0) - dotVec N μ ν ^ 2 := fun ν => by
    unfold ecW
    by_cases h : ν = μ
    · subst h; simp; ring
    · simp [h]; ring
  simp only [dotProduct, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ec_sum_dotVec_sq hN, ec_dotVec_self hN]

private lemma ec_W_dot_single (hN : 2 ≤ N) (μ : Fin N) :
    ecW N μ ⬝ᵥ Pi.single μ 1 = 1 - dotLen N := by
  rw [dotProduct_single, mul_one]
  unfold ecW
  simp [ec_dotVec_self hN]

private lemma ec_refl_eq (μ : Fin N) :
    dotRefl N μ = 1 - (1 - dotLen N)⁻¹ • vecMulVec (ecW N μ) (ecW N μ) := rfl

/-- `R_μᵀ = R_μ`. -/
theorem dot_dotRefl_transpose (μ : Fin N) : (dotRefl N μ)ᵀ = dotRefl N μ := by
  rw [ec_refl_eq, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

/-- `R_μ R_μ = 1` for `N ≥ 2`. -/
theorem dot_dotRefl_mul_self (hN : 2 ≤ N) (μ : Fin N) : dotRefl N μ * dotRefl N μ = 1 := by
  have hL := (dot_dotLen_bounds hN).2
  have h1 : (1 - dotLen N) ≠ 0 := by linarith
  set c := (1 - dotLen N)⁻¹ with hc
  set P := vecMulVec (ecW N μ) (ecW N μ) with hP
  have hPP : P * P = (2 * (1 - dotLen N)) • P := by
    rw [hP, vecMulVec_mul_vecMulVec, ec_W_dot_W hN, vecMulVec_smul]
  have hcc : c * c * (2 * (1 - dotLen N)) = 2 * c := by
    rw [hc]; field_simp
  rw [ec_refl_eq, ← hc, ← hP, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, smul_mul_smul_comm, hPP, smul_smul, hcc]
  rw [two_mul, add_smul]
  abel

private lemma ec_refl_mulVec_single (hN : 2 ≤ N) (μ : Fin N) :
    dotRefl N μ *ᵥ Pi.single μ 1 = dotVec N μ := by
  have hL := (dot_dotLen_bounds hN).2
  have h1 : (1 - dotLen N) ≠ 0 := by linarith
  rw [ec_refl_eq, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ec_W_dot_single hN,
    op_smul_eq_smul, smul_smul, inv_mul_cancel₀ h1, one_smul]
  unfold ecW
  abel

private lemma ec_refl_mulVec_dotVec (hN : 2 ≤ N) (μ : Fin N) :
    dotRefl N μ *ᵥ dotVec N μ = Pi.single μ 1 := by
  have hL := (dot_dotLen_bounds hN).2
  have h1 : (1 - dotLen N) ≠ 0 := by linarith
  have e : (1 - dotLen N)⁻¹ * (dotLen N - 1) = -1 := by field_simp; ring
  rw [ec_refl_eq, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ec_W_dot_v hN,
    op_smul_eq_smul, smul_smul, e, neg_one_smul]
  unfold ecW
  abel

/-- The column `μ` of `R_μ` is `v̂_μ`. -/
private lemma ec_refl_col (hN : 2 ≤ N) (μ a : Fin N) : dotRefl N μ a μ = dotVec N μ a := by
  have := congrFun (ec_refl_mulVec_single hN μ) a
  rwa [mulVec_single_one] at this

private lemma ec_refl_symm_apply (μ a b : Fin N) : dotRefl N μ a b = dotRefl N μ b a := by
  have := congrFun (congrFun (dot_dotRefl_transpose μ) b) a
  rwa [transpose_apply] at this

/-- `(π̄ R_μ)_{μ a} = |π̄ e_μ| δ_{μ a}`. -/
private lemma ec_piBar_refl (hN : 2 ≤ N) (μ a : Fin N) :
    ∑ ν, piBar N μ ν * dotRefl N μ ν a = if a = μ then dotLen N else 0 := by
  have e : ∀ ν, piBar N μ ν * dotRefl N μ ν a = dotLen N * (dotRefl N μ a ν * dotVec N μ ν) :=
    fun ν => by rw [ec_piBar_symm, ec_piBar_eq hN, ec_refl_symm_apply μ ν a]; ring
  simp only [e, ← Finset.mul_sum]
  have h := congrFun (ec_refl_mulVec_dotVec hN μ) a
  simp only [mulVec, dotProduct] at h
  rw [h, Pi.single_apply]
  split_ifs <;> simp

/-! ## The entry `(i, μ)` of `Ẋ` in the rotated frame -/

private lemma ec_Xupd_eq {K : ℕ} (Xm : Matrix (Fin K) (Fin N) ℝ) (i : Fin K) (μ : Fin N) (t : ℝ) :
    Xupd Xm i μ t = Xm + (t - Xm i μ) • Matrix.single i μ 1 := by
  ext j ν
  by_cases h : j = i ∧ ν = μ
  · obtain ⟨rfl, rfl⟩ := h
    simp [Xupd]
  · have h' : ¬ (i = j ∧ μ = ν) := fun h'' => h ⟨h''.1.symm, h''.2.symm⟩
    simp [Xupd, h, Matrix.single, h']

private lemma ec_single_piBar_refl {K : ℕ} (hN : 2 ≤ N) (i : Fin K) (μ : Fin N) :
    Matrix.single i μ (1 : ℝ) * piBar N * dotRefl N μ = dotLen N • Matrix.single i μ 1 := by
  ext j a
  rw [Matrix.mul_assoc, Matrix.smul_apply]
  by_cases hj : j = i
  · subst hj
    rw [single_mul_apply_same, one_mul, Matrix.mul_apply, ec_piBar_refl hN]
    by_cases ha : a = μ
    · subst ha; simp
    · simp [ha, Matrix.single, Ne.symm ha]
  · rw [single_mul_apply_of_ne (c := (1 : ℝ)) i μ j a hj]
    simp [Matrix.single, Ne.symm hj]

/-- In the frame `R_μ`, the entry `(i, μ)` of `X` acts on `Ẋ R_μ` as the entry `(i, μ)` with
the factor `|π̄ e_μ|`: `Ẋ(X^{t}_{(iμ)}) R_μ = (Ẋ R_μ)^{s}_{(iμ)}` with
`s = (Ẋ R_μ)_{iμ} + |π̄ e_μ| (t - X_{iμ})` (§11.2, `∂Ẋ/∂X_{iμ} = e_i (π̄ e_μ)ᵀ`). -/
theorem dot_Xdot_Xupd_mul (hN : 2 ≤ N) (Xm : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N)
    (t : ℝ) :
    Xdot (Xupd Xm i μ t) * dotRefl N μ =
      Xupd (Xdot Xm * dotRefl N μ) i μ ((Xdot Xm * dotRefl N μ) i μ + dotLen N * (t - Xm i μ)) := by
  rw [ec_Xupd_eq (Xdot Xm * dotRefl N μ), ec_Xupd_eq Xm]
  unfold Xdot
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, ec_single_piBar_refl hN,
    smul_smul]
  congr 2
  ring

/-! ## Invariance of `𝒳` and `G` under the reflection -/

private lemma ec_QN_mul (Sig : Matrix (Fin M) (Fin M) ℝ) (Y : Matrix (Fin M) (Fin N) ℝ)
    (O : Matrix (Fin N) (Fin N) ℝ) : QN Sig (Y * O) = Oᵀ * QN Sig Y * O := by
  unfold QN
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]

private lemma ec_QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Y : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Y).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Y hSig
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- `𝒳(Y R_μ) = 𝒳(Y)`: the smoothed count of `Q_N` is invariant under the orthogonal `R_μ`. -/
theorem dot_smCount_mul_refl {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (hN : 2 ≤ N) (Y : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (η E₁ E₂ : ℝ) :
    smCount (QN Sig (Y * dotRefl N μ)) η E₁ E₂ = smCount (QN Sig Y) η E₁ E₂ := by
  have hA := ec_QN_isHermitian hSig Y
  have hB := ec_QN_isHermitian hSig (Y * dotRefl N μ)
  have hc : (QN Sig (Y * dotRefl N μ)).charpoly = (QN Sig Y).charpoly := by
    rw [ec_QN_mul, dot_dotRefl_transpose, charpoly_mul_comm, ← Matrix.mul_assoc,
      dot_dotRefl_mul_self hN, Matrix.one_mul]
  have he : specOf (QN Sig (Y * dotRefl N μ)) = specOf (QN Sig Y) := by
    rw [specOf_eq hB, specOf_eq hA]
    exact (hB.eigenvalues_eq_eigenvalues_iff hA).2 hc
  unfold smCount
  rw [he]

/-- `𝒳(Ẋ(X^{t}_{(iμ)})) = 𝒳((Ẋ R_μ)^{s}_{(iμ)})`, `s = (Ẋ R_μ)_{iμ} + |π̄ e_μ| (t - X_{iμ})`. -/
theorem dot_smCount_Xupd {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (hN : 2 ≤ N) (Xm : Matrix (Fin M) (Fin N) ℝ) (η E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (t : ℝ) :
    smCount (QN Sig (Xdot (Xupd Xm i μ t))) η E₁ E₂ =
      smCount (QN Sig (Xupd (Xdot Xm * dotRefl N μ) i μ
        ((Xdot Xm * dotRefl N μ) i μ + dotLen N * (t - Xm i μ)))) η E₁ E₂ := by
  rw [← dot_Xdot_Xupd_mul hN, dot_smCount_mul_refl hSig hN]

/-- `d/dt g(a + b t) = b g'(a + b t)` at every order, for every `g`. -/
private lemma ec_iteratedDeriv_affine (g : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => g (a + b * t)) = fun t => b ^ n * iteratedDeriv n g (a + b * t) := by
  induction n with
  | zero => funext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext t
    rw [deriv_const_mul_field']
    beta_reduce
    have h1 : deriv (fun t => iteratedDeriv n g (a + b * t)) t =
        b * deriv (iteratedDeriv n g) (a + b * t) := by
      have e := deriv_comp_mul_left (f := fun s => iteratedDeriv n g (a + s)) (c := b) (x := t)
      rw [smul_eq_mul, deriv_comp_const_add] at e
      exact e
    rw [h1, pow_succ]
    ring

/-- The entry derivatives of `F(𝒳(Ẋ))`: `∂_{X_{iμ}}^n F(𝒳(Ẋ)) = |π̄ e_μ|^n` times the `n`-th
derivative of `F(𝒳)` in the entry `(i, μ)` of `Ẋ R_μ`, at
`(Ẋ R_μ)_{iμ} + |π̄ e_μ| (u - X_{iμ})`. -/
theorem dot_iteratedDeriv_smF {l : ℕ} (F : (Fin l → ℝ) → ℝ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.IsHermitian) (hN : 2 ≤ N) (Xm : Matrix (Fin M) (Fin N) ℝ) (η : ℝ)
    (Ea Eb : Fin l → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (fun t => smF F Sig (Xdot (Xupd Xm i μ t)) η Ea Eb) u =
      dotLen N ^ n * smT n F Sig (Xdot Xm * dotRefl N μ) η Ea Eb i μ
        ((Xdot Xm * dotRefl N μ) i μ + dotLen N * (u - Xm i μ)) := by
  set W := Xdot Xm * dotRefl N μ with hW
  have e : (fun t => smF F Sig (Xdot (Xupd Xm i μ t)) η Ea Eb) =
      fun t => smF F Sig (Xupd W i μ ((W i μ - dotLen N * Xm i μ) + dotLen N * t)) η Ea Eb := by
    funext t
    unfold smF
    congr 1
    funext j
    rw [dot_smCount_Xupd hSig hN, ← hW]
    congr 3
    ring
  have h := congrFun (ec_iteratedDeriv_affine (fun s => smF F Sig (Xupd W i μ s) η Ea Eb)
    (W i μ - dotLen N * Xm i μ) (dotLen N) n) u
  rw [e, h]
  unfold smT
  congr 2
  ring

/-- The smoothed count of `Q̇`'s companion `Q_N(Ẋ)` is smooth in an entry of `X`. -/
theorem dot_contDiff_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) (hN : 2 ≤ N)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) :
    ContDiff ℝ n (fun t => smCount (QN Sig (Xdot (Xupd Xm i μ t))) η E₁ E₂) := by
  set W := Xdot Xm * dotRefl N μ with hW
  have e : (fun t => smCount (QN Sig (Xdot (Xupd Xm i μ t))) η E₁ E₂) =
      (fun s => smCount (QN Sig (Xupd W i μ s)) η E₁ E₂) ∘
        fun t => (W i μ - dotLen N * Xm i μ) + dotLen N * t := by
    funext t
    simp only [Function.comp_apply]
    rw [dot_smCount_Xupd hSig.1 hN, ← hW]
    congr 3
    ring
  rw [e]
  exact (derivative_contDiff_smCount hSig W hη E₁ E₂ i μ n).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id))

/-- `diag(1, R_μ)` on `𝓘_M ⊔ 𝓘_N`. -/
private def ecP (M N : ℕ) (μ : Fin N) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  fromBlocks 1 0 0 (dotRefl N μ)

private lemma ec_P_transpose (μ : Fin N) : (ecP M N μ)ᵀ = ecP M N μ := by
  unfold ecP
  rw [fromBlocks_transpose, dot_dotRefl_transpose]
  simp

private lemma ec_cplx_P_mul_self (hN : 2 ≤ N) (μ : Fin N) :
    cplx (ecP M N μ) * cplx (ecP M N μ) = 1 := by
  rw [← Matrix.map_mul]
  unfold ecP
  rw [fromBlocks_multiply, dot_dotRefl_mul_self hN]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [fromBlocks_one, Matrix.map_one _ (map_zero _) (map_one _)]

private lemma ec_H_mul_refl {Sig : Matrix (Fin M) (Fin M) ℝ} (hN : 2 ≤ N)
    (Y : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (z : ℂ) :
    H Sig (Y * dotRefl N μ) z = cplx (ecP M N μ) * H Sig Y z * cplx (ecP M N μ) := by
  have hRR : cplx (dotRefl N μ) * cplx (dotRefl N μ) = 1 := by
    rw [← Matrix.map_mul, dot_dotRefl_mul_self hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPc : cplx (ecP M N μ) = fromBlocks 1 0 0 (cplx (dotRefl N μ)) := by
    simp [ecP, cplx, Matrix.fromBlocks_map]
  rw [hPc]
  unfold H linH
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · exact Matrix.map_mul
  · rw [transpose_mul, dot_dotRefl_transpose]
    exact Matrix.map_mul
  · rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR]

/-- `G(Y R_μ) = diag(1, R_μ) G(Y) diag(1, R_μ)`. -/
private lemma ec_G_mul_refl {Sig : Matrix (Fin M) (Fin M) ℝ} (hN : 2 ≤ N)
    (Y : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (z : ℂ) :
    G Sig (Y * dotRefl N μ) z = cplx (ecP M N μ) * G Sig Y z * cplx (ecP M N μ) := by
  have hP := ec_cplx_P_mul_self (M := M) hN μ
  have hinv : (cplx (ecP M N μ))⁻¹ = cplx (ecP M N μ) := Matrix.inv_eq_left_inv hP
  rw [G_def, G_def, ec_H_mul_refl hN, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinv,
    Matrix.mul_assoc]

/-- `⟨R x, L R y⟩ = ⟨x, Rᵀ L R y⟩` for a real matrix `R`. -/
private lemma ec_testBilin_mulVec {ι : Type*} [Fintype ι] (R : Matrix ι ι ℝ) (L : Matrix ι ι ℂ)
    (x y : ι → ℝ) :
    testBilin (R *ᵥ x) L (R *ᵥ y) =
      testBilin x ((R.map (algebraMap ℝ ℂ))ᵀ * L * R.map (algebraMap ℝ ℂ)) y := by
  have hc : ∀ v : ι → ℝ, (fun s => ((R *ᵥ v) s : ℂ)) =
      R.map (algebraMap ℝ ℂ) *ᵥ fun s => (v s : ℂ) := by
    intro v
    ext s
    simp [mulVec, dotProduct, Complex.ofReal_sum]
  unfold testBilin
  rw [hc x, hc y, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (R.map (algebraMap ℝ ℂ))ᵀ, vecMul_transpose]

private lemma ec_testBilin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (s t : ι) : testBilin (Pi.single s 1) A (Pi.single t 1) = A s t := by
  unfold testBilin
  have h1 : (fun u => (((Pi.single t (1 : ℝ) : ι → ℝ) u : ℝ) : ℂ)) = Pi.single t 1 := by
    ext u; by_cases h : u = t <;> simp [h]
  have h2 : (fun u => (((Pi.single s (1 : ℝ) : ι → ℝ) u : ℝ) : ℂ)) = Pi.single s 1 := by
    ext u; by_cases h : u = s <;> simp [h]
  rw [h1, h2, mulVec_single_one, single_one_dotProduct]
  simp

private lemma ec_testBilin_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) (A B : Matrix ι ι ℂ) :
    testBilin x (A - B) y = testBilin x A y - testBilin x B y := by
  unfold testBilin
  rw [sub_mulVec, dotProduct_sub]

/-- The test vectors `e_i` and `(0, v̂_μ)` of the frame `R_μ`. -/
private def ecU (M N : ℕ) (μ : Fin N) (a : Fin M ⊕ Fin N) : Fin M ⊕ Fin N → ℝ :=
  ecP M N μ *ᵥ Pi.single a 1

private lemma ec_U_inl (μ : Fin N) (i : Fin M) :
    ecU M N μ (Sum.inl i) = Pi.single (Sum.inl i) 1 := by
  unfold ecU ecP
  ext s
  rw [mulVec_single_one]
  rcases s with j | ν
  · by_cases h : j = i
    · subst h; simp
    · simp [h]
  · simp

private lemma ec_U_inr (hN : 2 ≤ N) (μ : Fin N) :
    ecU M N μ (Sum.inr μ) = Sum.elim (0 : Fin M → ℝ) (dotVec N μ) := by
  unfold ecU ecP
  ext s
  rw [mulVec_single_one]
  rcases s with j | ν
  · simp
  · simp [ec_refl_col hN]

/-- `G(Y R_μ)_{ab} = ⟨u_a, G(Y) u_b⟩`, `u = diag(1, R_μ) e`. -/
private lemma ec_G_refl_apply {Sig : Matrix (Fin M) (Fin M) ℝ} (hN : 2 ≤ N)
    (Y : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (z : ℂ) (a b : Fin M ⊕ Fin N) :
    G Sig (Y * dotRefl N μ) z a b = testBilin (ecU M N μ a) (G Sig Y z) (ecU M N μ b) := by
  unfold ecU
  rw [ec_testBilin_mulVec, ← Matrix.transpose_map, ec_P_transpose, ec_testBilin_single,
    ec_G_mul_refl hN]

private lemma ec_testBilin_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (s : Fin N → ℝ)
    (i : Fin M) :
    testBilin (Sum.elim (0 : Fin M → ℝ) s) A (Pi.single (Sum.inl i) 1) =
      ∑ μ, (s μ : ℂ) * A (Sum.inr μ) (Sum.inl i) := by
  unfold testBilin
  have h1 : (fun u => (((Pi.single (Sum.inl i) (1 : ℝ) : Fin M ⊕ Fin N → ℝ) u : ℝ) : ℂ)) =
      Pi.single (Sum.inl i) 1 := by
    ext u; by_cases h : u = Sum.inl i <;> simp [h]
  rw [h1, mulVec_single_one]
  simp [dotProduct, Fintype.sum_sum_type]

/-- `G(Ẋ R_μ)_{μ i} = ⟨v̂_μ, Ġ e_i⟩`. -/
theorem dot_G_refl_inr_inl {Sig : Matrix (Fin M) (Fin M) ℝ} (hN : 2 ≤ N)
    (Y : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (z : ℂ) (i : Fin M) :
    G Sig (Y * dotRefl N μ) z (Sum.inr μ) (Sum.inl i) =
      ∑ ν, (dotVec N μ ν : ℂ) * G Sig Y z (Sum.inr ν) (Sum.inl i) := by
  rw [ec_G_refl_apply hN, ec_U_inr hN, ec_U_inl, ec_testBilin_embN]

/-! ## Entry bounds for `G(Ẋ R_μ)` at the counting points -/

/-- The real matrix `Σ̲ = diag(Σ, 1)` of (def_ul_Sigma). -/
private def ecR (Sig : Matrix (Fin M) (Fin M) ℝ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  fromBlocks Sig 0 0 1

private lemma ec_ulSigma_eq (Sig : Matrix (Fin M) (Fin M) ℝ) :
    ulSigma N Sig = (ecR (N := N) Sig).map (algebraMap ℝ ℂ) := by
  unfold ulSigma ecR
  rw [Matrix.fromBlocks_map]
  simp

/-- `⟨Σ̲ x, Σ̲⁻¹ B Σ̲⁻¹ Σ̲ y⟩ = ⟨x, B y⟩`. -/
private lemma ec_testBilin_conj {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (x y : Fin M ⊕ Fin N → ℝ) :
    testBilin (ecR Sig *ᵥ x) ((ulSigma N Sig)⁻¹ * B * (ulSigma N Sig)⁻¹) (ecR Sig *ᵥ y) =
      testBilin x B y := by
  rw [ec_testBilin_mulVec, ← ec_ulSigma_eq]
  have hT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  set V : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ := fromBlocks (cplx Sig⁻¹) 0 0 1 with hV
  have h1 : ulSigma N Sig * V = 1 := by
    rw [ulSigma, hV, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [show Sig.map (algebraMap ℝ ℂ) * cplx Sig⁻¹ = 1 by
      rw [cplx, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)]]
    exact fromBlocks_one
  have h2 : V * ulSigma N Sig = 1 := by
    rw [ulSigma, hV, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [show cplx Sig⁻¹ * Sig.map (algebraMap ℝ ℂ) = 1 by
      rw [cplx, ← Matrix.map_mul, hS', Matrix.map_one _ (map_zero _) (map_one _)]]
    exact fromBlocks_one
  have hinv : (ulSigma N Sig)⁻¹ = V := Matrix.inv_eq_right_inv h1
  have htr : (ulSigma N Sig)ᵀ = ulSigma N Sig := by
    rw [ulSigma, fromBlocks_transpose]
    simp [← Matrix.transpose_map, hT]
  rw [htr, hinv]
  congr 1
  calc ulSigma N Sig * (V * B * V) * ulSigma N Sig
      = (ulSigma N Sig * V) * B * (V * ulSigma N Sig) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

private lemma ec_testBilin_lawMatDot {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (x y : Fin M ⊕ Fin N → ℝ) :
    testBilin (ecR Sig *ᵥ x) (lawMatDot Sig Xm z) (ecR Sig *ᵥ y) =
      testBilin x (G Sig (Xdot Xm) z - piMatDot Sig (mFun N (specOf Sig) z) z) y := by
  unfold lawMatDot
  exact ec_testBilin_conj hSig _ x y

private lemma ec_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ∃ U : Matrix (Fin M) (Fin M) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      Sig = U * diagonal (specOf Sig) * Uᵀ ∧ ∀ i, 0 < specOf Sig i := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hSig.1
  have h₁ : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h₂ : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  refine ⟨U, h₂, h₁, ?_, fun i => ?_⟩
  · rw [← hD]
    simp only [← Matrix.mul_assoc]
    rw [h₂, Matrix.one_mul, Matrix.mul_assoc, h₂, Matrix.mul_one]
  · rw [specOf_eq hSig.1]
    exact hSig.eigenvalues_pos i

private lemma ec_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (i : Fin K) : ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `∑_j Σ_{ji}² ≤ τ⁻²` when every eigenvalue of `Σ > 0` is at most `τ⁻¹`. -/
private lemma ec_col_sq_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hle : ∀ k, specOf Sig k ≤ τ⁻¹) (i : Fin M) :
    ∑ j, Sig j i ^ 2 ≤ τ⁻¹ ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := ec_diag hSig
  have hT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hSS : Sig * Sig = U * diagonal (fun k => specOf Sig k ^ 2) * Uᵀ := by
    conv_lhs => rw [hSd]
    calc U * diagonal (specOf Sig) * Uᵀ * (U * diagonal (specOf Sig) * Uᵀ)
        = U * (diagonal (specOf Sig) * (Uᵀ * U) * diagonal (specOf Sig)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h₁, Matrix.mul_one, diagonal_mul_diagonal]
          congr 3
          funext k
          ring
  have e1 : ∑ j, Sig j i ^ 2 = (Sig * Sig) i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Sig i j = Sig j i := by
      have := congrFun (congrFun hT j) i
      simpa [Matrix.transpose_apply] using this
    rw [this, sq]
  have e2 : (Sig * Sig) i i = ∑ k, U i k ^ 2 * specOf Sig k ^ 2 := by
    rw [hSS]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2]
  calc ∑ k, U i k ^ 2 * specOf Sig k ^ 2 ≤ ∑ k, U i k ^ 2 * τ⁻¹ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (hσ k).le (hle k) 2
    _ = τ⁻¹ ^ 2 := by rw [← Finset.sum_mul, ec_row_sq h₂, one_mul]

/-- `|Σ̲ e_s| ≤ τ⁻¹` for `τ ≤ 1`. -/
private lemma ec_testNorm_col_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hle : ∀ k, specOf Sig k ≤ τ⁻¹) (s : Fin M ⊕ Fin N) :
    testNorm (ecR Sig *ᵥ Pi.single s 1) ≤ τ⁻¹ := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  rw [mulVec_single_one]
  unfold testNorm
  rw [Real.sqrt_le_left (by positivity)]
  rcases s with i | μ
  · have e : ∑ t, (ecR (N := N) Sig).col (Sum.inl i) t ^ 2 = ∑ j, Sig j i ^ 2 := by
      simp [ecR, Fintype.sum_sum_type, Matrix.col_apply]
    rw [e]
    exact ec_col_sq_le hSig hle i
  · have e : ∑ t, (ecR (N := N) Sig).col (Sum.inr μ) t ^ 2 = 1 := by
      simp [ecR, Fintype.sum_sum_type, Matrix.col_apply, Matrix.one_apply]
    rw [e]
    exact one_le_pow₀ hτi

/-- `Σ̲ (0, s) = (0, s)` and `|(0, s)| = |s|`. -/
private lemma ec_ecR_embN (Sig : Matrix (Fin M) (Fin M) ℝ) (s : Fin N → ℝ) :
    ecR Sig *ᵥ Sum.elim (0 : Fin M → ℝ) s = Sum.elim (0 : Fin M → ℝ) s ∧
      testNorm (Sum.elim (0 : Fin M → ℝ) s) = testNorm s := by
  constructor
  · ext t
    rcases t with j | μ <;> simp [ecR, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [testNorm, Fintype.sum_sum_type]

private lemma ec_testNorm_dotVec (hN : 2 ≤ N) (μ : Fin N) : testNorm (dotVec N μ) = 1 := by
  unfold testNorm
  rw [ec_sum_dotVec_sq hN, Real.sqrt_one]

/-! ### `Π̇` in the frame `R_μ` -/

private lemma ec_testBilin_embN_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (x y : Fin N → ℝ) :
    testBilin (Sum.elim (0 : Fin M → ℝ) x) A (Sum.elim (0 : Fin M → ℝ) y) =
      ∑ ν, (x ν : ℂ) * ∑ ν', A (Sum.inr ν) (Sum.inr ν') * (y ν' : ℂ) := by
  unfold testBilin
  simp [dotProduct, mulVec, Fintype.sum_sum_type]

private lemma ec_testBilin_single_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (y : Fin N → ℝ) :
    testBilin (Pi.single (Sum.inl i) 1) A (Sum.elim (0 : Fin M → ℝ) y) =
      ∑ ν, A (Sum.inl i) (Sum.inr ν) * (y ν : ℂ) := by
  unfold testBilin
  have h1 : (fun u => (((Pi.single (Sum.inl i) (1 : ℝ) : Fin M ⊕ Fin N → ℝ) u : ℝ) : ℂ)) =
      Pi.single (Sum.inl i) 1 := by
    ext u; by_cases h : u = Sum.inl i <;> simp [h]
  rw [h1, single_one_dotProduct]
  simp [mulVec, dotProduct, Fintype.sum_sum_type]

private lemma ec_piMatDot_inr {Sig : Matrix (Fin M) (Fin M) ℝ} (w z : ℂ) (ν ν' : Fin N) :
    piMatDot (N := N) Sig w z (Sum.inr ν) (Sum.inr ν') =
      w * (if ν = ν' then 1 else 0) - (w + z⁻¹) * ((if ν = ν' then 1 else 0) -
        (piBar N ν ν' : ℂ)) := by
  by_cases h : ν = ν' <;> simp [piMatDot, piMat, h]

/-- On `J = {i, μ}`, `⟨u_a, Π̇ u_b⟩ = Π_{ab}`: `Π̇ = Π` on `𝓘_M`, the mixed blocks vanish, and
`Π̇ = m` on `1^⊥ ∋ v̂_μ` (§11.2). -/
private lemma ec_testBilin_piMatDot {Sig : Matrix (Fin M) (Fin M) ℝ} (hN : 2 ≤ N) (w z : ℂ)
    (i : Fin M) (μ : Fin N)
    (a : Fin M ⊕ Fin N) (ha : a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)))
    (b : Fin M ⊕ Fin N) (hb : b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N))) :
    testBilin (ecU M N μ a) (piMatDot Sig w z) (ecU M N μ b) = piMat (N := N) Sig w a b := by
  have hma : a = Sum.inl i ∨ a = Sum.inr μ := by simpa using ha
  have hmb : b = Sum.inl i ∨ b = Sum.inr μ := by simpa using hb
  rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl
  · rw [ec_U_inl, ec_testBilin_single]
    simp [piMatDot, piMat]
  · rw [ec_U_inl, ec_U_inr hN, ec_testBilin_single_embN]
    simp [piMatDot, piMat]
  · rw [ec_U_inl, ec_U_inr hN, ec_testBilin_embN]
    simp [piMatDot, piMat]
  · rw [ec_U_inr hN, ec_testBilin_embN_embN]
    have hin : ∀ ν, ∑ ν', piMatDot (N := N) Sig w z (Sum.inr ν) (Sum.inr ν') *
        (dotVec N μ ν' : ℂ) = w * (dotVec N μ ν : ℂ) := by
      intro ν
      have hp := ec_piBar_dotVec hN ν μ
      have hp' : ∑ ν', (piBar N ν ν' : ℂ) * (dotVec N μ ν' : ℂ) = (dotVec N μ ν : ℂ) := by
        rw [← hp]; push_cast; rfl
      simp only [ec_piMatDot_inr, sub_mul, mul_sub, ite_mul, zero_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      have h3 : ∑ x, (w + z⁻¹) * (piBar N ν x : ℂ) * (dotVec N μ x : ℂ) =
          (w + z⁻¹) * (dotVec N μ ν : ℂ) := by
        rw [← hp', Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [h3]
      ring
    simp only [hin]
    have h1 : ∑ ν, (dotVec N μ ν : ℂ) * (w * (dotVec N μ ν : ℂ)) =
        w * ((∑ ν, dotVec N μ ν ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      ring
    rw [h1, ec_sum_dotVec_sq hN]
    simp [piMat]

/-! ### The deterministic matrix `Π` at the counting points -/

/-- `(Σ (1 + wΣ)⁻¹)_{jl} = ∑ₖ U_{jk} σₖ (1 + σₖ w)⁻¹ U_{lk}` for `Σ = U diag(σ) Uᵀ`. -/
private lemma ec_SigInv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (j l : Fin M) :
    (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
      ∑ k, (U j k : ℂ) * ((σ k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹) * (U l k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
    have e2 : diagonal (fun i => 1 + (σ i : ℂ) * w) =
        1 + w • diagonal (fun i => (σ i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_smul, diagonal_add]
      congr 1
      funext i
      simp [mul_comm]
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, c₂, Matrix.mul_smul,
      Matrix.smul_mul, e1]
  have hinv : (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hT]
    have hd : diagonal (fun i => 1 + (σ i : ℂ) * w) *
        diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hw i)
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => 1 + (σ i : ℂ) * w) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [c₁, Matrix.mul_one, hd, Matrix.mul_one, c₂]
  have hprod : cplx Sig * (1 + w • cplx Sig)⁻¹ = (cplx Uᵀ)ᵀ *
      diagonal (fun i => (σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    rw [hinv, e1]
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [c₁, Matrix.mul_one, diagonal_mul_diagonal]
  rw [hprod]
  simp only [Matrix.mul_apply, cplx, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.map_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.coe_algebraMap]

/-- `|Π_{st}| ≤ A c⁻¹ + C_m` when `0 ≤ σ_k ≤ A`, `|1 + σ_k w| ≥ c` and `|w| ≤ C_m`. -/
private lemma ec_piMat_le {A c Cm : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hA : 0 ≤ A) (hle : ∀ k, specOf Sig k ≤ A) (hc : 0 < c) (hCm : 0 ≤ Cm) {w : ℂ}
    (hOne : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) (hw : ‖w‖ ≤ Cm) (s t : Fin M ⊕ Fin N) :
    ‖piMat (N := N) Sig w s t‖ ≤ A * c⁻¹ + Cm := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := ec_diag hSig
  have hw0 : ∀ i, 1 + (specOf Sig i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  set d : Fin M → ℂ := fun k => (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ with hd
  have hdle : ∀ k, ‖d k‖ ≤ A * c⁻¹ := fun k => by
    simp only [hd]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ k).le]
    exact mul_le_mul (hle k) (inv_anti₀ hc (hOne k)) (inv_nonneg.2 (norm_nonneg _)) hA
  have hD0 : 0 ≤ A * c⁻¹ := mul_nonneg hA (inv_nonneg.2 hc.le)
  have he := ec_SigInv_entry h₂ h₁ hSd hw0
  rcases s with j | ν <;> rcases t with l | ν'
  · simp only [piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
    rw [he]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |U j k|) (fun k => |U l k|)
    simp only [sq_abs] at hcs
    rw [ec_row_sq h₂, ec_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    calc ‖∑ k, (U j k : ℂ) * d k * (U l k : ℂ)‖ ≤ ∑ k, A * c⁻¹ * (|U j k| * |U l k|) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hdle k) (abs_nonneg (U j k))
          calc |U j k| * ‖d k‖ * |U l k| ≤ |U j k| * (A * c⁻¹) * |U l k| :=
                mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ = A * c⁻¹ * (|U j k| * |U l k|) := by ring
      _ = A * c⁻¹ * ∑ k, |U j k| * |U l k| := by rw [Finset.mul_sum]
      _ ≤ A * c⁻¹ * 1 := mul_le_mul_of_nonneg_left hcs hD0
      _ ≤ A * c⁻¹ + Cm := by linarith
  · have h0 : 0 ≤ A * c⁻¹ + Cm := by positivity
    simpa [piMat] using h0
  · have h0 : 0 ≤ A * c⁻¹ + Cm := by positivity
    simpa [piMat] using h0
  · simp only [piMat, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    split_ifs
    · linarith
    · simp only [norm_zero]; positivity

/-- `|w₂ Π_{ii}(w₂) - w₁ Π_{ii}(w₁)| ≤ A c⁻² |w₂ - w₁|` when `0 ≤ σ_k ≤ A` and
`|1 + σ_k w_j| ≥ c`, from `w Π_{ii}(w) = -∑_k U_{ik}² w σ_k (1 + σ_k w)⁻¹` in an eigenbasis `U`
of `Σ`. -/
private lemma ec_mPi_sub {A c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hA : 0 ≤ A) (hle : ∀ k, specOf Sig k ≤ A) (hc : 0 < c) {w₁ w₂ : ℂ}
    (hOne₁ : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w₁‖)
    (hOne₂ : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w₂‖) (i : Fin M) :
    ‖w₂ * piMat (N := N) Sig w₂ (Sum.inl i) (Sum.inl i) -
        w₁ * piMat (N := N) Sig w₁ (Sum.inl i) (Sum.inl i)‖ ≤ A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := ec_diag hSig
  have hne : ∀ (w : ℂ), (∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) →
      ∀ k, 1 + (specOf Sig k : ℂ) * w ≠ 0 := fun w hw k h0 => by
    have := hw k
    rw [h0, norm_zero] at this
    linarith
  have hP : ∀ (w : ℂ), (∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) →
      w * piMat (N := N) Sig w (Sum.inl i) (Sum.inl i) =
        -∑ k, ((U i k ^ 2 : ℝ) : ℂ) * (w * ((specOf Sig k : ℂ) *
          (1 + (specOf Sig k : ℂ) * w)⁻¹)) := by
    intro w hw
    simp only [piMat, fromBlocks_apply₁₁, Matrix.neg_apply]
    rw [ec_SigInv_entry h₂ h₁ hSd (hne w hw), mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hP w₂ hOne₂, hP w₁ hOne₁, neg_sub_neg, ← Finset.sum_sub_distrib]
  have hk : ∀ k, ‖((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹))‖ ≤ U i k ^ 2 * (A * c⁻¹ ^ 2 * ‖w₂ - w₁‖) := by
    intro k
    have h1 := hne w₁ hOne₁ k
    have h2 := hne w₂ hOne₂ k
    have e : ((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹)) = ((U i k ^ 2 : ℝ) : ℂ) * ((specOf Sig k : ℂ) *
        (w₁ - w₂) * ((1 + (specOf Sig k : ℂ) * w₁)⁻¹ * (1 + (specOf Sig k : ℂ) * w₂)⁻¹)) := by
      have ha := mul_inv_cancel₀ h1
      have hb := mul_inv_cancel₀ h2
      linear_combination
        (-(((U i k ^ 2 : ℝ) : ℂ) * (specOf Sig k : ℂ) * w₁ *
          (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) * hb +
        (((U i k ^ 2 : ℝ) : ℂ) * (specOf Sig k : ℂ) * w₂ *
          (1 + (specOf Sig k : ℂ) * w₂)⁻¹) * ha
    rw [e, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hσ k).le, norm_sub_rev w₁ w₂]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have i1 : ‖1 + (specOf Sig k : ℂ) * w₁‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne₁ k)
    have i2 : ‖1 + (specOf Sig k : ℂ) * w₂‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne₂ k)
    have i0 : 0 ≤ ‖w₂ - w₁‖ := norm_nonneg _
    calc specOf Sig k * ‖w₂ - w₁‖ * (‖1 + (specOf Sig k : ℂ) * w₁‖⁻¹ *
          ‖1 + (specOf Sig k : ℂ) * w₂‖⁻¹)
        ≤ A * ‖w₂ - w₁‖ * (c⁻¹ * c⁻¹) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hle k) i0)
            (mul_le_mul i1 i2 (inv_nonneg.2 (norm_nonneg _)) (inv_nonneg.2 hc.le))
            (by positivity) (mul_nonneg hA i0)
      _ = A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by ring
  calc ‖∑ k, (((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹)))‖
      ≤ ∑ k, U i k ^ 2 * (A * c⁻¹ ^ 2 * ‖w₂ - w₁‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hk k)
    _ = A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by rw [← Finset.sum_mul, ec_row_sq h₂, one_mul]

/-! ### The counting points and the law for `Ġ` -/

/-- `N^y ≤ c` eventually, for `y < 0` and `c > 0`. -/
private lemma ec_ev_small {y c : ℝ} (hy : y < 0) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ y ≤ c := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.2 hy)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    refine h.congr fun N => ?_
    simp
  exact (h'.eventually (ge_mem_nhds hc))

/-- The law parameter `τ₂ = min(τ/2, 1/6, (2τ⁻¹(1+τ⁻¹)+1)⁻¹)`. -/
private def ecTau (τ : ℝ) : ℝ := min (τ / 2) (min (1 / 6) ((2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹))

/-- The window parameter `τ'' = min(τ'(τ₂), τ₂/2)`. -/
private def ecTau'' (τ : ℝ) : ℝ := min (edgeTau' (ecTau τ)) (ecTau τ / 2)

private lemma ec_tau_facts {τ : ℝ} (hτ : 0 < τ) :
    0 < ecTau τ ∧ ecTau τ ≤ τ / 2 ∧ ecTau τ ≤ 1 / 6 ∧
      2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ (ecTau τ)⁻¹ ∧
      0 < ecTau'' τ ∧ ecTau'' τ ≤ edgeTau' (ecTau τ) ∧ ecTau'' τ ≤ ecTau τ / 2 := by
  have hA : 0 < 2 * τ⁻¹ * (1 + τ⁻¹) + 1 := by positivity
  have h0 : 0 < ecTau τ := lt_min (half_pos hτ) (lt_min (by norm_num) (inv_pos.2 hA))
  have h3 : ecTau τ ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨h0, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_,
    lt_min (edgeTau'_pos h0) (half_pos h0), min_le_left _ _, min_le_right _ _⟩
  rw [le_inv_comm₀ hA h0]
  exact h3

private lemma ec_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ τ ≤ 1 ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))
  refine ⟨hN, hτ1, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
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

/-- `A ≤ N^y` eventually, for `y > 0`. -/
private lemma ec_ev_large {y : ℝ} (hy : 0 < y) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ (N : ℝ) ^ y :=
  ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A

/-- A counting point `z = E + iη`, `N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}`, `|E - a_k| ≤ 3N^{-2/3+ε}`,
lies in `𝐃^e_k(τ₂, τ'', N)`, `Ψ(z) ≤ 4N^{-1/3+9ε}`, and `|z - a_k| ≤ 4N^{-2/3+ε} ≤ τ'₀`. -/
private lemma ec_window {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (σ : Fin M → ℝ) (k : ℕ), DensityAssumptions τ N σ →
      RegularEdge τ N σ k → ∀ E : ℝ, |E - edgeVal N σ k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      ((E : ℂ) + η * Complex.I) ∈ edgeDomain (ecTau τ) (ecTau'' τ) N σ k ∧
      Psi N σ ((E : ℂ) + η * Complex.I) ≤ 4 * (N : ℝ) ^ (-1 / 3 + 9 * ε) ∧
      ‖(E : ℂ) + η * Complex.I - edgeVal N σ k‖ ≤ 4 * (N : ℝ) ^ (-2 / 3 + ε) ∧
      4 * (N : ℝ) ^ (-2 / 3 + ε) ≤ edgeTau0 τ := by
  obtain ⟨hτ₂, hτ₂a, hτ₂b, hτ₂c, hτ'', hτ''a, hτ''b⟩ := ec_tau_facts hτ
  set τ₂ := ecTau τ with hτ₂def
  set τ'' := ecTau'' τ with hτ''def
  set S := sqUpper τ₂ with hSdef
  have ht0 : 0 < edgeTau0 τ := by
    have := edgeTau'_pos hτ
    unfold edgeTau' at this
    linarith
  filter_upwards [eventually_ge_atTop 1,
    ec_ev_small (y := -2 / 3 + ε) (by linarith) (by positivity : 0 < τ'' / 3),
    ec_ev_large (y := 17 * ε) (by positivity) (4 * S ^ 2),
    ec_ev_small (y := -2 / 3 + ε) (by linarith) (by positivity : 0 < edgeTau0 τ / 4),
    ec_ev_large (y := 1 / 6 - 9 * ε) (by linarith) 2]
    with N hN1 hN2 hN3 hN4 hN5
  intro M σ k h hk E hE η hη₁ hη₂
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  set n : ℝ := (N : ℝ) with hndef
  set c : ℝ := n ^ (-2 / 3 + ε) with hcdef
  set η₀ : ℝ := etaE N ε with hη₀def
  have hη₀e : η₀ = n ^ (-2 / 3 - 9 * ε) := rfl
  have hη₀pos : 0 < η₀ := by rw [hη₀e]; exact Real.rpow_pos_of_pos hn _
  have hηpos : 0 < η := by linarith
  have hηc : η ≤ c := hη₂.trans (by
    rw [hη₀e]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hη1 : η ≤ 1 := hη₂.trans (by
    rw [hη₀e]; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  have hc0 : 0 < c := Real.rpow_pos_of_pos hn _
  obtain ⟨hN0, hτ1, hS⟩ := ec_facts h
  have ha := edgeVal_mem_Icc N σ h.nonneg hN0 hS hτ h.phi_lower h.phi_upper h.bound_Sigma
    hk.1 hk.2.1
  have haτ : τ ≤ edgeVal N σ k := hk.2.2.1
  set a := edgeVal N σ k with hadef
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hre : ((E : ℂ) + η * Complex.I).re = E := by simp
  have him : ((E : ℂ) + η * Complex.I).im = η := by simp
  set z : ℂ := (E : ℂ) + η * Complex.I with hzdef
  have hτinv : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
  have hEpos : 0 ≤ E := by linarith [ha.1]
  have hlow : n ^ (-1 + τ₂) ≤ η := by
    have e1 : n ^ (-1 + τ₂) ≤ n ^ (-5 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have e2 : n ^ (-5 / 6 : ℝ) * n ^ (1 / 6 - 9 * ε) = η₀ := by
      rw [hη₀e, ← Real.rpow_add hn]; congr 1; ring
    have e3 : n ^ (-5 / 6 : ℝ) * 2 ≤ η₀ := by
      rw [← e2]; exact mul_le_mul_of_nonneg_left hN5 (by positivity)
    linarith
  have hdom : z ∈ edgeDomain τ₂ τ'' N σ k := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [him]; exact hηpos
    · refine le_trans ?_ (Complex.abs_re_le_norm z)
      rw [hre, abs_of_nonneg hEpos]
      linarith
    · rw [hre, abs_of_nonneg hEpos]
      linarith [ha.2]
    · rw [him]; exact hlow
    · rw [him]; linarith
    · rw [hre]; linarith
    · rw [hre]; linarith
  have h2 : DensityAssumptions τ₂ N σ := h.mono hτ₂ (by linarith)
  have hk2 : RegularEdge τ₂ N σ k := regularEdge_mono hk (by linarith)
  have hκ := kappa_edgeDomain h2 hk2 hτ''b hdom
  have hsq := m_sq_root_edge h2 hk2 hτ''a hdom
  rw [hκ, hre, him] at hsq
  have hκη0 : 0 < |E - a| + η := by positivity
  have hsq0 : 0 < √(|E - a| + η) := Real.sqrt_pos.2 hκη0
  have hS0 : 0 ≤ S := by
    rw [hSdef, sqUpper]
    exact le_trans (div_nonneg (mBoundConst_pos hτ₂).le (Real.sqrt_nonneg _))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hmim : (mFun N σ z).im ≤ S * √(|E - a| + η) := by
    by_cases hsup : z.re ∈ (varrho N σ).support
    · rw [hre] at hsup
      exact (hsq.1 hsup).2
    · rw [hre] at hsup
      refine (hsq.2 hsup).2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hS0
      rw [div_le_iff₀ hsq0, Real.mul_self_sqrt hκη0.le]
      linarith [abs_nonneg (E - a)]
  have hκη : |E - a| + η ≤ 4 * c := by linarith
  have hm2 : (mFun N σ z).im ≤ S * √(4 * c) :=
    hmim.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hκη) hS0)
  set b : ℝ := -1 / 3 + 9 * ε with hbdef
  have hb0 : 0 < n ^ b := Real.rpow_pos_of_pos hn _
  have hbb : n ^ b * n ^ b = n ^ (-2 / 3 + 18 * ε) := by
    rw [← Real.rpow_add hn]; congr 1; rw [hbdef]; ring
  have hc17 : c * n ^ (17 * ε) = n ^ (-2 / 3 + 18 * ε) := by
    rw [hcdef, ← Real.rpow_add hn]; congr 1; ring
  have hmb : (mFun N σ z).im ≤ n ^ b := by
    refine hm2.trans ?_
    have hl : 0 ≤ S * √(4 * c) := by positivity
    rw [← sq_le_sq₀ hl hb0.le, mul_pow, Real.sq_sqrt (by positivity), sq (n ^ b), hbb, ← hc17]
    calc S ^ 2 * (4 * c) = c * (4 * S ^ 2) := by ring
      _ ≤ c * n ^ (17 * ε) := mul_le_mul_of_nonneg_left hN3 hc0.le
  have hb1 : n ^ b * (n * η₀) = 1 := by
    have e := Real.rpow_add hn b (1 + (-2 / 3 - 9 * ε))
    rw [Real.rpow_add hn 1, Real.rpow_one, ← hη₀e] at e
    rw [← e, hbdef]
    have : -1 / 3 + 9 * ε + (1 + (-2 / 3 - 9 * ε)) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hNη0 : 0 < n * η := by positivity
  have hNη : n * η₀ ≤ 2 * (n * η) := by
    have := mul_le_mul_of_nonneg_left (show η₀ ≤ 2 * η by linarith) hn.le
    linarith
  have hhalf : 1 ≤ 2 * (n ^ b * (n * η)) := by
    have := mul_le_mul_of_nonneg_left hNη hb0.le
    linarith
  have hinv : 1 / (n * η) ≤ 2 * n ^ b := by
    rw [div_le_iff₀ hNη0]
    linarith
  have hsqrt : √((mFun N σ z).im / (n * η)) ≤ 2 * n ^ b := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hNη0]
    have e : (2 * n ^ b) ^ 2 * (n * η) = 2 * n ^ b * (2 * (n ^ b * (n * η))) := by ring
    have : n ^ b ≤ (2 * n ^ b) ^ 2 * (n * η) := by
      rw [e]
      have := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * n ^ b by positivity)
      linarith
    linarith
  refine ⟨hdom, ?_, ?_, ?_⟩
  · unfold Psi
    rw [him]
    linarith
  · have e : z - (a : ℂ) = ((E - a : ℝ) : ℂ) + η * Complex.I := by
      rw [hzdef]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    linarith
  · linarith

/-- The constant of (1+xm) on `𝐃^e_k(τ₂, τ'', N)`. -/
private def ecC (τ : ℝ) : ℝ := oneXmConst (edgeMz (ecTau τ)) (mBoundConst (ecTau τ))

private lemma ec_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < ecC τ := by
  obtain ⟨hτ₂, -⟩ := ec_tau_facts hτ
  have hC : 0 < mBoundConst (ecTau τ) := mBoundConst_pos hτ₂
  have hmz : 0 < edgeMz (ecTau τ) := lt_min (half_pos hτ₂) (div_pos (edgeTau'_pos hτ₂) hC)
  exact lt_min (by norm_num) (div_pos hmz (by linarith))

/-- At a counting point: (1+xm) with constant `c(τ)` and `|m| ≤ C_m(τ₂)`. -/
private lemma ec_window_m {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (σ : Fin M → ℝ) (k : ℕ), DensityAssumptions τ N σ →
      RegularEdge τ N σ k → ∀ E : ℝ, |E - edgeVal N σ k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      (∀ i, ecC τ ≤ ‖1 + (σ i : ℂ) * mFun N σ ((E : ℂ) + η * Complex.I)‖) ∧
      ‖mFun N σ ((E : ℂ) + η * Complex.I)‖ ≤ mBoundConst (ecTau τ) := by
  obtain ⟨hτ₂, hτ₂a, -, -, -, hτ''a, -⟩ := ec_tau_facts hτ
  filter_upwards [ec_window hτ hε hε1] with N hN
  intro M σ k h hk E hE η hη₁ hη₂
  have hdom := (hN M σ k h hk E hE η hη₁ hη₂).1
  have h2 : DensityAssumptions (ecTau τ) N σ := h.mono hτ₂ (by linarith)
  have hk2 : RegularEdge (ecTau τ) N σ k := regularEdge_mono hk (by linarith)
  exact ⟨one_add_mul_mFun_edge h2 hk2 hτ''a hdom, (gen_prop_m_specDomain h2 hdom.1).2.1⟩

/-- Deterministic bounds at the counting points `z = E + iη` of a regular edge `k`, with
`N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}` and `|E - a_k| ≤ 3N^{-2/3+ε}`: `Ψ(z) ≤ 4N^{-1/3+9ε}`,
`|m(z)| ≤ K` and `|Π_{st}(z)| ≤ K` for all `s, t ∈ 𝓘_M ⊔ 𝓘_N`, where `K` depends only on `τ`
(Theorem 3.14 (i) setting, (m_sq_root) and (1+xm)); the range of `η` contains the smoothing scale
`N^{-1} (N-1)^{1/3-9ε}` of `Q̇` in the normalization of `Q_N(Ẋ)`. -/
theorem dot_det (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
      Sig.PosDef → DensityAssumptions τ N (specOf Sig) → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
        Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) ≤ 4 * (N : ℝ) ^ (-1 / 3 + 9 * ε) ∧
          ‖mFun N (specOf Sig) ((E : ℂ) + η * Complex.I)‖ ≤ K ∧
          ∀ s t : Fin M ⊕ Fin N,
            ‖piMat Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I)) s t‖ ≤ K := by
  obtain ⟨hτ₂, -⟩ := ec_tau_facts hτ
  have hc := ec_C_pos hτ
  have hCm := mBoundConst_pos hτ₂
  refine ⟨τ⁻¹ * (ecC τ)⁻¹ + mBoundConst (ecTau τ), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((ec_window hτ hε hε1).and (ec_window_m hτ hε hε1))
  refine ⟨N₀, fun N hN M Sig k hSig h hk E hE η hη₁ hη₂ => ?_⟩
  obtain ⟨hw1, hw2⟩ := hN₀ N hN
  obtain ⟨-, hPsi, -⟩ := hw1 M (specOf Sig) k h hk E hE η hη₁ hη₂
  obtain ⟨hOne, hm⟩ := hw2 M (specOf Sig) k h hk E hE η hη₁ hη₂
  refine ⟨hPsi, by linarith [mul_nonneg (inv_nonneg.2 hτ.le) (inv_nonneg.2 hc.le)], ?_⟩
  exact ec_piMat_le hSig (inv_nonneg.2 hτ.le) h.bound_Sigma hc hCm.le hOne hm

/-- The `m`-difference at the counting points of a regular edge (from (z-a_taylor)): for
`|E_j - a_k| ≤ 3N^{-2/3+ε}`, `N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}` and `z_j = E_j + iη`,
`|m(z_1) - x_k| ≤ 4 c₂^{-1/2} N^{-1/3+ε/2}`, `|m(z_2) - m(z_1)| ≤ 8 c₂^{-1/2} N^{-1/3+ε/2}`, and
`|m(z_2) Π_{ii}(z_2) - m(z_1) Π_{ii}(z_1)| ≤ K N^{-1/3+ε/2}` for every `i ∈ 𝓘_M`, with `K` depending
only on `τ`. -/
theorem dot_mPi_window (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
      Sig.PosDef → DensityAssumptions τ N (specOf Sig) → RegularEdge τ N (specOf Sig) k →
      ∀ E₁ E₂ : ℝ, |E₁ - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        |E₂ - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
        ‖mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I) - xCrit N (specOf Sig) k‖ ≤
            4 / √(edgec2 τ) * (N : ℝ) ^ (-1 / 3 + ε / 2) ∧
          ‖mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) -
              mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I)‖ ≤
            8 / √(edgec2 τ) * (N : ℝ) ^ (-1 / 3 + ε / 2) ∧
          ∀ i : Fin M,
            ‖mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I))
                  (Sum.inl i) (Sum.inl i) -
              mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I))
                  (Sum.inl i) (Sum.inl i)‖ ≤ K * (N : ℝ) ^ (-1 / 3 + ε / 2) := by
  have hc := ec_C_pos hτ
  have hc2 := edgec2_pos hτ
  have hsc2 : 0 < √(edgec2 τ) := Real.sqrt_pos.2 hc2
  refine ⟨τ⁻¹ * (ecC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ)), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (((ec_window hτ hε hε1).and (ec_window_m hτ hε hε1)).and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN M Sig k hSig h hk E₁ E₂ hE₁ hE₂ η hη₁ hη₂ => ?_⟩
  obtain ⟨⟨hw1, hw2⟩, hN1⟩ := hN₀ N hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  set b : ℝ := -1 / 3 + ε / 2 with hbdef
  have hbb : (N : ℝ) ^ b * (N : ℝ) ^ b = (N : ℝ) ^ (-2 / 3 + ε) := by
    rw [← Real.rpow_add hn]; congr 1; rw [hbdef]; ring
  have hb0 : 0 < (N : ℝ) ^ b := Real.rpow_pos_of_pos hn _
  have hpt : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ‖mFun N (specOf Sig) ((E : ℂ) + η * Complex.I) - xCrit N (specOf Sig) k‖ ≤
        4 / √(edgec2 τ) * (N : ℝ) ^ b := by
    intro E hE
    obtain ⟨hdom, -, hza, hza'⟩ := hw1 M (specOf Sig) k h hk E hE η hη₁ hη₂
    have hz : 0 < ((E : ℂ) + η * Complex.I).im := hdom.1.1
    refine (entryBounds_mFun_sub_xCrit h hk hz (hza.trans hza')).trans ?_
    rw [Real.sqrt_le_left (by positivity), mul_pow, div_pow, Real.sq_sqrt hc2.le,
      sq ((N : ℝ) ^ b), hbb, div_le_iff₀ hc2]
    have e : (4 : ℝ) ^ 2 / edgec2 τ * (N : ℝ) ^ (-2 / 3 + ε) * edgec2 τ =
        16 * (N : ℝ) ^ (-2 / 3 + ε) := by
      field_simp; norm_num
    rw [e]
    linarith
  have hm1 := hpt E₁ hE₁
  have hm2 := hpt E₂ hE₂
  have hdiff : ‖mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) -
      mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I)‖ ≤
      8 / √(edgec2 τ) * (N : ℝ) ^ b := by
    have e : mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) -
        mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I) =
        (mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) - xCrit N (specOf Sig) k) -
          (mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I) - xCrit N (specOf Sig) k) := by
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have e8 : 8 / √(edgec2 τ) * (N : ℝ) ^ b =
        4 / √(edgec2 τ) * (N : ℝ) ^ b + 4 / √(edgec2 τ) * (N : ℝ) ^ b := by ring
    rw [e8]
    exact add_le_add hm2 hm1
  refine ⟨hm1, hdiff, fun i => ?_⟩
  have hO1 := (hw2 M (specOf Sig) k h hk E₁ hE₁ η hη₁ hη₂).1
  have hO2 := (hw2 M (specOf Sig) k h hk E₂ hE₂ η hη₁ hη₂).1
  refine (ec_mPi_sub hSig (inv_nonneg.2 hτ.le) h.bound_Sigma hc hO1 hO2 i).trans ?_
  have hA : 0 ≤ τ⁻¹ * (ecC τ)⁻¹ ^ 2 := by positivity
  calc τ⁻¹ * (ecC τ)⁻¹ ^ 2 * ‖mFun N (specOf Sig) ((E₂ : ℂ) + η * Complex.I) -
        mFun N (specOf Sig) ((E₁ : ℂ) + η * Complex.I)‖
      ≤ τ⁻¹ * (ecC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ) * (N : ℝ) ^ b) :=
        mul_le_mul_of_nonneg_left hdiff hA
    _ = τ⁻¹ * (ecC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ)) * (N : ℝ) ^ b := by ring

/-- Theorem 11.2 at the counting points: `|⟨x, (Ġ - Π̇) y⟩| ≺ Ψ |Σ̲ x| |Σ̲ y|`, with the laws for
`G` on `𝐃^e_k(τ₂, τ'', N)` from Theorem 3.14 (i). -/
private lemma ec_law (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      ∀ x y : Fin M ⊕ Fin N → ℝ, DomAt N ε' D
        (fun ω => ‖testBilin x (G Sig (Xdot (X ω)) ((E : ℂ) + η * Complex.I) -
          piMatDot Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I))
            ((E : ℂ) + η * Complex.I)) y‖)
        (fun _ => Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) *
          testNorm (ecR Sig *ᵥ x) * testNorm (ecR Sig *ᵥ y)) := by
  obtain ⟨hτ₂, hτ₂a, -, -, hτ'', hτ''a, -⟩ := ec_tau_facts hτ
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := local_laws_dot (ecTau τ) C ε' D hτ₂ hε'
  obtain ⟨N₂, h₂⟩ := edge_law (ecTau τ) (ecTau'' τ) C ε₁ D₁ hτ₂ hτ'' hτ''a hε₁
  obtain ⟨N₃, h₃⟩ := eventually_atTop.1 (ec_window hτ hε hε1)
  refine ⟨max (max N₁ N₂) N₃, fun N hN Ω _ _ M Sig X k hm hk E hE η hη₁ hη₂ x y => ?_⟩
  have hm2 : IsModel (ecTau τ) C M N Sig X := hm.mono hτ₂ (by linarith)
  have hk2 : RegularEdge (ecTau τ) N (specOf Sig) k := regularEdge_mono hk (by linarith)
  have hl := h₂ N (le_trans (le_max_right _ _) (le_of_max_le_left hN)) M Sig X k hm2 hk2
  have hd := h₁ N (le_trans (le_max_left _ _) (le_of_max_le_left hN)) M Sig X _ hm2
    (spectralDomain_edgeDomain _ _ _ _ _) hl.1 hl.2
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hdom := (h₃ N (le_of_max_le_right hN) M (specOf Sig) k hda hk E hE η hη₁ hη₂).1
  have h := hd.1 _ hdom (ecR Sig *ᵥ x) (ecR Sig *ᵥ y)
  simp only [ec_testBilin_lawMatDot hm.sigma.posDef] at h
  exact h

private lemma ec_Psi_nonneg {σ : Fin M → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hN : 0 < N) : 0 ≤ Psi N σ z := by
  unfold Psi
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- Entry bounds for `G(Ẋ R_μ)` on `J = {i, μ}` at the counting points of a regular edge
(Theorem 11.2 with the test vectors `Σ̲ e_i`, `(0, v̂_μ)`): `|G(Ẋ R_μ)_{ab} - Π_{ab}| ≺ τ⁻² Ψ` for
`a, b ∈ J`, at `z = E + iη`, `N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}`, `|E - a_k| ≤ 3N^{-2/3+ε}`, with
`N₀` uniform in the model, the edge `k`, the point `z` and the entry `(i, μ)`. -/
theorem dot_entry (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      ∀ (i : Fin M) (μ : Fin N),
      ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), DomAt N ε' D
        (fun ω => ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) a b -
          piMat Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I)) a b‖)
        (fun _ => τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) := by
  obtain ⟨N₀, h₀⟩ := ec_law τ C ε ε' D hτ hε hε1 hε'
  refine ⟨max N₀ 2, fun N hN Ω _ _ M Sig X k hm hk E hE η hη₁ hη₂ i μ a ha b hb => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := by omega
  have h := h₀ N (le_of_max_le_left hN) M Sig X k hm hk E hE η hη₁ hη₂ (ecU M N μ a)
    (ecU M N μ b)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨-, hτ1, -⟩ := ec_facts hda
  have hSig := hm.sigma.posDef
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hnorm : ∀ c ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      testNorm (ecR Sig *ᵥ ecU M N μ c) ≤ τ⁻¹ := by
    intro c hc
    have hmc : c = Sum.inl i ∨ c = Sum.inr μ := by simpa using hc
    rcases hmc with rfl | rfl
    · rw [ec_U_inl]
      exact ec_testNorm_col_le hSig hτ hτ1 hda.bound_Sigma _
    · rw [ec_U_inr hN2]
      obtain ⟨h1, h2⟩ := ec_ecR_embN (N := N) Sig (dotVec N μ)
      rw [h1, h2, ec_testNorm_dotVec hN2]
      exact hτi
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hη0 : 0 < etaE N ε := Real.rpow_pos_of_pos hNr _
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    rw [add_zero]
    linarith
  have hP := ec_Psi_nonneg (σ := specOf Sig) hz (show 0 < N by omega)
  refine DomAt.mono hN1 (fun ω => le_of_eq ?_) (fun _ => ?_) (fun _ => by positivity) le_rfl
    le_rfl h
  · rw [ec_G_refl_apply hN2, ← ec_testBilin_piMatDot hN2 _ _ i μ a ha b hb, ← ec_testBilin_sub]
  · have h0a : 0 ≤ testNorm (ecR Sig *ᵥ ecU M N μ a) := Real.sqrt_nonneg _
    have h0b : 0 ≤ testNorm (ecR Sig *ᵥ ecU M N μ b) := Real.sqrt_nonneg _
    calc Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) *
          testNorm (ecR Sig *ᵥ ecU M N μ a) * testNorm (ecR Sig *ᵥ ecU M N μ b)
        ≤ Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) * τ⁻¹ * τ⁻¹ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hnorm a ha) hP) (hnorm b hb) h0b
          exact mul_nonneg hP (inv_nonneg.2 hτ.le)
      _ = τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) := by ring

/-- On the event `|G_{ab} - Π_{ab}| ≤ δ ≤ 1` for `a, b ∈ {i, μ}`: `|G_{ab}| ≤ K + 1`,
`|G_{iμ}|, |G_{μi}| ≤ δ`, and `|G_{ii} G_{μμ} - m Π_{ii}| ≤ (2K + 1) δ`. -/
private lemma ec_consequences {G P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ} {m : ℂ}
    {K δ : ℝ} (i : Fin M) (μ : Fin N) (hPK : ∀ s t, ‖P s t‖ ≤ K)
    (hP1 : P (Sum.inl i) (Sum.inr μ) = 0) (hP2 : P (Sum.inr μ) (Sum.inl i) = 0)
    (hP3 : P (Sum.inr μ) (Sum.inr μ) = m) (hδ1 : δ ≤ 1)
    (h : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b - P a b‖ ≤ δ) :
    (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G a b - P a b‖ ≤ δ ∧ ‖G a b‖ ≤ K + 1) ∧
      ‖G (Sum.inl i) (Sum.inr μ)‖ ≤ δ ∧ ‖G (Sum.inr μ) (Sum.inl i)‖ ≤ δ ∧
      ‖G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
          m * P (Sum.inl i) (Sum.inl i)‖ ≤ (2 * K + 1) * δ := by
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert_of_mem _ rfl
  have hGK : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b‖ ≤ K + 1 := by
    intro a ha b hb
    have e : G a b = P a b + (G a b - P a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hPK a b, h a ha b hb])
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (h _ hiJ _ hiJ)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hPK (Sum.inl i) (Sum.inl i))
  refine ⟨fun a ha b hb => ⟨h a ha b hb, hGK a ha b hb⟩, ?_, ?_, ?_⟩
  · have := h _ hiJ _ hμJ
    rwa [hP1, sub_zero] at this
  · have := h _ hμJ _ hiJ
    rwa [hP2, sub_zero] at this
  · have e : G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
        m * P (Sum.inl i) (Sum.inl i) =
        (G (Sum.inl i) (Sum.inl i) - P (Sum.inl i) (Sum.inl i)) * G (Sum.inr μ) (Sum.inr μ) +
          P (Sum.inl i) (Sum.inl i) * (G (Sum.inr μ) (Sum.inr μ) - P (Sum.inr μ) (Sum.inr μ)) := by
      rw [hP3]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (h _ hiJ _ hiJ) (hGK _ hμJ _ hμJ) (norm_nonneg _) hδ0
    have h2 := mul_le_mul (hPK (Sum.inl i) (Sum.inl i)) (h _ hμJ _ hμJ) (norm_nonneg _) hK0
    calc _ ≤ δ * (K + 1) + K * δ := add_le_add h1 h2
      _ = (2 * K + 1) * δ := by ring

/-- The high-probability event for `G(Ẋ R_μ)` at a counting point `z = E + iη` of a regular edge
and an entry `(i, μ)`, `N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}`, `J = {i, μ}`, `δ = N^{ε'} τ⁻² Ψ(z)`,
`ε' ≤ ε`: on an event of probability
`≥ 1 - N^{-D}`, `|G_{ab} - Π_{ab}| ≤ δ` and `|G_{ab}| ≤ K + 1` for `a, b ∈ J`,
`|G_{iμ}|, |G_{μi}| ≤ δ`, and `|G_{ii} G_{μμ} - m Π_{ii}| ≤ (2K + 1) δ`, with `G = G(Ẋ R_μ)`;
here `δ ≤ 1`, `K` depends only on `τ`, and `N₀` is uniform in the model, `k`, `E` and `(i, μ)`. -/
theorem dot_event (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') (hε'ε : ε' ≤ ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      ∀ (i : Fin M) (μ : Fin N),
        (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ≤ 1 ∧
        HighProbAt N D {ω |
          (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
            ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
              ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) a b -
                  piMat Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I)) a b‖ ≤
                (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
              ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) a b‖ ≤
                K + 1) ∧
          ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I)
              (Sum.inl i) (Sum.inr μ)‖ ≤
            (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
          ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I)
              (Sum.inr μ) (Sum.inl i)‖ ≤
            (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
          ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I)
                (Sum.inl i) (Sum.inl i) *
              G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I)
                (Sum.inr μ) (Sum.inr μ) -
              mFun N (specOf Sig) ((E : ℂ) + η * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I))
                  (Sum.inl i) (Sum.inl i)‖ ≤
            (2 * K + 1) *
              ((N : ℝ) ^ ε' * (τ⁻¹ ^ 2 *
                Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)))} := by
  obtain ⟨K, hK, N₁, hdet⟩ := dot_det τ ε hτ hε hε1
  obtain ⟨N₂, hent⟩ := dot_entry τ C ε ε' (D + 2) hτ hε hε1 hε'
  have hτ2 : 0 < (4 * τ⁻¹ ^ 2)⁻¹ := by positivity
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (ec_ev_small (y := -1 / 3 + 10 * ε) (by linarith) hτ2)
  refine ⟨K, hK, max (max N₁ N₂) (max N₃ 2),
    fun N hN Ω _ _ M Sig X k hm hk E hE η hη₁ hη₂ i μ => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hN4 : 2 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  set z : ℂ := (E : ℂ) + η * Complex.I with hzdef
  obtain ⟨hPsi, hmK, hPK⟩ := hdet N hN1 M Sig k hm.sigma.posDef hda hk E hE η hη₁ hη₂
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN4
  have hn : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  set δ : ℝ := (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) with hδdef
  have hδ1 : δ ≤ 1 := by
    have e1 : (N : ℝ) ^ ε' ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hn1 hε'ε
    have e2 : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have e3 := hN₃ N hN3
    have hz : 0 < z.im := by
      rw [hzdef]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero]
      have : 0 < etaE N ε := Real.rpow_pos_of_pos hn _
      linarith
    have hP0 : 0 ≤ Psi N (specOf Sig) z := ec_Psi_nonneg hz (by omega)
    have hτi : 0 ≤ τ⁻¹ ^ 2 := by positivity
    calc δ ≤ (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * (4 * (N : ℝ) ^ (-1 / 3 + 9 * ε))) := by
          apply mul_le_mul e1 (mul_le_mul_of_nonneg_left hPsi hτi) (by positivity)
            (by positivity)
      _ = 4 * τ⁻¹ ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by ring
      _ = 4 * τ⁻¹ ^ 2 * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by rw [e2]
      _ ≤ 4 * τ⁻¹ ^ 2 * (4 * τ⁻¹ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  refine ⟨hδ1, ?_⟩
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert_of_mem _ rfl
  have h1 := hent N hN2 M Sig X k hm hk E hE η hη₁ hη₂ i μ _ hiJ _ hiJ
  have h2 := hent N hN2 M Sig X k hm hk E hE η hη₁ hη₂ i μ _ hiJ _ hμJ
  have h3 := hent N hN2 M Sig X k hm hk E hE η hη₁ hη₂ i μ _ hμJ _ hiJ
  have h4 := hent N hN2 M Sig X k hm hk E hE η hη₁ hη₂ i μ _ hμJ _ hμJ
  unfold DomAt at h1 h2 h3 h4
  unfold HighProbAt
  set m := mFun N (specOf Sig) z with hmdef
  set W : Ω → Matrix (Fin M) (Fin N) ℝ := fun ω => Xdot (X ω) * dotRefl N μ with hWdef
  have hP1 : piMat (N := N) Sig m (Sum.inl i) (Sum.inr μ) = 0 := by simp [piMat]
  have hP2 : piMat (N := N) Sig m (Sum.inr μ) (Sum.inl i) = 0 := by simp [piMat]
  have hP3 : piMat (N := N) Sig m (Sum.inr μ) (Sum.inr μ) = m := by simp [piMat]
  have hsub : {ω | (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
            ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
              ‖G Sig (W ω) z a b - piMat (N := N) Sig m a b‖ ≤ δ ∧ ‖G Sig (W ω) z a b‖ ≤ K + 1) ∧
          ‖G Sig (W ω) z (Sum.inl i) (Sum.inr μ)‖ ≤ δ ∧
          ‖G Sig (W ω) z (Sum.inr μ) (Sum.inl i)‖ ≤ δ ∧
          ‖G Sig (W ω) z (Sum.inl i) (Sum.inl i) * G Sig (W ω) z (Sum.inr μ) (Sum.inr μ) -
              m * piMat (N := N) Sig m (Sum.inl i) (Sum.inl i)‖ ≤ (2 * K + 1) * δ}ᶜ ⊆
      {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (W ω) z (Sum.inl i) (Sum.inl i) - piMat (N := N) Sig m (Sum.inl i) (Sum.inl i)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (W ω) z (Sum.inl i) (Sum.inr μ) - piMat (N := N) Sig m (Sum.inl i) (Sum.inr μ)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (W ω) z (Sum.inr μ) (Sum.inl i) - piMat (N := N) Sig m (Sum.inr μ) (Sum.inl i)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (W ω) z (Sum.inr μ) (Sum.inr μ) -
            piMat (N := N) Sig m (Sum.inr μ) (Sum.inr μ)‖} := by
    intro ω hω
    by_contra hc
    apply hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
    refine ec_consequences i μ hPK hP1 hP2 hP3 hδ1 ?_
    intro a ha b hb
    have hma : a = Sum.inl i ∨ a = Sum.inr μ := by simpa using ha
    have hmb : b = Sum.inl i ∨ b = Sum.inr μ := by simpa using hb
    rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hn.le _
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
    (add_le_add_left (measure_union_le _ _) _)) _)).trans ?_
  refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans ?_
  rw [← ENNReal.ofReal_add hx0 hx0, ← ENNReal.ofReal_add (by positivity) hx0,
    ← ENNReal.ofReal_add (by positivity) hx0]
  apply ENNReal.ofReal_le_ofReal
  have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 2)) * (N : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  rw [e, Real.rpow_two]
  have hsq : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 2
    norm_num at this
    linarith
  calc (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) +
        (N : ℝ) ^ (-(D + 2)) = (N : ℝ) ^ (-(D + 2)) * 4 := by ring
    _ ≤ (N : ℝ) ^ (-(D + 2)) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hx0

/-- `|∑_μ s_μ π̄_{νμ}|² ` summed over `ν` is at most `|s|²`. -/
private lemma ec_sum_piBar_sq_le (hN : 0 < N) (s : Fin N → ℝ) :
    ∑ ν, (∑ μ, s μ * piBar N ν μ) ^ 2 ≤ ∑ ν, s ν ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set S := ∑ μ, s μ with hS
  have e1 : ∀ ν, ∑ μ, s μ * piBar N ν μ = s ν - (N : ℝ)⁻¹ * S := by
    intro ν
    simp only [ec_piBar_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_mul, hS]
    ring
  simp only [e1]
  have e2 : ∑ ν, (s ν - (N : ℝ)⁻¹ * S) ^ 2 = ∑ ν, s ν ^ 2 - (N : ℝ)⁻¹ * S ^ 2 := by
    have : ∀ ν, (s ν - (N : ℝ)⁻¹ * S) ^ 2 =
        s ν ^ 2 - 2 * (N : ℝ)⁻¹ * S * s ν + ((N : ℝ)⁻¹ * S) ^ 2 := fun ν => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hS,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [e2]
  have : 0 ≤ (N : ℝ)⁻¹ * S ^ 2 := by positivity
  linarith

/-- The bound on `∑_μ s_μ G(Ẋ R_μ)_{μ i} = ⟨∑_μ s_μ v̂_μ, Ġ e_i⟩` for a deterministic
`s ∈ ℝ^{𝓘_N}` at the counting points of a regular edge: since the mixed block of `Π̇` vanishes,
`|∑_μ s_μ G(Ẋ R_μ)_{μ i}(z)| ≺ 2τ⁻¹ Ψ(z) |s|` (Theorem 11.2 with the test vectors
`(0, ∑_μ s_μ v̂_μ)`, `|∑_μ s_μ v̂_μ| ≤ 2|s|`, and `Σ̲ e_i`), at `z = E + iη`,
`N^{-2/3-9ε}/2 ≤ η ≤ N^{-2/3-9ε}`, with `N₀` uniform in the model, the edge `k`, the point `z`, the
vector `s` and the index `i`. -/
theorem dot_sG (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ η : ℝ, etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      ∀ (s : Fin N → ℝ) (i : Fin M), DomAt N ε' D
        (fun ω => ‖∑ μ, (s μ : ℂ) * G Sig (Xdot (X ω) * dotRefl N μ)
          ((E : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖)
        (fun _ => 2 * τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) *
          testNorm s) := by
  obtain ⟨N₀, h₀⟩ := ec_law τ C ε ε' D hτ hε hε1 hε'
  refine ⟨max N₀ 2, fun N hN Ω _ _ M Sig X k hm hk E hE η hη₁ hη₂ s i => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := by omega
  set q : Fin N → ℝ := fun ν => ∑ μ, s μ * dotVec N μ ν with hq
  have h := h₀ N (le_of_max_le_left hN) M Sig X k hm hk E hE η hη₁ hη₂
    (Sum.elim (0 : Fin M → ℝ) q)
    (Pi.single (Sum.inl i) 1)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨-, hτ1, -⟩ := ec_facts hda
  have hSig := hm.sigma.posDef
  have hw := ec_testNorm_col_le (N := N) hSig hτ hτ1 hda.bound_Sigma (Sum.inl i)
  obtain ⟨hv1, hv2⟩ := ec_ecR_embN (N := N) Sig q
  rw [hv1, hv2] at h
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    rw [add_zero]
    have : 0 < etaE N ε := Real.rpow_pos_of_pos hNr _
    linarith
  have hP := ec_Psi_nonneg (σ := specOf Sig) hz (show 0 < N by omega)
  have h0s : 0 ≤ testNorm s := Real.sqrt_nonneg _
  have hqs : testNorm q ≤ 2 * testNorm s := by
    have hL := ec_dotLen_pos hN2
    have hL2 := (dot_dotLen_bounds hN2).1
    have e : ∀ ν, q ν = (∑ μ, s μ * piBar N ν μ) / dotLen N := by
      intro ν
      rw [hq]
      simp only [dotVec, mul_div_assoc', ← Finset.sum_div]
    have hsq : ∑ ν, q ν ^ 2 ≤ 2 ^ 2 * ∑ ν, s ν ^ 2 := by
      simp only [e, div_pow, ← Finset.sum_div]
      rw [div_le_iff₀ (by positivity)]
      have h1 := ec_sum_piBar_sq_le (show 0 < N by omega) s
      have h2 : 1 ≤ 2 ^ 2 * dotLen N ^ 2 := by nlinarith
      have h3 : 0 ≤ ∑ ν, s ν ^ 2 := Finset.sum_nonneg fun ν _ => sq_nonneg _
      nlinarith
    unfold testNorm
    calc √(∑ ν, q ν ^ 2) ≤ √(2 ^ 2 * ∑ ν, s ν ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * √(∑ ν, s ν ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  refine DomAt.mono hN1 (fun ω => le_of_eq ?_) (fun _ => ?_) (fun _ => by positivity) le_rfl
    le_rfl h
  · rw [ec_testBilin_sub, ec_testBilin_embN, ec_testBilin_embN]
    have hz0 : ∑ μ, (q μ : ℂ) * piMatDot Sig (mFun N (specOf Sig)
        ((E : ℂ) + η * Complex.I)) ((E : ℂ) + η * Complex.I)
          (Sum.inr μ) (Sum.inl i) = 0 := by
      refine Finset.sum_eq_zero fun μ _ => ?_
      simp [piMatDot, piMat]
    rw [hz0, sub_zero]
    congr 1
    simp only [dot_G_refl_inr_inl hN2, Finset.mul_sum, hq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  · calc Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) * testNorm q *
          testNorm (ecR (N := N) Sig *ᵥ Pi.single (Sum.inl i) 1)
        ≤ Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) * (2 * testNorm s) * τ⁻¹ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hqs hP) hw (Real.sqrt_nonneg _)
          positivity
      _ = 2 * τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) * testNorm s := by ring

/-! ## Compiled instances

The reflection facts are instantiated at `N = 3`, `μ = 0`. -/

example : 1 / 2 ≤ dotLen 3 ∧ dotLen 3 < 1 := dot_dotLen_bounds (by norm_num)

example : (dotRefl 3 0)ᵀ = dotRefl 3 0 := dot_dotRefl_transpose 0

example : dotRefl 3 0 * dotRefl 3 0 = 1 := dot_dotRefl_mul_self (by norm_num) 0

end Anisotropic

#print axioms Anisotropic.dot_dotLen_bounds
#print axioms Anisotropic.dot_dotRefl_transpose
#print axioms Anisotropic.dot_dotRefl_mul_self
#print axioms Anisotropic.dot_Xdot_Xupd_mul
#print axioms Anisotropic.dot_smCount_mul_refl
#print axioms Anisotropic.dot_smCount_Xupd
#print axioms Anisotropic.dot_iteratedDeriv_smF
#print axioms Anisotropic.dot_contDiff_smCount
#print axioms Anisotropic.dot_G_refl_inr_inl
#print axioms Anisotropic.dot_det
#print axioms Anisotropic.dot_mPi_window
#print axioms Anisotropic.dot_entry
#print axioms Anisotropic.dot_event
#print axioms Anisotropic.dot_sG
