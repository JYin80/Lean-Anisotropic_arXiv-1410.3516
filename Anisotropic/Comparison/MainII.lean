module

public import Anisotropic.Comparison.HatA
public import Anisotropic.Comparison.MainI
public import Anisotropic.Gaussian.Main

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-!
# The Section 7 statements without the third-moment condition, Lemma 8.2, the Grönwall closure
over `𝒱_v`, Proposition 8.1
-/

/-!
The moment-matching expansion (moment_matching) without (zero_third_moment) keeps the terms
`n ∈ [3, 4p]`, and Lemma 7.16 is iterated from `n = 3`. Lemma 8.2 combines Lemma 7.16 with
Lemma 8.3 (`n = 3`) and Lemma 7.17 (`n ∈ [4, 4p]`). Lemmas 7.11 and 7.10 then hold for every `X`,
with the right side `max_{w ∈ 𝒱_v} E F_w^p(X^θ)`. Since `𝒱_w ⊆ 𝒱_v` for `w ∈ 𝒱_v`, Grönwall for
the finite family `θ ↦ E F_w^p(X^θ)`, `w ∈ 𝒱_v`, gives Lemma 7.5 for every `X`. Lemma 7.4 and the
induction on `m` with `C₀ = C₀(τ)`, `δ = min(ε, τ)/(4 C₀(τ))` and the levels `D_m` give
Proposition 8.1.
-/

/-! ## Rough deterministic bounds -/

/-- The `L²` operator norm is at most the Frobenius norm. -/
private theorem m2tP_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖XᵀX‖ ≤ ‖X‖_F² = ∑_{iμ} X_{iμ}²`. -/
private theorem m2tP_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖Aᵀ * A‖ ≤ ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2 := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := m2tP_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

private theorem m2tR_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def m2tSq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem m2tSq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ m2tSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Replacing one entry by `s` raises `‖A‖_F²` by at most `s²`. -/
private theorem m2tSq_Xupd_le (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (s : ℝ) :
    m2tSq (Xupd A i μ s) ≤ m2tSq A + s ^ 2 := by
  unfold m2tSq
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i, μ)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (i, μ))]
  have h : ∑ α ∈ Finset.univ.erase (i, μ), Xupd A i μ s α.1 α.2 ^ 2 =
      ∑ α ∈ Finset.univ.erase (i, μ), A α.1 α.2 ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    have hne : α ≠ (i, μ) := Finset.ne_of_mem_erase hα
    have : ¬ (α.1 = i ∧ α.2 = μ) := fun h => hne (Prod.ext h.1 h.2)
    simp [Xupd, this]
  rw [h]
  simp only [Xupd, and_self, ite_true]
  nlinarith [sq_nonneg (A i μ)]

/-- `1 ≤ N η` on `𝐃(τ, N)`. -/
private theorem m2t_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

/-- `Ψ ≥ 1/(Nη) ≥ τ/N` on `𝐃(τ, N)`. -/
private theorem m2t_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : τ / N ≤ Psi N σ z := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := hz.1
  have hητ : z.im ≤ τ⁻¹ := hz.2.2.2.2
  unfold Psi
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

/-- The rough constant `max(K_r, 1)` of (A_rough), with `K_r = roughConst τ c`. -/
private def m2tKr (τ c : ℝ) : ℝ := max (roughConst τ c) 1

private theorem m2tKr_ge_one {τ c : ℝ} (_hτ : 0 < τ) (_hc : 0 < c) : 1 ≤ m2tKr τ c :=
  le_max_right _ _

/-- `|f_n(A)| ≤ (n+1)^p (2 K N (1 + ‖A‖_F²))^{n+p}` (rough form of (w_est), from (A_rough)). -/
private theorem m2t_rough_fCoeff {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M)
    (μ : Fin N) (p n : ℕ) :
    ‖fCoeff p (resCoeff Sig A z v i μ) n‖ ≤
      ((n : ℝ) + 1) ^ p * (2 * (m2tKr τ c * (N * (1 + m2tSq A)))) ^ (n + p) := by
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hNη := m2t_one_le_N_im hN hset.pos hzD
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := m2tSq_nonneg A
  have hKr1 : 1 ≤ m2tKr τ c := le_max_right _ _
  have hτ := hset.pos
  have hR0 : 0 ≤ roughConst τ c := by
    unfold roughConst
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    have : 0 < max c⁻¹ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  set B := m2tKr τ c * (N * (1 + m2tSq A)) with hB
  have hNW : 1 ≤ (N : ℝ) * (1 + m2tSq A) := by nlinarith
  have hB1 : 1 ≤ B := by nlinarith
  have hw : ∀ k (w : Word k), ‖wordA Sig A z v i μ k w‖ ≤ B ^ (k + 1) := by
    intro k w
    refine (norm_wordA_rough hset hz A v hv i μ k w).trans (pow_le_pow_left₀ ?_ ?_ _)
    · have : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
      positivity
    · have h1 : (1 + ‖Aᵀ * A‖) / z.im ≤ N * (1 + m2tSq A) := by
        rw [div_le_iff₀ hη]
        have hX : ‖Aᵀ * A‖ ≤ m2tSq A := m2tP_XtX_le A
        have h2 : (1 + m2tSq A) * 1 ≤ (1 + m2tSq A) * ((N : ℝ) * z.im) :=
          mul_le_mul_of_nonneg_left hNη (by linarith)
        nlinarith
      rw [mul_div_assoc]
      exact mul_le_mul (le_max_left _ _) h1 (by positivity) (by linarith)
  refine norm_fCoeff_le p (by linarith) n fun k _ => ?_
  rw [resCoeff_eq_sum_wordA hset.sigma.posDef A hη v i μ k, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul]
  calc ‖∑ w : Word k, wordA Sig A z v i μ k w‖ ≤ ∑ w : Word k, ‖wordA Sig A z v i μ k w‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _w : Word k, B ^ (k + 1) := Finset.sum_le_sum fun w _ => hw k w
    _ = 2 ^ k * B ^ (k + 1) := by simp
    _ ≤ 2 ^ (k + 1) * B ^ (k + 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = (2 * B) ^ (k + 1) := (mul_pow 2 B (k + 1)).symm

/-! ## Continuity in the entries -/

private theorem m2t_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
  have hc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
    unfold linH cplx
    refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
    · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
    · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ • (linH Sig⁻¹ A z).adjugate := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Continuous.smul ((hc.matrix_det).inv₀ fun A => ?_) hc.matrix_adjugate
  exact ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig A hz)).ne_zero

private theorem m2t_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => m2tR_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem m2t_continuous_Xupd (i : Fin M) (μ : Fin N) :
    Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ => Xupd q.1 i μ q.2 := by
  refine continuous_pi fun j => continuous_pi fun ν => ?_
  simp only [Xupd]
  split_ifs
  · exact continuous_snd
  · exact continuous_fst.matrix_elem j ν

private theorem m2t_continuous_resCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => resCoeff Sig A z v i μ k := by
  have hG := m2t_continuous_G (N := N) hSig hz
  unfold resCoeff
  refine continuous_const.mul ((m2t_continuous_ent _ _).comp ?_)
  exact (hG.matrix_mul ((continuous_const.matrix_mul hG).pow k)).sub continuous_const

private theorem m2t_continuous_fCoeff {X : Type*} [TopologicalSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Continuous fun x => a x k) :
    Continuous fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.comp (ha _)

/-- `F_v = |a_0|`. -/
private theorem m2t_Fv_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    Fv Sig A z v = ‖resCoeff Sig A z v i μ 0‖ := by
  simp [resCoeff, Fv]

/-- `F_v^p = f_0` for even `p`. -/
private theorem m2t_Fv_pow_eq {p : ℕ} (hp : Even p) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    (Fv Sig A z v : ℂ) ^ p = fCoeff p (resCoeff Sig A z v i μ) 0 := by
  rw [fCoeff_zero hp, m2t_Fv_eq Sig A z v i μ]

private theorem m2t_continuous_fCoeff_upd {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (p n : ℕ) :
    Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      fCoeff p (resCoeff Sig (Xupd q.1 i μ q.2) z v i μ) n :=
  m2t_continuous_fCoeff p n fun k =>
    (m2t_continuous_resCoeff hSig hz v i μ k).comp (m2t_continuous_Xupd i μ)

/-! ## Moments, Markov, events -/

private theorem m2t_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : A ⊆ B) (hA : HighProbAt N D A) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 h)).trans hA

private theorem m2t_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

private theorem m2t_pow_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (q : ℕ) :
    (a + b + c) ^ q ≤ 4 ^ q * (a ^ q + b ^ q + c ^ q) := by
  have h1 := add_pow_le (add_nonneg ha hb) hc q
  have h2 := add_pow_le ha hb q
  have h3 : (2 : ℝ) ^ (q - 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (Nat.sub_le q 1)
  have h4 : (4 : ℝ) ^ q = 2 ^ q * 2 ^ q := by rw [← mul_pow]; norm_num
  have h5 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hab : 0 ≤ a ^ q + b ^ q := by positivity
  have hc' : 0 ≤ c ^ q := by positivity
  have hq0 : (0 : ℝ) ≤ 2 ^ (q - 1) := by positivity
  have h6 : (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) :=
    h2.trans (mul_le_mul_of_nonneg_right h3 hab)
  have h7 : (a + b) ^ q + c ^ q ≤ 2 ^ q * (a ^ q + b ^ q + c ^ q) := by nlinarith
  calc (a + b + c) ^ q ≤ 2 ^ (q - 1) * ((a + b) ^ q + c ^ q) := h1
    _ ≤ 2 ^ q * (2 ^ q * (a ^ q + b ^ q + c ^ q)) :=
        mul_le_mul h3 h7 (by positivity) (by positivity)
    _ = 4 ^ q * (a ^ q + b ^ q + c ^ q) := by rw [h4]; ring

/-- The moment constant `4^q (2 + τ^{−q}) (1 + C'_{2q})`. -/
private def m2tKW (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  4 ^ q * (2 + τ⁻¹ ^ q) * (1 + max (C (2 * q)) 0)

/-- Moments of `W = 1 + ‖X‖_F² + y²`: `E W^q ≤ 4^q (2 + τ^{−q}) (1 + C'_{2q}) N^{2q}`. -/
private theorem m2t_moment_W {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {y : Ω → ℝ}
    (hX : EntryAssumption C X) (hy : Measurable y)
    (hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + m2tSq (X ω) + y ω ^ 2) ^ q) ∧
      ∫ ω, (1 + m2tSq (X ω) + y ω ^ 2) ^ q ≤ m2tKW τ C q * (N : ℝ) ^ (2 * q) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, mul_zero]
    unfold m2tKW
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set C' := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : ∀ t : ℝ, (t ^ 2) ^ (n + 1) =
      ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * t| ^ (2 * (n + 1)) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  have hXi : ∀ α : Fin M × Fin N, Integrable fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1) := by
    intro α
    simp_rw [hpow]
    exact (hX.integrable_moment (2 * (n + 1)) α.1 α.2).const_mul _
  have hXle : ∀ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro α
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hX.moment (2 * (n + 1)) α.1 α.2).trans (le_max_left _ _))
      (by positivity)
  have hyi : Integrable fun ω => (y ω ^ 2) ^ (n + 1) := by
    simp_rw [hpow]
    exact (hym (2 * (n + 1))).1.const_mul _
  have hyle : ∫ ω, (y ω ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hym (2 * (n + 1))).2.trans (le_max_left _ _))
      (by positivity)
  set cd : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcd
  have hcdMN : cd = (M : ℝ) * N := by
    rw [hcd, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  have hcd0 : 0 ≤ cd := by rw [hcdMN]; positivity
  have hSi : Integrable fun ω => ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    integrable_finsetSum _ fun α _ => hXi α
  have hSi' : Integrable fun ω => cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    hSi.const_mul _
  have h1i : Integrable fun ω => 1 + cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    (integrable_const _).add hSi'
  have h2i : Integrable fun ω =>
      1 + cd ^ n * (∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1)) + (y ω ^ 2) ^ (n + 1) :=
    h1i.add hyi
  set g : Ω → ℝ := fun ω => 4 ^ (n + 1) * (1 + cd ^ n * (∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) + (y ω ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := h2i.const_mul _
  have hle : ∀ ω, (1 + m2tSq (X ω) + y ω ^ 2) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := m2t_pow_three_le zero_le_one (m2tSq_nonneg (X ω)) (sq_nonneg (y ω)) (n + 1)
    have h2 : m2tSq (X ω) ^ (n + 1) ≤ cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg, one_pow]
          gcongr
  have hmeas : Measurable fun ω => (1 + m2tSq (X ω) + y ω ^ 2) ^ (n + 1) := by
    unfold m2tSq
    refine ((measurable_const.add (Finset.measurable_sum _ fun α _ =>
      (hX.measurable α.1 α.2).pow_const 2)).add (hy.pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + m2tSq (X ω) + y ω ^ 2) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := m2tSq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 4 ^ (n + 1) * (1 + cd ^ n * (∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) + ∫ ω, (y ω ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add h1i hyi, integral_add (integrable_const _) hSi',
      integral_const_mul, integral_finsetSum _ fun α _ => hXi α]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum : ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      cd * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ _α : Fin M × Fin N, ((N : ℝ) ^ (n + 1))⁻¹ * C' :=
          Finset.sum_le_sum fun α _ => hXle α
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM1 : cd ^ n * (cd * (((N : ℝ) ^ (n + 1))⁻¹ * C')) = (M : ℝ) ^ (n + 1) * C' := by
    rw [hcdMN]
    field_simp
    ring
  have hM2 : (M : ℝ) ^ (n + 1) ≤ τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
  have hNn : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN1r
  have hN2 : (N : ℝ) ^ (2 * (n + 1)) = (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [two_mul, pow_add]
  have hyC : ((N : ℝ) ^ (n + 1))⁻¹ * C' ≤ C' :=
    mul_le_of_le_one_left hC'0 (inv_le_one_of_one_le₀ hNn)
  have hτn : 0 ≤ τ⁻¹ ^ (n + 1) := by positivity
  calc ∫ ω, (1 + m2tSq (X ω) + y ω ^ 2) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 4 ^ (n + 1) * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have h5 := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith [hyle, hyC]
    _ ≤ m2tKW τ C (n + 1) * (N : ℝ) ^ (2 * (n + 1)) := by
        unfold m2tKW
        rw [← hC', hN2]
        have h4 : (0 : ℝ) ≤ 4 ^ (n + 1) := by positivity
        have hA : 1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C' ≤
            (2 + τ⁻¹ ^ (n + 1)) * (1 + C') * ((N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1)) := by
          have hNN : (N : ℝ) ^ (n + 1) ≤ (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) :=
            le_mul_of_one_le_left (by positivity) hNn
          have hNN1 : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by nlinarith
          nlinarith [mul_nonneg hτn hC'0, mul_nonneg (mul_nonneg hτn hC'0) (sub_nonneg.2 hNN)]
        calc 4 ^ (n + 1) * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C') ≤
            4 ^ (n + 1) * ((2 + τ⁻¹ ^ (n + 1)) * (1 + C') *
              ((N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1))) := mul_le_mul_of_nonneg_left hA h4
          _ = _ := by ring

/-- `|y| ≤ N^{ε − 1/2}` with probability `≥ 1 − N^{−D}`, from the moments of `√N y` (Markov). -/
private theorem m2t_markov (C : ℕ → ℝ) (ε D : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (y : Ω → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
      HighProbAt N D {ω | |y ω| ≤ (N : ℝ) ^ (ε - 1 / 2)} := by
  set q : ℕ := ⌈2 * max D 0 / ε⌉₊ + 1 with hq
  set Cq := max (C q) 1 with hCq
  refine ⟨max 1 ⌈Cq ^ (ε / 2)⁻¹⌉₊, fun N hN Ω _ _ y hy => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hCqN : Cq ≤ (N : ℝ) ^ (ε / 2) :=
    m2t_le_rpow (zero_le_one.trans (le_max_right _ _)) (by positivity)
      (le_trans (le_max_right _ _) hN)
  have hq1 : 2 * max D 0 / ε ≤ (q : ℝ) := by
    rw [hq]; push_cast
    linarith [Nat.le_ceil (2 * max D 0 / ε)]
  have hp : D ≤ (ε - ε / 2) * q := by
    calc D ≤ max D 0 := le_max_left _ _
      _ = (ε - ε / 2) * (2 * max D 0 / ε) := by field_simp; ring
      _ ≤ (ε - ε / 2) * q := mul_le_mul_of_nonneg_left hq1 (by linarith)
  have hNe1 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1r (by positivity)
  have hmom : ∫ ω, |Real.sqrt N * y ω| ^ q ≤ ((N : ℝ) ^ (ε / 2) * 1) ^ q := by
    rw [mul_one]
    calc ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q := (hy q).2
      _ ≤ Cq := le_max_left _ _
      _ ≤ (N : ℝ) ^ (ε / 2) := hCqN
      _ ≤ ((N : ℝ) ^ (ε / 2)) ^ q := le_self_pow₀ hNe1 (by omega)
  have hd := DomAt.of_moment (ε := ε / 2) (ε' := ε) (D := D) (ζ := 1)
    (ξ := fun ω => |Real.sqrt N * y ω|) q hN1 hp (fun ω => abs_nonneg _) one_pos
    (hy q).1 hmom
  unfold DomAt at hd
  unfold HighProbAt
  refine le_trans (measure_mono fun ω hω => ?_) hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
  have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  rw [abs_mul, abs_of_pos hsq0, mul_one]
  have e : (N : ℝ) ^ ε = Real.sqrt N * (N : ℝ) ^ (ε - 1 / 2) := by
    rw [hsq, ← Real.rpow_add hNp]; ring_nf
  rw [e]
  exact mul_lt_mul_of_pos_left hω hsq0

private theorem m2t_hp_level {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D D' : ℝ} {A : Set Ω}
    (hN : 1 ≤ N) (hD : D' ≤ D) (hA : HighProbAt N D A) : HighProbAt N D' A := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HighProbAt at *
  exact hA.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)))

private theorem m2t_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- The remainder of order `4p + 1` (re-expansion with remainder, exponents of (Taylo_id1)):
`|f_l(t) − ∑_{k ≤ 4p−l} C(l+k, l) t^k f_{l+k}(0)| ≤ N^{l/2−2} Ψ^p` for `|t| ≤ N^{ε_A − 1/2}` and
`|f_{4p+1}| ≤ N^{(2δ+4ε_A)(5p+1)}` on `[0, t]`. -/
private theorem m2t_rem_det {τ δ εA : ℝ} {p : ℕ} (hp2 : 2 ≤ p) (hτ : 0 < τ) (hδ1 : δ ≤ 1 / 100)
    (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) {N : ℕ} (hN : 1 ≤ N)
    (hN10 : ((4 * p + 1).factorial : ℝ) ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ))
    {σ : Fin M → ℝ} {z : ℂ} (hz : z ∈ specDomain τ N) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x)
    (t : ℝ) (ht : |t| ≤ (N : ℝ) ^ (εA - 1 / 2))
    (hB : ∀ s : ℝ, |s| ≤ |t| → ‖fCoeff p (a s) (4 * p + 1)‖ ≤
      (N : ℝ) ^ ((2 * δ + 4 * εA) * (((4 * p + 1 : ℕ) : ℝ) + p)))
    (l : ℕ) (hl : l ≤ 4 * p) :
    ‖fCoeff p (a t) l - ∑ k ∈ Finset.range (4 * p - l + 1),
        ((l + k).choose l : ℂ) * (t : ℂ) ^ k * fCoeff p (a 0) (l + k)‖ ≤
      (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set eB : ℝ := (2 * δ + 4 * εA) * (((4 * p + 1 : ℕ) : ℝ) + p) with heB
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 t ((N : ℝ) ^ eB) (fun s hs => by
    rw [zero_add, hidx]
    exact hB s (m2t_abs_le_of_mem_uIcc hs))
  rw [zero_add, hidx] at hT
  refine hT.trans ?_
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set et : ℝ := (εA - 1 / 2) * ((4 * p - l + 1 : ℕ) : ℝ) with het
  have htk : |t| ^ (4 * p - l + 1) ≤ (N : ℝ) ^ et := by
    rw [het, Real.rpow_mul hNp.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ ht0 ht _
  have hΨ := m2t_Psi_ge (σ := σ) hN hτ hz
  have hΨp : (τ / N) ^ p ≤ Psi N σ z ^ p := pow_le_pow_left₀ (by positivity) hΨ p
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hL : (l : ℝ) ≤ 4 * p := by exact_mod_cast hl
  have hL0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hcast : ((4 * p - l + 1 : ℕ) : ℝ) = 4 * p - l + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hl]; push_cast; ring
  have hδ0 : 0 < δ := by linarith
  have hexp : 1 / 10 + eB + et ≤ (l : ℝ) / 2 - 2 - p := by
    rw [het, hcast, heB]
    push_cast
    have h1 : (2 * δ + 4 * εA) * (4 * p + 1 + p) ≤ 3 * δ * (5 * p + 1) := by nlinarith
    have h2 : εA * (4 * p - l + 1) ≤ δ / 4 * (4 * p + 1) := by nlinarith
    nlinarith
  have hfac0 : (0 : ℝ) ≤ ((4 * p + 1).factorial : ℝ) := Nat.cast_nonneg _
  calc ((4 * p + 1).factorial : ℝ) * (N : ℝ) ^ eB * |t| ^ (4 * p - l + 1)
      ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ eB * (N : ℝ) ^ et := by
        gcongr
    _ = τ ^ p * (N : ℝ) ^ (1 / 10 + eB + et) := by
        rw [Real.rpow_add hNp, Real.rpow_add hNp]; ring
    _ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) := by
        gcongr
    _ = (N : ℝ) ^ ((l : ℝ) / 2 - 2) * (τ / N) ^ p := by
        rw [show (l : ℝ) / 2 - 2 - p = ((l : ℝ) / 2 - 2) + (-(p : ℝ)) by ring,
          Real.rpow_add hNp, Real.rpow_neg hNp.le, Real.rpow_natCast, div_pow]
        field_simp
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p := by gcongr

/-- Intersection of two events of probability `≥ 1 − N^{−D}` (union bound), `N ≥ 2`. -/
private theorem m2t_hp_inter {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (hN : 2 ≤ N) (hA : HighProbAt N D A) (hB : HighProbAt N D B) :
    HighProbAt N (D - 1) (A ∩ B) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  unfold HighProbAt at *
  rw [Set.compl_inter]
  have hp : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hpos.le _
  calc ℙ (Aᶜ ∪ Bᶜ) ≤ ℙ Aᶜ + ℙ Bᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) := add_le_add hA hB
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-D)) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 1))) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (N : ℝ) ^ (-(D - 1)) = (N : ℝ) ^ (-D) * N := by
          rw [show -(D - 1) = -D + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
        rw [e]
        nlinarith

/-- The event of Lemma 7.15 at a general `C₀`, for `y` with the moments of an entry:
`|y| ≤ N^{ε_A − 1/2}` and `|f_{4p+1}(s)| ≤ N^{(2δ+4ε_A)(5p+1)}` for all `|s| ≤ |y|`. -/
private theorem m2t_event (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
          ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v : Fin M ⊕ Fin N → ℝ),
          testNorm v = 1 →
          HighProbAt N (DA - 4) {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2) ∧ ∀ s : ℝ, |s| ≤ |y ω| →
            ‖fCoeff p (resCoeff Sig (Xupd (X ω) i μ s) z v i μ) (4 * p + 1)‖ ≤
              (N : ℝ) ^ ((2 * δ + 4 * εA) * (((4 * p + 1 : ℕ) : ℝ) + p))} := by
  obtain ⟨N₁, h₁⟩ := taylor_exp' τ c C p C₀ δ εA DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hεA hεAδ
  obtain ⟨N₂, h₂⟩ := m2t_markov C εA DA hεA
  refine ⟨max (max N₁ N₂) 2, ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X y hX hP hym z hz i μ v hv
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hy := h₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) y hym
  have hev := (h₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) M Sig S P m
    hset hm hA Ω X y hX hP hy z hz i μ v hv).1 (4 * p + 1) le_rfl
  have hy3 : HighProbAt N (DA - 3) {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)} :=
    m2t_hp_level (by omega) (by linarith) hy
  have h := m2t_hp_inter hN2 hy3 hev
  rw [show DA - 3 - 1 = DA - 4 by ring] at h
  exact h

/-! ## Expectations: independence and Lemma 7.7 -/

/-- `R_l(t) = f_l(t) − ∑_{k ≤ 4p−l} C(l+k, l) t^k f_{l+k}(0)` at the base matrix `A`. -/
private def m2tRem (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (p l : ℕ) (t : ℝ) : ℂ :=
  fCoeff p (resCoeff Sig (Xupd A i μ t) z v i μ) l -
    ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * (t : ℂ) ^ k *
      fCoeff p (resCoeff Sig (Xupd A i μ 0) z v i μ) (l + k)

/-- The constant `(4p+1)^p (2K)^{5p}` of `|f_n| ≤ K₁ (N W)^{5p}`, `n ≤ 4p`. -/
private def m2tK1 (τ c : ℝ) (p : ℕ) : ℝ := ((4 * p + 1 : ℝ)) ^ p * (2 * m2tKr τ c) ^ (5 * p)

/-- The constant `K₁ (1 + (4p+1) 2^{4p})` of `|R_l| ≤ K₂ (N W)^{9p}`. -/
private def m2tK2 (τ c : ℝ) (p : ℕ) : ℝ := m2tK1 τ c p * (1 + (4 * p + 1) * 2 ^ (4 * p))

private theorem m2tK1_nonneg {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (p : ℕ) : 0 ≤ m2tK1 τ c p := by
  have := m2tKr_ge_one hτ hc
  unfold m2tK1
  have : (0 : ℝ) ≤ 2 * m2tKr τ c := by linarith
  positivity

/-- `|f_n(A)| ≤ K₁ (N W)^{5p}` for `n ≤ 4p` and `1 + ‖A‖_F² ≤ W`. -/
private theorem m2t_rough_f_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M)
    (μ : Fin N) {p n : ℕ} (hn : n ≤ 4 * p) {W : ℝ} (hW : 1 + m2tSq A ≤ W) :
    ‖fCoeff p (resCoeff Sig A z v i μ) n‖ ≤ m2tK1 τ c p * ((N : ℝ) * W) ^ (5 * p) := by
  have h := m2t_rough_fCoeff hset hN hz v hv A i μ p n
  have hKr := m2tKr_ge_one hset.pos hset.c_pos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := m2tSq_nonneg A
  have hNW : 1 ≤ (N : ℝ) * W := by nlinarith
  have hb1 : 1 ≤ 2 * m2tKr τ c * ((N : ℝ) * W) := by nlinarith
  have hb : 2 * (m2tKr τ c * (N * (1 + m2tSq A))) ≤ 2 * m2tKr τ c * ((N : ℝ) * W) := by
    have : (N : ℝ) * (1 + m2tSq A) ≤ N * W := mul_le_mul_of_nonneg_left hW (by linarith)
    nlinarith
  have hn1 : (n : ℝ) + 1 ≤ 4 * p + 1 := by
    have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
    linarith
  refine h.trans ?_
  calc ((n : ℝ) + 1) ^ p * (2 * (m2tKr τ c * (N * (1 + m2tSq A)))) ^ (n + p)
      ≤ (4 * p + 1 : ℝ) ^ p * (2 * (m2tKr τ c * (N * (1 + m2tSq A)))) ^ (n + p) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn1 p) (by positivity)
    _ ≤ (4 * p + 1 : ℝ) ^ p * (2 * m2tKr τ c * ((N : ℝ) * W)) ^ (5 * p) :=
        mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) hb _).trans
          (pow_le_pow_right₀ hb1 (by omega))) (by positivity)
    _ = m2tK1 τ c p * ((N : ℝ) * W) ^ (5 * p) := by unfold m2tK1; rw [mul_pow]; ring

/-- `|R_l(t)| ≤ K₂ (N W)^{9p}` for `l ≤ 4p` and `1 + ‖A‖_F² + t² ≤ W`. -/
private theorem m2t_rough_R {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M)
    (μ : Fin N) {p l : ℕ} (hl : l ≤ 4 * p) (t : ℝ) {W : ℝ} (hW : 1 + m2tSq A + t ^ 2 ≤ W) :
    ‖m2tRem Sig A z v i μ p l t‖ ≤ m2tK2 τ c p * ((N : ℝ) * W) ^ (9 * p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := m2tSq_nonneg A
  have hW1 : 1 ≤ W := by nlinarith [sq_nonneg t]
  have hNW : 1 ≤ (N : ℝ) * W := by nlinarith
  have hK1 := m2tK1_nonneg hset.pos hset.c_pos p
  set Φ : ℝ := (N : ℝ) * W with hΦ
  have hWt : 1 + m2tSq (Xupd A i μ t) ≤ W := by
    have := m2tSq_Xupd_le A i μ t; linarith
  have hW0 : 1 + m2tSq (Xupd A i μ 0) ≤ W := by
    have := m2tSq_Xupd_le A i μ 0; nlinarith [sq_nonneg t]
  have ht : |t| ≤ Φ := by
    have h1 : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
    have h2 : W ≤ Φ := le_mul_of_one_le_left (by linarith) hN1r
    nlinarith
  have hterm : ∀ k ∈ Finset.range (4 * p - l + 1),
      ‖((l + k).choose l : ℂ) * (t : ℂ) ^ k *
          fCoeff p (resCoeff Sig (Xupd A i μ 0) z v i μ) (l + k)‖
        ≤ 2 ^ (4 * p) * (m2tK1 τ c p * Φ ^ (9 * p)) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hc : ((l + k).choose l : ℝ) ≤ 2 ^ (4 * p) := by
      have := Nat.choose_le_two_pow (l + k) l
      have h2 : 2 ^ (l + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this.trans h2
    have htk : |t| ^ k ≤ Φ ^ (4 * p) :=
      (pow_le_pow_left₀ (abs_nonneg t) ht k).trans (pow_le_pow_right₀ hNW (by omega))
    have hf := m2t_rough_f_le hset hN hz hv (Xupd A i μ 0) i μ (p := p) (n := l + k) (by omega) hW0
    have e : Φ ^ (9 * p) = Φ ^ (4 * p) * Φ ^ (5 * p) := by rw [← pow_add]; ring_nf
    rw [e]
    have h0 : 0 ≤ |t| ^ k := by positivity
    calc ((l + k).choose l : ℝ) * |t| ^ k * ‖fCoeff p (resCoeff Sig (Xupd A i μ 0) z v i μ) (l + k)‖
        ≤ 2 ^ (4 * p) * Φ ^ (4 * p) * (m2tK1 τ c p * Φ ^ (5 * p)) := by
          gcongr
      _ = 2 ^ (4 * p) * (m2tK1 τ c p * (Φ ^ (4 * p) * Φ ^ (5 * p))) := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfl := m2t_rough_f_le hset hN hz hv (Xupd A i μ t) i μ (p := p) (n := l) hl hWt
  have h59 : Φ ^ (5 * p) ≤ Φ ^ (9 * p) := pow_le_pow_right₀ hNW (by omega)
  have hcard : ((4 * p - l + 1 : ℕ) : ℝ) ≤ 4 * p + 1 := by
    have : 4 * p - l + 1 ≤ 4 * p + 1 := by omega
    exact_mod_cast this
  unfold m2tRem
  refine (norm_sub_le _ _).trans ?_
  have hΦ0 : 0 ≤ Φ ^ (9 * p) := by positivity
  have hA0 : 0 ≤ 2 ^ (4 * p) * (m2tK1 τ c p * Φ ^ (9 * p)) := by positivity
  calc _ ≤ m2tK1 τ c p * Φ ^ (5 * p) +
        ((4 * p - l + 1 : ℕ) : ℝ) * (2 ^ (4 * p) * (m2tK1 τ c p * Φ ^ (9 * p))) :=
        add_le_add hfl hsum
    _ ≤ m2tK1 τ c p * Φ ^ (9 * p) + (4 * p + 1) * (2 ^ (4 * p) * (m2tK1 τ c p * Φ ^ (9 * p))) := by
        gcongr
    _ = m2tK2 τ c p * Φ ^ (9 * p) := by unfold m2tK2; ring

/-- Expectation of the re-expansion: for `y` independent of `X^{(iμ),0}`,
`E f_l(y) = ∑_k C(l+k, l) E y^k E f_{l+k}(0) + E R_l`, and Lemma 7.7 bounds `|E R_l| ≤ 2N^δ Γ`
on the event `|R_l| ≤ Γ`. -/
private theorem m2t_expect {τ c : ℝ} {C : ℕ → ℝ} {p : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {y : Ω → ℝ} (hX : EntryAssumption C X)
    (hy : Measurable y)
    (hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hind : IndepFun (fun ω => Xupd (X ω) i μ 0) y) (l : ℕ) (hl : l ≤ 4 * p)
    {δ D Γ : ℝ} (hδ : 0 ≤ δ) (hD : 3 * (54 * (p : ℝ) + 1) ≤ D)
    (hΓ : (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ Γ)
    (hK : m2tK2 τ c p ^ 2 * m2tKW τ C (18 * p) ≤ N)
    (hev : HighProbAt N D {ω | ‖m2tRem Sig (X ω) z v i μ p l (y ω)‖ ≤ Γ}) :
    (∀ n ≤ 4 * p, Integrable fun ω => fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n) ∧
    (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l) =
      (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * (∫ ω, (y ω : ℂ) ^ k) *
        (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k))) +
        ∫ ω, m2tRem Sig (X ω) z v i μ p l (y ω) ∧
    ‖∫ ω, m2tRem Sig (X ω) z v i μ p l (y ω)‖ ≤ 2 * (N : ℝ) ^ δ * Γ := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hSig := hset.sigma.posDef
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  set W : Ω → ℝ := fun ω => 1 + m2tSq (X ω) + y ω ^ 2 with hW
  have hW1 : ∀ ω, 1 ≤ W ω := fun ω => by
    have := m2tSq_nonneg (X ω); simp only [hW]; nlinarith [sq_nonneg (y ω)]
  have hmom := m2t_moment_W hset.pos hX hy hym hN hM
  have hK1 := m2tK1_nonneg hset.pos hset.c_pos p
  -- integrability from a polynomial bound in `N W`
  have hint : ∀ (g : Ω → ℂ) (K : ℝ) (q : ℕ), AEStronglyMeasurable g →
      (∀ ω, ‖g ω‖ ≤ K * ((N : ℝ) * W ω) ^ q) → Integrable g := by
    intro g K q hg hb
    refine ((hmom q).1.const_mul (K * (N : ℝ) ^ q)).mono' hg (ae_of_all _ fun ω => ?_)
    refine (hb ω).trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have hcont0 : ∀ n, Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      fCoeff p (resCoeff Sig A z v i μ) n :=
    fun n => m2t_continuous_fCoeff p n fun k => m2t_continuous_resCoeff hSig hη v i μ k
  have hXupd0 : Measurable fun ω => Xupd (X ω) i μ 0 :=
    (m2t_continuous_Xupd i μ).measurable.comp (hXm.prodMk measurable_const)
  have hF0m : ∀ n, AEStronglyMeasurable fun ω =>
      fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n :=
    fun n => ((hcont0 n).measurable.comp hXupd0).aestronglyMeasurable
  have hFym : AEStronglyMeasurable fun ω =>
      fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l :=
    ((m2t_continuous_fCoeff_upd hSig hη v i μ p l).measurable.comp
      (hXm.prodMk hy)).aestronglyMeasurable
  have hpowm : ∀ k : ℕ, Measurable fun t : ℝ => (t : ℂ) ^ k :=
    fun k => Complex.measurable_ofReal.pow_const k
  have hym' : ∀ k : ℕ, AEStronglyMeasurable fun ω => (y ω : ℂ) ^ k :=
    fun k => ((hpowm k).comp hy).aestronglyMeasurable
  have hW0 : ∀ ω, 1 + m2tSq (Xupd (X ω) i μ 0) ≤ W ω := fun ω => by
    have := m2tSq_Xupd_le (X ω) i μ 0; simp only [hW]; nlinarith [sq_nonneg (y ω)]
  have hWy : ∀ ω, 1 + m2tSq (Xupd (X ω) i μ (y ω)) ≤ W ω := fun ω => by
    have := m2tSq_Xupd_le (X ω) i μ (y ω); simp only [hW]; linarith
  have hNW : ∀ ω, 1 ≤ (N : ℝ) * W ω := fun ω => by nlinarith [hW1 ω]
  have hF0i : ∀ n ≤ 4 * p, Integrable fun ω =>
      fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n :=
    fun n hn => hint _ _ _ (hF0m n) fun ω =>
      m2t_rough_f_le hset hN hz hv _ i μ hn (hW0 ω)
  have hFyi : Integrable fun ω => fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l :=
    hint _ _ _ hFym fun ω => m2t_rough_f_le hset hN hz hv _ i μ hl (hWy ω)
  have hyk : ∀ k ≤ 4 * p, ∀ ω, ‖(y ω : ℂ) ^ k‖ ≤ ((N : ℝ) * W ω) ^ (4 * p) := by
    intro k hk ω
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |y ω| ≤ (N : ℝ) * W ω := by
      have h2 : |y ω| ≤ 1 + y ω ^ 2 := by
        nlinarith [abs_nonneg (y ω), sq_abs (y ω), sq_nonneg (|y ω| - 1)]
      have h3 : W ω ≤ (N : ℝ) * W ω := le_mul_of_one_le_left (by linarith [hW1 ω]) hN1r
      have := m2tSq_nonneg (X ω)
      simp only [hW] at h3 ⊢
      linarith
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 k).trans (pow_le_pow_right₀ (hNW ω) hk)
  have hprodi : ∀ k ∈ Finset.range (4 * p - l + 1), Integrable fun ω =>
      (y ω : ℂ) ^ k * fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    refine hint _ (m2tK1 τ c p) (4 * p + 5 * p) ((hym' k).mul (hF0m (l + k))) fun ω => ?_
    rw [norm_mul, pow_add]
    have h1 := hyk k (by omega) ω
    have h2 := m2t_rough_f_le hset hN hz hv (Xupd (X ω) i μ 0) i μ (p := p) (n := l + k)
      (by omega) (hW0 ω)
    calc _ ≤ ((N : ℝ) * W ω) ^ (4 * p) * (m2tK1 τ c p * ((N : ℝ) * W ω) ^ (5 * p)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (by linarith [hNW ω]) _)
      _ = _ := by ring
  have hprod : ∀ k : ℕ, ∫ ω, (y ω : ℂ) ^ k *
      fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k) =
      (∫ ω, (y ω : ℂ) ^ k) * ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k) :=
    fun k => (hind.symm.comp (hpowm k) (hcont0 (l + k)).measurable).integral_fun_mul_eq_mul_integral
      (hym' k) (hF0m (l + k))
  set Rf : Ω → ℂ := fun ω => m2tRem Sig (X ω) z v i μ p l (y ω) with hRf
  set Sf : Ω → ℂ := fun ω => ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
      ((y ω : ℂ) ^ k * fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k)) with hSf
  have hSi : Integrable Sf := integrable_finsetSum _ fun k hk => (hprodi k hk).const_mul _
  have hdec : ∀ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l = Sf ω + Rf ω := by
    intro ω
    simp only [hSf, hRf, m2tRem]
    rw [Finset.sum_congr rfl fun k _ => (mul_assoc ((l + k).choose l : ℂ) ((y ω : ℂ) ^ k)
      (fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) (l + k))).symm]
    ring
  have hRi : Integrable Rf := by
    have : Rf = fun ω => fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l - Sf ω := by
      funext ω; rw [hdec ω]; ring
    rw [this]; exact hFyi.sub hSi
  refine ⟨hF0i, ?_, ?_⟩
  · calc (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) l)
        = ∫ ω, (Sf ω + Rf ω) := integral_congr_ae (ae_of_all _ hdec)
      _ = (∫ ω, Sf ω) + ∫ ω, Rf ω := integral_add hSi hRi
      _ = _ := by
          congr 1
          rw [hSf, integral_finsetSum _ fun k hk => (hprodi k hk).const_mul _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, hprod k]
          ring
  · -- Lemma 7.7
    set Cr : ℝ := 54 * (p : ℝ) + 1 with hCr
    have hRb : ∀ ω, ‖Rf ω‖ ≤ m2tK2 τ c p * ((N : ℝ) * W ω) ^ (9 * p) := fun ω =>
      m2t_rough_R hset hN hz hv (X ω) i μ hl (y ω) le_rfl
    have hK2 : 0 ≤ m2tK2 τ c p := by
      unfold m2tK2; positivity
    have hRm : AEStronglyMeasurable fun ω => ‖Rf ω‖ ^ 2 := hRi.aestronglyMeasurable.norm.pow 2
    have hR2b : ∀ ω, ‖Rf ω‖ ^ 2 ≤ m2tK2 τ c p ^ 2 * (N : ℝ) ^ (18 * p) * W ω ^ (18 * p) := by
      intro ω
      have h := pow_le_pow_left₀ (norm_nonneg _) (hRb ω) 2
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, ← pow_mul, mul_pow]; ring_nf
    have hR2i : Integrable fun ω => ‖Rf ω‖ ^ 2 :=
      ((hmom (18 * p)).1.const_mul (m2tK2 τ c p ^ 2 * (N : ℝ) ^ (18 * p))).mono' hRm
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]
          refine (hR2b ω).trans (le_of_eq ?_); ring)
    have hR2E : ∫ ω, ‖Rf ω‖ ^ 2 ≤ (N : ℝ) ^ Cr := by
      calc ∫ ω, ‖Rf ω‖ ^ 2 ≤ ∫ ω, m2tK2 τ c p ^ 2 * (N : ℝ) ^ (18 * p) * W ω ^ (18 * p) :=
            integral_mono hR2i ((hmom (18 * p)).1.const_mul _) hR2b
        _ = m2tK2 τ c p ^ 2 * (N : ℝ) ^ (18 * p) * ∫ ω, W ω ^ (18 * p) := integral_const_mul _ _
        _ ≤ m2tK2 τ c p ^ 2 * (N : ℝ) ^ (18 * p) *
            (m2tKW τ C (18 * p) * (N : ℝ) ^ (2 * (18 * p))) :=
            mul_le_mul_of_nonneg_left (hmom (18 * p)).2 (by positivity)
        _ = (m2tK2 τ c p ^ 2 * m2tKW τ C (18 * p)) * (N : ℝ) ^ (54 * p) := by
            rw [show 54 * p = 18 * p + 2 * (18 * p) by ring, pow_add]; ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (54 * p) := by gcongr
        _ = (N : ℝ) ^ Cr := by
            rw [hCr, show (54 * (p : ℝ) + 1) = ((54 * p + 1 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_natCast, pow_succ]; ring
    have hΓ0 : 0 ≤ Γ := (Real.rpow_nonneg hNp.le _).trans hΓ
    have hdom : DomAt N δ D (fun ω => ‖Rf ω‖) (fun _ => Γ) := by
      unfold DomAt
      unfold HighProbAt at hev
      refine le_trans (measure_mono fun ω hω => ?_) hev
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le] at hω ⊢
      have : Γ ≤ (N : ℝ) ^ δ * Γ := le_mul_of_one_le_left hΓ0 (Real.one_le_rpow hN1r hδ)
      exact lt_of_le_of_lt this hω
    have h77 := integral_le_of_domAt (ξ := fun ω => ‖Rf ω‖) hN hδ (C := Cr) hD
      (by rw [hCr]; exact hΓ) (fun ω => norm_nonneg _) hR2i hR2E hdom
    exact (norm_integral_le_integral_norm _).trans h77

/-- `N^{−(54p+1)} ≤ N^{l/2−2} Ψ^p` on `𝐃(τ, N)` for `N ≥ τ⁻¹`. -/
private theorem m2t_Gamma_ge {τ : ℝ} {p l : ℕ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N)
    (hp2 : 2 ≤ p) (hτ : 0 < τ) (hτN : τ⁻¹ ≤ N) (hz : z ∈ specDomain τ N) :
    (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hΨ := m2t_Psi_ge (σ := σ) hN hτ hz
  have h1 : (N : ℝ) ^ (-2 : ℝ) ≤ Psi N σ z := by
    refine le_trans ?_ hΨ
    rw [Real.rpow_neg hNp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      le_div_iff₀ hNp]
    have hτ' : (N : ℝ)⁻¹ ≤ τ := by
      rw [inv_le_comm₀ hNp hτ]; exact hτN
    calc ((N : ℝ) ^ 2)⁻¹ * N = (N : ℝ)⁻¹ := by field_simp
      _ ≤ τ := hτ'
  have h2 : ((N : ℝ) ^ (-2 : ℝ)) ^ p ≤ Psi N σ z ^ p :=
    pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) h1 p
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le] at h2
  have h3 : (N : ℝ) ^ (-2 : ℝ) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  calc (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ (N : ℝ) ^ ((-2 : ℝ) + -2 * p) :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    _ = (N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ (-2 * (p : ℝ)) := Real.rpow_add hNp _ _
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p :=
        mul_le_mul h3 h2 (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)

private theorem m2t_measurable_Xupd (i : Fin M) (μ : Fin N) (t : ℝ) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => Xupd A i μ t :=
  (m2t_continuous_Xupd i μ).measurable.comp (measurable_id.prodMk measurable_const)

private theorem m2t_integral_ofReal_pow {Ω : Type} [MeasureSpace Ω] (y : Ω → ℝ) (k : ℕ) :
    ∫ ω, (y ω : ℂ) ^ k = ((∫ ω, y ω ^ k : ℝ) : ℂ) := by
  simp_rw [← Complex.ofReal_pow]
  exact integral_complex_ofReal

/-! ## The moment-matching expansion without the third-moment condition -/

/-- The moment-matching expansion (moment_matching) without (zero_third_moment): the sum starts
at `n = 3`. -/
theorem moment_matching3 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) (hDA : dPrev p ≤ DA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        IndepFun X y → Measurable y → ∫ ω, y ω = 0 → ∫ ω, y ω ^ 2 = 1 / (N : ℝ) →
        (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
          ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v : Fin M ⊕ Fin N → ℝ),
          testNorm v = 1 →
          ‖(∫ ω, (Fv Sig (Xupd (X ω) i μ (y ω)) z v : ℂ) ^ p)
              - (∫ ω, (fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 0
                  + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 2))
              - ∑ n ∈ Finset.Icc 3 (4 * p),
                  (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n) *
                    ∫ ω, (y ω : ℂ) ^ n‖
            ≤ 2 * (N : ℝ) ^ (δ - 2) * Psi N (specOf Sig) z ^ p := by
  obtain ⟨N₁, h₁⟩ := m2t_event τ c C p C₀ δ εA DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hεA hεAδ
  have h25 : 25 * δ ≤ C₀ * δ := by nlinarith
  have hδ1 : δ ≤ 1 / 100 := by nlinarith
  set K₁ : ℝ := ((4 * p + 1).factorial : ℝ) / τ ^ p with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₃ : ℝ := m2tK2 τ c p ^ 2 * m2tKW τ C (18 * p) with hK₃
  refine ⟨max (max (max N₁ 2) (max 1 ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊)) (max ⌈K₃⌉₊ ⌈τ⁻¹⌉₊), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X y hX hP hXY hy hy1 hy2 hym z hz i μ v hv
  have hNN₁ : N₁ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hNK₃ : ⌈K₃⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hN10 : ((4 * p + 1).factorial : ℝ) ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h := m2t_le_rpow hK₁0 (by norm_num : (0 : ℝ) < 1 / 10) hNK₁
    rw [hK₁, div_le_iff₀ (by positivity)] at h
    linarith
  have hK : K₃ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK₃)
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hSig := hset.sigma.posDef
  have hev := h₁ N hNN₁ M Sig S P m hset hm hA Ω X y hX hP hym z hz i μ v hv
  set Γ : ℝ := (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * Psi N (specOf Sig) z ^ p with hΓ
  have hevR : HighProbAt N (DA - 4)
      {ω | ‖m2tRem Sig (X ω) z v i μ p 0 (y ω)‖ ≤ Γ} := by
    refine m2t_hp_mono (fun ω hω => ?_) hev
    exact m2t_rem_det (σ := specOf Sig) hp2 hτ hδ1 hεA hεAδ hN1 hN10 hzD
      (fun k x => hasDerivAt_resCoeff hSig (X ω) hzD.1 v i μ k x) (y ω) hω.1
      (fun s hs => hω.2 s hs) 0 (by omega)
  have hind : IndepFun (fun ω => Xupd (X ω) i μ 0) y :=
    hXY.comp (m2t_measurable_Xupd i μ 0) measurable_id
  have hD : 3 * (54 * (p : ℝ) + 1) ≤ DA - 4 := by
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    unfold dPrev at hDA
    nlinarith
  obtain ⟨hF0i, hid, hR⟩ := m2t_expect hset hN1 hzS hv i μ hX hy hym hind 0 (Nat.zero_le _)
    hδ.le hD (m2t_Gamma_ge hN1 hp2 hτ hτN hzD) hK hevR
  simp only [Nat.sub_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul] at hid
  have hFv : (∫ ω, (Fv Sig (Xupd (X ω) i μ (y ω)) z v : ℂ) ^ p) =
      ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) 0 :=
    integral_congr_ae (ae_of_all _ fun ω => m2t_Fv_pow_eq hp Sig _ z v i μ)
  have hA02 : (∫ ω, (fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 0
      + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 2)) =
      (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 0) +
        (N : ℂ)⁻¹ * ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 2 := by
    rw [integral_add (hF0i 0 (by omega)) ((hF0i 2 (by omega)).const_mul _), integral_const_mul]
  have hm0 : ∫ ω, (y ω : ℂ) ^ 0 = 1 := by simp
  have hm1 : ∫ ω, (y ω : ℂ) ^ 1 = 0 := by
    rw [m2t_integral_ofReal_pow]; simp [hy1]
  have hm2 : ∫ ω, (y ω : ℂ) ^ 2 = (N : ℂ)⁻¹ := by
    rw [m2t_integral_ofReal_pow, hy2]; push_cast; ring
  set a : ℕ → ℂ := fun n => ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n with ha
  set mm : ℕ → ℂ := fun n => ∫ ω, (y ω : ℂ) ^ n with hmm
  have hsplit : ∑ k ∈ Finset.range (4 * p + 1), mm k * a k =
      mm 0 * a 0 + mm 1 * a 1 + mm 2 * a 2 +
        ∑ n ∈ Finset.Icc 3 (4 * p), a n * mm n := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 3 ≤ 4 * p + 1 by omega)]
    have e : Finset.Icc 3 (4 * p) = Finset.Ico 3 (4 * p + 1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hid' : (∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (y ω)) z v i μ) 0) =
      (∑ k ∈ Finset.range (4 * p + 1), mm k * a k) +
        ∫ ω, m2tRem Sig (X ω) z v i μ p 0 (y ω) := hid
  rw [hFv, hA02, hid', hsplit]
  simp only [hmm, hm0, hm1, hm2, one_mul, zero_mul, add_zero]
  have e2 : ∀ (A0 A2 S0 Rr : ℂ), A0 + (N : ℂ)⁻¹ * A2 + S0 + Rr - (A0 + (N : ℂ)⁻¹ * A2) - S0 = Rr :=
    fun _ _ _ _ => by ring
  rw [show ∀ (A0 A2 S0 Rr : ℂ), A0 + (N : ℂ)⁻¹ * A2 + S0 + Rr - (A0 + (N : ℂ)⁻¹ * A2) - S0 = Rr
    from e2]
  refine hR.trans (le_of_eq ?_)
  have e : (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) = (N : ℝ) ^ (-2 : ℝ) := by norm_num
  rw [e, show δ - 2 = δ + (-2) by ring, Real.rpow_add hNp]
  ring

/-! ## Lemma 7.16 for `n ∈ [3, 4p]` -/

/-- `X_{iμ}` is independent of `X^{(iμ),0}` (the other entries). -/
private theorem m2t_indep_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (i : Fin M) (μ : Fin N) :
    IndepFun (fun ω => Xupd (X ω) i μ 0) (fun ω => X ω i μ) := by
  set T : Finset (Fin M × Fin N) := {(i, μ)} with hT
  set S : Finset (Fin M × Fin N) := Finset.univ.erase (i, μ) with hS
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_singleton_right]
    exact Finset.notMem_erase _ _
  have h := hX.indep.indepFun_finset S T hST (fun q => hX.measurable q.1 q.2)
  let φ : (S → ℝ) → Matrix (Fin M) (Fin N) ℝ :=
    fun x j ν => if hj : (j, ν) ∈ S then x ⟨(j, ν), hj⟩ else 0
  let ψ : (T → ℝ) → ℝ := fun x => x ⟨(i, μ), Finset.mem_singleton_self _⟩
  have hφ : Measurable φ := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => ?_
    by_cases hj : (j, ν) ∈ S
    · simp only [φ, hj, ↓reduceDIte]; exact measurable_pi_apply _
    · simp only [φ, hj, ↓reduceDIte]; exact measurable_const
  have hψ : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφ hψ
  have e1 : (φ ∘ fun a (q : S) => X a (q : Fin M × Fin N).1 (q : Fin M × Fin N).2) =
      fun ω => Xupd (X ω) i μ 0 := by
    funext ω j ν
    simp only [Function.comp, φ, Xupd, hS, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
      Prod.mk.injEq]
    by_cases h' : j = i ∧ ν = μ
    · simp [h']
    · simp [h']
  have e2 : (ψ ∘ fun a (q : T) => X a (q : Fin M × Fin N).1 (q : Fin M × Fin N).2) =
      fun ω => X ω i μ := rfl
  rw [e1, e2] at h2
  exact h2

/-- `|E ξ^k| ≤ N^{−k/2} C'_k` for `ξ = X_{iμ}`. -/
private theorem m2t_moment_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (i : Fin M) (μ : Fin N) (k : ℕ) :
    ‖∫ ω, (X ω i μ : ℂ) ^ k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have e : ∀ x : ℝ, ‖(x : ℂ) ^ k‖ = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * x| ^ k := by
    intro x
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hs, mul_pow,
      ← mul_assoc]
    have : (N : ℝ) ^ (-(k : ℝ) / 2) * Real.sqrt N ^ k = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp,
        show -(k : ℝ) / 2 + 1 / 2 * k = 0 by ring, Real.rpow_zero]
    rw [this, one_mul]
  calc ‖∫ ω, (X ω i μ : ℂ) ^ k‖ ≤ ∫ ω, ‖(X ω i μ : ℂ) ^ k‖ := norm_integral_le_integral_norm _
    _ = (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ ω, |Real.sqrt N * X ω i μ| ^ k := by
        simp_rw [e]; exact integral_const_mul _ _
    _ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 :=
        mul_le_mul_of_nonneg_left ((hX.moment k i μ).trans (le_max_left _ _)) (by positivity)

private theorem m2t_sc_mul {N : ℕ} (hN : 1 ≤ N) (n k : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) = (N : ℝ) ^ (-((n + k : ℕ) : ℝ) / 2) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [← Real.rpow_add hNp]; push_cast; ring_nf

/-- One step of (Taylo_id1) after scaling: from `b = ∑_{k ≤ 4p−n} C(n+k, n) m_k a_{n+k} + e`,
`m_0 = 1`, `|m_k| ≤ N^{−k/2} C'_k`, `C(n+k, n) C'_k ≤ L`:
`N^{−n/2}|a_n| ≤ N^{−n/2}|b| + L ∑_{k < 4p−n} N^{−(n+k+1)/2}|a_{n+k+1}| + N^{−n/2}|e|`. -/
private theorem m2t_recur_pair {N : ℕ} (hN : 1 ≤ N) {p n : ℕ} (a : ℕ → ℂ) (b e : ℂ)
    (m : ℕ → ℂ) (Cm : ℕ → ℝ) (L : ℝ)
    (hid : b = (∑ k ∈ Finset.range (4 * p - n + 1), ((n + k).choose n : ℂ) * m k * a (n + k)) + e)
    (hm0 : m 0 = 1) (hm : ∀ k, ‖m k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * Cm k)
    (hL : ∀ k, k ≤ 4 * p - n → ((n + k).choose n : ℝ) * Cm k ≤ L) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ‖b‖ +
      L * ∑ k ∈ Finset.range (4 * p - n),
        (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖ +
      (N : ℝ) ^ (-(n : ℝ) / 2) * ‖e‖ := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set sc : ℝ := (N : ℝ) ^ (-(n : ℝ) / 2) with hsc
  have hsc0 : 0 ≤ sc := Real.rpow_nonneg hNp.le _
  rw [Finset.sum_range_succ'] at hid
  simp only [add_zero, Nat.choose_self, Nat.cast_one, one_mul, hm0] at hid
  have ha : a n = b - (∑ k ∈ Finset.range (4 * p - n),
      ((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))) - e := by
    rw [hid]; ring
  have hterm : ∀ k ∈ Finset.range (4 * p - n),
      sc * ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ ≤
        L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) := by
    intro k hk
    have hk' : k + 1 ≤ 4 * p - n := Finset.mem_range.1 hk
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := hm (k + 1)
    have h2 := hL (k + 1) hk'
    have hcm : 0 ≤ Cm (k + 1) := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_right this (Real.rpow_pos_of_pos hNp _)
    have e3 : sc * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) =
        (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) := by
      rw [hsc, m2t_sc_mul hN n (k + 1), Nat.add_assoc]
    rw [show n + (k + 1) = n + k + 1 by ring]
    have hA0 : 0 ≤ ‖a (n + k + 1)‖ := norm_nonneg _
    calc sc * (((n + k + 1).choose n : ℝ) * ‖m (k + 1)‖ * ‖a (n + k + 1)‖)
        ≤ sc * (((n + k + 1).choose n : ℝ) * ((N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) * Cm (k + 1)) *
            ‖a (n + k + 1)‖) := by gcongr
      _ = (((n + k + 1).choose n : ℝ) * Cm (k + 1)) *
            ((sc * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2)) * ‖a (n + k + 1)‖) := by ring
      _ ≤ L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) := by
          rw [e3]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show n + k + 1 = n + (k + 1) by ring]; exact h2
  rw [ha]
  calc sc * ‖b - (∑ k ∈ Finset.range (4 * p - n),
        ((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))) - e‖
      ≤ sc * (‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ + ‖e‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hsc0
        exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add le_rfl (norm_sum_le _ _))) le_rfl)
    _ = sc * ‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          sc * ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ + sc * ‖e‖ := by
        rw [mul_add, mul_add, Finset.mul_sum]
    _ ≤ sc * ‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) + sc * ‖e‖ := by
        exact add_le_add (add_le_add le_rfl (Finset.sum_le_sum hterm)) le_rfl
    _ = _ := by rw [← Finset.mul_sum]

/-- The downward induction of Lemma 7.16: from
`α_n ≤ B' + L ∑_{k < 4p−n} α_{n+k+1}` for `n ∈ [3, 4p]`, `α_n ≤ (1 + 4pL)^{4p−n} B'`. -/
private theorem m2t_induct {p : ℕ} (α : ℕ → ℝ) {L B' : ℝ} (hL : 0 ≤ L) (hB' : 0 ≤ B')
    (hrec : ∀ n, 3 ≤ n → n ≤ 4 * p →
      α n ≤ B' + L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1)) :
    ∀ n, 3 ≤ n → n ≤ 4 * p → α n ≤ (1 + 4 * p * L) ^ (4 * p - n) * B' := by
  set Q : ℝ := 1 + 4 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 4 * p * L := by positivity
    linarith
  suffices H : ∀ j, ∀ n, 3 ≤ n → n ≤ 4 * p → 4 * p - n = j → α n ≤ Q ^ j * B' from
    fun n h4 hn => H _ n h4 hn rfl
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro n h4 hn hj
    have hsum : ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) ≤
        ∑ _k ∈ Finset.range (4 * p - n), Q ^ (j - 1) * B' := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      have h1 := ih (j - k - 1) (by omega) (n + k + 1) (by omega) (by omega) (by omega)
      exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ1 (by omega)) hB')
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hrn := hrec n h4 hn
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have : 4 * p - n = 0 := hj
      rw [this, Finset.sum_range_zero, mul_zero, add_zero] at hrn
      simpa using hrn
    · have hcnt : ((4 * p - n : ℕ) : ℝ) ≤ 4 * p := by
        have : 4 * p - n ≤ 4 * p := Nat.sub_le _ _
        exact_mod_cast this
      have hQj : B' ≤ Q ^ (j - 1) * B' := le_mul_of_one_le_left hB' (one_le_pow₀ hQ1)
      have hQ0 : 0 ≤ Q ^ (j - 1) * B' := by positivity
      have hpow : Q ^ j = Q ^ (j - 1) * Q := by
        rw [← pow_succ]; congr 1; omega
      calc α n ≤ B' + L * (((4 * p - n : ℕ) : ℝ) * (Q ^ (j - 1) * B')) :=
            hrn.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hL))
        _ ≤ Q ^ (j - 1) * B' + L * (4 * p * (Q ^ (j - 1) * B')) := by gcongr
        _ = Q ^ j * B' := by rw [hpow, hQ]; ring

/-- The constant `L = 2^{4p} ∑_{k ≤ 4p} C'_k` of Lemma 7.16. -/
private def m2tL (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  2 ^ (4 * p) * ∑ k ∈ Finset.range (4 * p + 1), max (C k) 0

private theorem m2tL_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ m2tL C p := by
  unfold m2tL
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => le_max_right _ _)

private theorem m2tL_ge {C : ℕ → ℝ} {p n k : ℕ} (hnk : n + k ≤ 4 * p) :
    ((n + k).choose n : ℝ) * max (C k) 0 ≤ m2tL C p := by
  unfold m2tL
  have h1 : ((n + k).choose n : ℝ) ≤ 2 ^ (4 * p) := by
    have := Nat.choose_le_two_pow (n + k) n
    have h2 : 2 ^ (n + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) hnk
    exact_mod_cast this.trans h2
  have h3 : max (C k) 0 ≤ ∑ j ∈ Finset.range (4 * p + 1), max (C j) 0 :=
    Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _)
      (Finset.mem_range.2 (by omega))
  exact mul_le_mul h1 h3 (le_max_right _ _) (by positivity)

/-- Lemma 7.16 (`lem:0_to_theta`) for `n ∈ [3, 4p]` (the replacement step of Lemma 8.2). -/
theorem zero_to_theta3 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) (hDA : dPrev p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → ∀ B : ℝ, 0 ≤ B →
          (∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖ ≤ B) →
          ∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n‖ ≤
              K * (B + (N : ℝ) ^ δ * Psi N (specOf Sig) z ^ p) := by
  have _hpEven := hp
  set L := m2tL C p with hLdef
  have hL0 : 0 ≤ L := m2tL_nonneg C p
  set Q : ℝ := 1 + 4 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 4 * p * L := by positivity
    linarith
  refine ⟨Q ^ (4 * p) * (1 + 2 * τ⁻¹), by positivity, ?_⟩
  obtain ⟨N₁, h₁⟩ := m2t_event τ c C p C₀ δ εA DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hεA hεAδ
  have h25 : 25 * δ ≤ C₀ * δ := by nlinarith
  have hδ1 : δ ≤ 1 / 100 := by nlinarith
  set K₁ : ℝ := ((4 * p + 1).factorial : ℝ) / τ ^ p with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₃ : ℝ := m2tK2 τ c p ^ 2 * m2tKW τ C (18 * p) with hK₃
  refine ⟨max (max (max N₁ 2) (max 1 ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊)) (max ⌈K₃⌉₊ ⌈τ⁻¹⌉₊), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz v hv B hB0 hB
  have hNN₁ : N₁ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hNK₃ : ⌈K₃⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hN10 : ((4 * p + 1).factorial : ℝ) ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h := m2t_le_rpow hK₁0 (by norm_num : (0 : ℝ) < 1 / 10) hNK₁
    rw [hK₁, div_le_iff₀ (by positivity)] at h
    linarith
  have hK : K₃ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK₃)
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hSig := hset.sigma.posDef
  have hD : 3 * (54 * (p : ℝ) + 1) ≤ DA - 4 := by
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    unfold dPrev at hDA
    nlinarith
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  set Ψp : ℝ := Psi N (specOf Sig) z ^ p with hΨp
  have hΨp0 : 0 ≤ Ψp := by
    have := m2t_Psi_ge (σ := specOf Sig) hN1 hτ hzD
    have : 0 ≤ Psi N (specOf Sig) z := le_trans (by positivity) this
    positivity
  set Er : ℝ := 2 * (N : ℝ) ^ (δ - 2) * Ψp with hEr
  -- the per-entry recursion
  set a : Fin M → Fin N → ℕ → ℂ := fun i μ n =>
    ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n with ha
  set b : Fin M → Fin N → ℕ → ℂ := fun i μ n =>
    ∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n with hb
  have hpair : ∀ (i : Fin M) (μ : Fin N) (n : ℕ), n ≤ 4 * p →
      (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a i μ n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er := by
    intro i μ n hn
    have hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * X ω i μ| ^ q) ∧
        ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ C q :=
      fun q => ⟨hX.integrable_moment q i μ, hX.moment q i μ⟩
    have hev := h₁ N hNN₁ M Sig S P m hset hm hA Ω X (fun ω => X ω i μ) hX hP hym z hz i μ v hv
    have hevR : HighProbAt N (DA - 4) {ω | ‖m2tRem Sig (X ω) z v i μ p n (X ω i μ)‖ ≤
        (N : ℝ) ^ ((n : ℝ) / 2 - 2) * Ψp} := by
      refine m2t_hp_mono (fun ω hω => ?_) hev
      exact m2t_rem_det (σ := specOf Sig) hp2 hτ hδ1 hεA hεAδ hN1 hN10 hzD
        (fun k x => hasDerivAt_resCoeff hSig (X ω) hzD.1 v i μ k x) (X ω i μ) hω.1
        (fun s hs => hω.2 s hs) n hn
    obtain ⟨-, hid, hR⟩ := m2t_expect hset hN1 hzS hv i μ hX (hX.measurable i μ) hym
      (m2t_indep_entry hX i μ) n hn hδ.le hD (m2t_Gamma_ge hN1 hp2 hτ hτN hzD) hK hevR
    have hb' : b i μ n = ∫ ω, fCoeff p (resCoeff Sig (Xupd (X ω) i μ (X ω i μ)) z v i μ) n := by
      simp only [hb, Xupd_self]
    have hrec := m2t_recur_pair hN1 (p := p) (n := n) (a i μ) (b i μ n)
      (∫ ω, m2tRem Sig (X ω) z v i μ p n (X ω i μ)) (fun k => ∫ ω, (X ω i μ : ℂ) ^ k)
      (fun k => max (C k) 0) L (by rw [hb', hid]) (by simp)
      (fun k => m2t_moment_entry hX hN1 i μ k) (fun k hk => m2tL_ge (by omega))
    refine hrec.trans (add_le_add le_rfl ?_)
    calc (N : ℝ) ^ (-(n : ℝ) / 2) * ‖∫ ω, m2tRem Sig (X ω) z v i μ p n (X ω i μ)‖
        ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * (2 * (N : ℝ) ^ δ * ((N : ℝ) ^ ((n : ℝ) / 2 - 2) * Ψp)) :=
          mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hNp.le _)
      _ = 2 * ((N : ℝ) ^ (-(n : ℝ) / 2) * (N : ℝ) ^ δ * (N : ℝ) ^ ((n : ℝ) / 2 - 2)) * Ψp := by
          ring
      _ = Er := by
          rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, hEr]
          congr 2
          ring_nf
  -- summed over the entries
  set α : ℕ → ℝ := fun n => (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖a i μ n‖ with hα
  have hαsum : ∀ n, α n = ∑ i, ∑ μ, (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a i μ n‖ := by
    intro n; simp only [hα, Finset.mul_sum]
  set E' : ℝ := 2 * τ⁻¹ * (N : ℝ) ^ δ * Ψp with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hMN : ∑ _i : Fin M, ∑ _μ : Fin N, Er ≤ E' := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hEr0 : 0 ≤ Er := by positivity
    have e : (N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ - 2)) = (N : ℝ) ^ δ := by
      rw [show δ = 1 + (1 + (δ - 2)) by ring, Real.rpow_add hNp, Real.rpow_add hNp,
        Real.rpow_one]
      congr 2; ring_nf
    calc (M : ℝ) * ((N : ℝ) * Er) ≤ τ⁻¹ * N * ((N : ℝ) * Er) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 2 * τ⁻¹ * ((N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ - 2))) * Ψp := by rw [hEr]; ring
      _ = E' := by rw [e]
  have hrec : ∀ n, 3 ≤ n → n ≤ 4 * p →
      α n ≤ (B + E') + L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) := by
    intro n h4 hn
    have hβ : (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖b i μ n‖ ≤ B :=
      hB n (Finset.mem_Icc.2 ⟨h4, hn⟩)
    have hs1 : α n ≤ ∑ i, ∑ μ, ((N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er) := by
      rw [hαsum]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hpair i μ n hn
    have hs2 : ∑ i, ∑ μ, ((N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er) =
        (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖b i μ n‖ +
          L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) +
          ∑ _i : Fin M, ∑ _μ : Fin N, Er := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      congr 1
      simp only [hαsum]
      exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
    linarith
  have hind := m2t_induct (p := p) α hL0 (by positivity) hrec
  intro n hn
  obtain ⟨h4, hn4⟩ := Finset.mem_Icc.1 hn
  have h1 := hind n h4 hn4
  have h2 : (1 + 4 * (p : ℝ) * L) ^ (4 * p - n) ≤ Q ^ (4 * p) :=
    pow_le_pow_right₀ hQ1 (Nat.sub_le _ _)
  have hBE : 0 ≤ B + E' := by positivity
  have h3 : B + E' ≤ (1 + 2 * τ⁻¹) * (B + (N : ℝ) ^ δ * Ψp) := by
    have : 0 ≤ (N : ℝ) ^ δ * Ψp := by positivity
    have hτ0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    rw [hE']
    nlinarith [mul_nonneg hτ0 hB0]
  calc α n ≤ (1 + 4 * (p : ℝ) * L) ^ (4 * p - n) * (B + E') := h1
    _ ≤ Q ^ (4 * p) * ((1 + 2 * τ⁻¹) * (B + (N : ℝ) ^ δ * Ψp)) :=
        mul_le_mul h2 h3 hBE (by positivity)
    _ = Q ^ (4 * p) * (1 + 2 * τ⁻¹) * (B + (N : ℝ) ^ δ * Ψp) := by ring

/-! ## Lemma 8.2 -/

private theorem m2sR_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-- `1 ≤ M` and `1 ≤ N` in the setting of §7 (from `τ ≤ M/N`). -/
private theorem m2s_N_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ N := by
  by_contra h
  have h0 : N = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

/-- `25 ≤ C₀(τ)` for `τ ∈ (0, 1]`. -/
private theorem m2s_czero_ge {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 25 ≤ czero τ := by
  unfold czero
  have h1 : (2400 : ℝ) ≤ 2400 / τ := by
    rw [le_div_iff₀ hτ]
    nlinarith
  have h2 : 2400 / τ ≤ (⌈2400 / τ⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- `D_{m−1}` of §7 is at most `D_{m−1}` of §8. -/
private theorem m2s_dPrev_le (τ : ℝ) (p : ℕ) : dPrev p ≤ dPrevTwo τ p := by
  unfold dPrevTwo
  have h0 : 0 ≤ dPrev p := by unfold dPrev; positivity
  have h1 : (1 : ℝ) ≤ (kTau τ : ℝ) + 1 := by
    have := (Nat.cast_nonneg (kTau τ) : (0 : ℝ) ≤ kTau τ)
    linarith
  nlinarith

private theorem m2s_continuous_Fv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Fv Sig A z v := by
  unfold Fv
  exact ((m2t_continuous_ent _ _).comp ((m2t_continuous_G (N := N) hSig hz).sub
    continuous_const)).norm

private theorem m2s_roughConst_ge {τ c : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) :
    1 ≤ roughConst τ c := by
  unfold roughConst
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hK : 0 ≤ mBoundConst τ * max c⁻¹ 1 := by
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    positivity
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  nlinarith

/-- (A_rough) with `η ≥ N⁻¹` and `‖XᵀX‖ ≤ ‖X‖_F²`. -/
private theorem m2s_wordA_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (k : ℕ)
    (w : Word k) :
    ‖wordA Sig A z v i μ k w‖ ≤ (roughConst τ c * N * (1 + m2tSq A)) ^ (k + 1) := by
  refine (norm_wordA_rough hset hz A v hv i μ k w).trans (pow_le_pow_left₀ ?_ ?_ _)
  · have h1 : 0 ≤ roughConst τ c :=
      zero_le_one.trans (m2s_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h2 : 0 < z.im := (hset.domain.1 hz).1
    positivity
  · have hzD := hset.domain.1 hz
    have hη : 0 < z.im := hzD.1
    have hNη := m2t_one_le_N_im (m2s_N_pos hset) hset.pos hzD
    have hR := zero_le_one.trans (m2s_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h1 : (1 + ‖Aᵀ * A‖) / z.im ≤ N * (1 + m2tSq A) := by
      rw [div_le_iff₀ hη]
      have : ‖Aᵀ * A‖ ≤ m2tSq A := m2tP_XtX_le A
      have h0 : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
      nlinarith
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hR

/-- (sc_step 2) on `[3, 4p]` with `max_{w ∈ 𝒱_v} E F_w^p`: Lemma 8.3 for `n = 3` and Lemma 7.17
for `n ∈ [4, 4p]` (where `E F_v^p ≤ max_{𝒱_v} E F_w^p`). -/
private theorem m2s_coeff (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hDA : dPrevTwo τ p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C allModels Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          0 ≤ maxFp Sig X z v p ∧
          ∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p) := by
  have h25 : 25 ≤ C₀ := (m2s_czero_ge hτ hτ1).trans hC₀
  obtain ⟨K₃, hK₃, N₃, h₃⟩ := sc_step3_three τ c C p C₀ δ DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hDA
  obtain ⟨K₄, hK₄, N₄, h₄⟩ := sc_step3' τ c C p C₀ δ (δ / 4) DA hτ hτ1 hc hp hp2 hδ h25 hC₀δ
    (by linarith) le_rfl ((m2s_dPrev_le τ p).trans hDA)
  refine ⟨K₃ + K₄, by positivity, max N₃ N₄, ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv
  have hNN₃ : N₃ ≤ N := le_trans (le_max_left _ _) hN
  have hNN₄ : N₄ ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := m2s_N_pos hset
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  set b := ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p with hb
  have hb0 : 0 ≤ b := by
    have h1 := m2t_Psi_ge (σ := specOf Sig) hN1 hset.pos (hset.domain.1 hz.1)
    have h2 : 0 ≤ Psi N (specOf Sig) z := le_trans (by have := hset.pos; positivity) h1
    exact pow_nonneg (mul_nonneg (Real.rpow_nonneg hNp.le _) h2) p
  have hbdd : BddAbove (Set.range fun w : Option (Fin N) =>
      ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p) := (Set.finite_range _).bddAbove
  have hEF : ∫ ω, Fv Sig (X ω) z v ^ p ≤ maxFp Sig X z v p := le_ciSup hbdd none
  have hEF0 : 0 ≤ ∫ ω, Fv Sig (X ω) z v ^ p :=
    integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hmF0 : 0 ≤ maxFp Sig X z v p := hEF0.trans hEF
  refine ⟨hmF0, fun n hn => ?_⟩
  obtain ⟨h3, hn4⟩ := Finset.mem_Icc.1 hn
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · have hn3 : n = 3 := by omega
    subst hn3
    have h := h₃ N hNN₃ M Sig S m hset hm hA Ω X hX z hz v hv
    simp only [Nat.cast_ofNat]
    refine h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₄) (by positivity))
  · have h := h₄ N hNN₄ M Sig S allModels m hset hm hA Ω X hX trivial z hz v hv n
      (Finset.mem_Icc.2 ⟨hge, hn4⟩)
    refine h.trans ?_
    calc K₄ * (b + ∫ ω, Fv Sig (X ω) z v ^ p) ≤ K₄ * (b + maxFp Sig X z v p) := by gcongr
      _ ≤ (K₃ + K₄) * (b + maxFp Sig X z v p) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₃) (by positivity)

/-! ## Laws of the entries and the interpolated ensembles -/

private theorem m2s_continuous_sq : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => m2tSq A := by
  unfold m2tSq
  exact continuous_finsetSum _ fun α _ => ((continuous_id.matrix_elem α.1 α.2).pow 2)

private theorem m2s_rpow_neg_half (hN : 1 ≤ N) (n : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) = ((Real.sqrt N)⁻¹) ^ n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNp.le, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  congr 1
  ring

private theorem m2s_wordA_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) (hk : k = 0) :
    ‖wordA Sig A z v i μ k w‖ = Fv Sig A z v := by
  subst hk
  rfl

private theorem m2s_M_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ M := by
  by_contra h
  have h0 : M = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

private theorem m2s_continuous_ofCoord :
    Continuous (ofCoord : (Fin M × Fin N → ℝ) → Matrix (Fin M) (Fin N) ℝ) :=
  continuous_pi fun i => continuous_pi fun μ => continuous_apply (i, μ)

/-- `X^{θ, t}_{(α)}`: the coordinate `α` of `x` replaced by `t`. -/
private theorem m2s_ofCoord_update (x : Fin M × Fin N → ℝ) (α : Fin M × Fin N) (t : ℝ) :
    ofCoord (Function.update x α t) = Xupd (ofCoord x) α.1 α.2 t := by
  funext j ν
  simp only [ofCoord, Xupd, Function.update_apply, Prod.ext_iff]

private theorem m2s_gaussLaw_prob (N : ℕ) : IsProbabilityMeasure (gaussLaw N) := by
  unfold gaussLaw
  infer_instance

private theorem m2s_entryLaw_prob {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {K : ℕ} {Y : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hY : EntryAssumption C Y)
    (β : Fin K × Fin N) : IsProbabilityMeasure (entryLaw Y β) :=
  ⟨by simp [entryLaw, Measure.map_apply (hY.measurable β.1 β.2) MeasurableSet.univ]⟩

/-- The Gaussian law `N(0, 1/N)` is the entry law of `X⁰`. -/
private theorem m2s_gaussLaw_eq (hN : 1 ≤ N) :
    gaussLaw N = entryLaw (gaussX 1 N) ((0 : Fin 1), (⟨0, hN⟩ : Fin N)) :=
  ((gaussX_isGaussianEnsemble 1 N).law 0 ⟨0, hN⟩).symm

private theorem m2s_entryLaw_sq_int {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (hN : 1 ≤ N)
    (β : Fin K × Fin N) (q : ℕ) : Integrable (fun t : ℝ => (t ^ 2) ^ q) (entryLaw Y β) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  refine (integrable_map_measure
    ((by fun_prop : Continuous fun t : ℝ => (t ^ 2) ^ q).aestronglyMeasurable)
    (hY.measurable β.1 β.2).aemeasurable).2 ?_
  have e : ∀ t : ℝ, (t ^ 2) ^ q = ((N : ℝ) ^ q)⁻¹ * |Real.sqrt N * t| ^ (2 * q) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  simp only [Function.comp_def, e]
  exact (hY.integrable_moment (2 * q) β.1 β.2).const_mul _

private theorem m2s_mix_sq_int {θ : ℝ} {ρ₀ ρ₁ : Measure ℝ} {q : ℕ}
    (h₀ : Integrable (fun t : ℝ => (t ^ 2) ^ q) ρ₀)
    (h₁ : Integrable (fun t : ℝ => (t ^ 2) ^ q) ρ₁) :
    Integrable (fun t : ℝ => (t ^ 2) ^ q) (mixMeasure θ ρ₀ ρ₁) :=
  (h₁.smul_measure ENNReal.ofReal_ne_top).add_measure (h₀.smul_measure ENNReal.ofReal_ne_top)

/-- `E (1 + ‖X‖_F²)^q < ∞` for a matrix with independent entries of laws `ν_α` with all moments. -/
private theorem m2s_integrable_pi_W {ν : Fin M × Fin N → Measure ℝ}
    [∀ β, IsProbabilityMeasure (ν β)] (h : ∀ β (q : ℕ), Integrable (fun t : ℝ => (t ^ 2) ^ q) (ν β))
    (q : ℕ) : Integrable (fun x => (1 + m2tSq (ofCoord x)) ^ q) (Measure.pi ν) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero]
    exact integrable_const _
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set cd : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcd
  have hSi : Integrable (fun x : Fin M × Fin N → ℝ => ∑ α : Fin M × Fin N, (x α ^ 2) ^ (n + 1))
      (Measure.pi ν) :=
    integrable_finsetSum _ fun α _ =>
      integrable_comp_eval (μ := ν) (i := α) (f := fun t : ℝ => (t ^ 2) ^ (n + 1)) (h α (n + 1))
  have hmeas : Measurable fun x : Fin M × Fin N → ℝ => (1 + m2tSq (ofCoord x)) ^ (n + 1) :=
    ((continuous_const.add (m2s_continuous_sq.comp m2s_continuous_ofCoord)).pow _).measurable
  refine (((integrable_const (1 : ℝ)).add (hSi.const_mul (cd ^ n))).const_mul (2 ^ n)).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by have := m2tSq_nonneg (ofCoord x); positivity)]
  have h1 := add_pow_le zero_le_one (m2tSq_nonneg (ofCoord x)) (n + 1)
  have h2 : m2tSq (ofCoord x) ^ (n + 1) ≤ cd ^ n * ∑ α : Fin M × Fin N, (x α ^ 2) ^ (n + 1) :=
    pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
  simp only [Nat.add_sub_cancel, one_pow] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := by simp only [Pi.add_apply]; gcongr

/-- `E F_v^p < ∞` for a matrix with independent entries of laws `ν_α` with all moments. -/
private theorem m2s_integrable_Fv_pi {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ}
    (hv : testNorm v = 1) {ν : Fin M × Fin N → Measure ℝ} [∀ β, IsProbabilityMeasure (ν β)]
    (h : ∀ β (q : ℕ), Integrable (fun t : ℝ => (t ^ 2) ^ q) (ν β)) (p : ℕ) :
    Integrable (fun x => Fv Sig (ofCoord x) z v ^ p) (Measure.pi ν) := by
  have hM := m2s_M_pos hset
  have hN := m2s_N_pos hset
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hmeas : Measurable fun x : Fin M × Fin N → ℝ => Fv Sig (ofCoord x) z v ^ p :=
    (((m2s_continuous_Fv hset.sigma.posDef hη v).comp m2s_continuous_ofCoord).pow _).measurable
  refine ((m2s_integrable_pi_W h p).const_mul ((roughConst τ c * N) ^ p)).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hF0 : 0 ≤ Fv Sig (ofCoord x) z v := norm_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg hF0 _), ← mul_pow]
  have hb := m2s_wordA_rough hset hz (ofCoord x) v hv ⟨0, hM⟩ ⟨0, hN⟩ 0 (fun _ => true)
  rw [m2s_wordA_zero _ _ _ _ _ _ 0 _ rfl, zero_add, pow_one] at hb
  exact pow_le_pow_left₀ (norm_nonneg _) hb p

private theorem m2s_integral_pullback {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    {f : Ω' → Ω} (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {h : Ω → ℝ}
    (hh : Measurable h) : ∫ ω', h (f ω') = ∫ ω, h ω := by
  rw [← integral_map hf.aemeasurable (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

private theorem m2s_integrable_pullback {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    {f : Ω' → Ω} (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {h : Ω → ℝ}
    (hh : Measurable h) (hi : Integrable h) : Integrable fun ω' => h (f ω') := by
  rw [← hmap] at hi
  exact (integrable_map_measure hh.aestronglyMeasurable hf.aemeasurable).1 hi

/-- The entry assumptions pass to `X ∘ f` for a measure-preserving `f`. -/
private theorem m2s_entry_transfer {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {f : Ω' → Ω}
    (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {C : ℕ → ℝ} {K : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) :
    EntryAssumption C fun ω' => X (f ω') := by
  have key : ∀ g : ℝ → ℝ, Continuous g → ∀ i μ,
      ∫ ω', g (X (f ω') i μ) = ∫ ω, g (X ω i μ) := fun g hg i μ =>
    m2s_integral_pullback hf hmap (hg.measurable.comp (hX.measurable i μ))
  have hmeasX : ∀ β : Fin K × Fin N, Measurable fun ω => X ω β.1 β.2 :=
    fun β => hX.measurable β.1 β.2
  refine ⟨fun i μ => (hX.measurable i μ).comp hf, ?_, fun i μ => ?_, fun i μ => ?_,
    fun q i μ => ?_, fun q i μ => ?_⟩
  · have hm' : ∀ β : Fin K × Fin N, AEMeasurable (fun ω' => X (f ω') β.1 β.2) ℙ :=
      fun β => ((hmeasX β).comp hf).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map hm']
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasX β).aemeasurable)).1 hX.indep
    have hg : Measurable fun ω (β : Fin K × Fin N) => X ω β.1 β.2 := measurable_pi_iff.2 hmeasX
    have e1 : (ℙ : Measure Ω').map (fun ω' (β : Fin K × Fin N) => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω (β : Fin K × Fin N) => X ω β.1 β.2) := by
      rw [← hmap, Measure.map_map hg hf]; rfl
    have e2 : ∀ β : Fin K × Fin N, (ℙ : Measure Ω').map (fun ω' => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω => X ω β.1 β.2) := fun β => by
      rw [← hmap, Measure.map_map (hmeasX β) hf]; rfl
    rw [e1, h]
    simp_rw [e2]
  · exact (key (fun t => t) continuous_id i μ).trans (hX.mean i μ)
  · exact (key (fun t => t ^ 2) (by fun_prop) i μ).trans (hX.var i μ)
  · exact m2s_integrable_pullback hf hmap
      ((by fun_prop : Continuous fun t : ℝ => |Real.sqrt N * t| ^ q).measurable.comp
        (hX.measurable i μ)) (hX.integrable_moment q i μ)
  · exact (key (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) i μ).trans_le (hX.moment q i μ)

/-! ## Lemma 7.11 and Lemma 7.10 for all `X` -/

/-- The moment-matching expansion (moment_matching) along the entry `α` of `X^θ`, with `X^θ_α`
replaced by `y ∼ ρ = law(Y_β)` independent of `X^θ`, and `|E y^n| ≤ N^{−n/2} C'_n`. -/
private theorem m2s_key (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (m : ℕ),
      CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N (momMax C) allModels Sig S C₀ δ (m - 1) (δ / 4) (dPrevTwo τ p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (K : ℕ) (ΩY : Type) [MeasureSpace ΩY]
          [IsProbabilityMeasure (ℙ : Measure ΩY)] (Y : ΩY → Matrix (Fin K) (Fin N) ℝ)
          (β : Fin K × Fin N), EntryAssumption (momMax C) Y →
          ∀ α : Fin M × Fin N,
          ‖(∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (entryLaw Y β)))
                - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
                    + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                      α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ ≤
            2 * (N : ℝ) ^ (δ - 2) * Psi N (specOf Sig) z ^ p +
              ∑ n ∈ Finset.Icc 3 (4 * p),
                ‖∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n
                    ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
                  ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) := by
  obtain ⟨N₁, h₁⟩ := moment_matching3 τ c (momMax C) p C₀ δ (δ / 4) (dPrevTwo τ p) hτ hτ1 hc hp
    hp2 hδ ((m2s_czero_ge hτ hτ1).trans hC₀) hC₀δ (by linarith) le_rfl (m2s_dPrev_le τ p)
  refine ⟨max N₁ 1, ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv θ hθ K ΩY _ _ Y β hY α
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hzS : z ∈ S := hz.1
  have hη : 0 < z.im := (hset.domain.1 hzS).1
  have hSig := hset.sigma.posDef
  have : IsProbabilityMeasure (gaussLaw N) := m2s_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) β) :=
    fun _ => m2s_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (entryLaw X β) := m2s_entryLaw_prob hX
  have : IsProbabilityMeasure (entryLaw Y β) := m2s_entryLaw_prob hY β
  have hmixP : ∀ β : Fin M × Fin N,
      IsProbabilityMeasure (mixMeasure θ (gaussLaw N) (entryLaw X β)) :=
    fun β => isProbabilityMeasure_mixMeasure _ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X))) := hIP
  have : IsProbabilityMeasure (ℙ : Measure (PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X) (entryLaw Y β))) := by
    change IsProbabilityMeasure ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod
      (entryLaw Y β))
    infer_instance
  -- the interpolated ensemble and the pair `(X^θ, y)`
  have hX₀ : EntryAssumption (momMax C)
      (Ω := InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord :=
    (entryAssumption_interp hX hN1 hθ.1 hθ.2).mono fun q => by
      unfold momMax; exact max_le le_rfl (le_max_right _ _)
  have hfst : Measurable fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β) => (Prod.fst ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
        (entryLaw X)) := measurable_fst
  have hmapfst : (ℙ : Measure (PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β))).map (fun ω => (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
        (fun _ => gaussLaw N) (entryLaw X))) =
      (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X))) := by
    change ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)).map Prod.fst =
      interpLaw θ (fun _ => gaussLaw N) (entryLaw X)
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hX' := m2s_entry_transfer hfst hmapfst hX₀
  have hind : IndepFun (fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β) => ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
        (fun _ => gaussLaw N) (entryLaw X))) (fun ω => Prod.snd ω) := by
    have h : IndepFun (Prod.fst : (Fin M × Fin N → ℝ) × ℝ → _) Prod.snd
        ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
        measurable_snd.aemeasurable]
      simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
        measure_univ, one_smul]
    exact h.comp m2s_continuous_ofCoord.measurable measurable_id
  -- integrals of functions of `y`
  have hy : ∀ g : ℝ → ℝ, Continuous g →
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        g (Prod.snd ω) = ∫ ω, g (Y ω β.1 β.2) := by
    intro g hg
    change ∫ q, g q.2 ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) = _
    rw [integral_fun_snd, probReal_univ, one_smul]
    exact integral_map (hY.measurable β.1 β.2).aemeasurable hg.aestronglyMeasurable
  have hyi : ∀ g : ℝ → ℝ, Continuous g → Integrable (fun ω => g (Y ω β.1 β.2)) →
      Integrable fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
        (entryLaw Y β) => g (Prod.snd ω) := by
    intro g hg hi
    change Integrable (fun q => g q.2)
      ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β))
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (hY.measurable β.1 β.2).aemeasurable).2 hi).comp_snd _
  have hy1 := (hy (fun t => t) continuous_id).trans (hY.mean β.1 β.2)
  have hy2 := (hy (fun t => t ^ 2) (by fun_prop)).trans (hY.var β.1 β.2)
  have hym : ∀ q : ℕ, Integrable (fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X) (entryLaw Y β) => |Real.sqrt N * Prod.snd ω| ^ q) ∧
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        |Real.sqrt N * Prod.snd ω| ^ q ≤ momMax C q := fun q =>
    ⟨hyi (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) (hY.integrable_moment q β.1 β.2),
      (hy (fun t => |Real.sqrt N * t| ^ q) (by fun_prop)).trans_le (hY.moment q β.1 β.2)⟩
  have hmm := h₁ N hNN₁ M Sig S allModels m hset hm hA _ _ _ hX' trivial hind measurable_snd hy1
    hy2 hym z hz α.1 α.2 v hv
  -- the three identifications
  have hFm : Measurable fun x : Fin M × Fin N → ℝ => Fv Sig (ofCoord x) z v ^ p :=
    (((m2s_continuous_Fv hSig hη v).comp m2s_continuous_ofCoord).pow _).measurable
  have hFi : Integrable (fun x : Fin M × Fin N → ℝ => Fv Sig (ofCoord x) z v ^ p)
      (interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (entryLaw Y β)) := by
    have : ∀ β' : Fin M × Fin N, IsProbabilityMeasure (Function.update
        (fun β => mixMeasure θ (gaussLaw N) (entryLaw X β)) α (entryLaw Y β) β') := fun β' => by
      by_cases h : β' = α
      · subst h; simpa using m2s_entryLaw_prob hY β
      · simpa [Function.update_of_ne h] using hmixP β'
    refine m2s_integrable_Fv_pi hset hzS hv (fun β' q => ?_) p
    by_cases h : β' = α
    · subst h; simpa using m2s_entryLaw_sq_int hY hN1 β q
    · simp only [Function.update_of_ne h]
      refine m2s_mix_sq_int ?_ (m2s_entryLaw_sq_int hX hN1 β' q)
      rw [m2s_gaussLaw_eq hN1]
      exact m2s_entryLaw_sq_int ((gaussX_isGaussianEnsemble 1 N).entryAssumption hN1) hN1 _ q
  have hE : ∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
        (entryLaw X) α (entryLaw Y β)) =
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        (Fv Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
          (entryLaw X))) α.1 α.2 (Prod.snd ω)) z v : ℂ) ^ p := by
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, integral_complex_ofReal]
    congr 1
    rw [integral_interpLawAt_eq α (entryLaw Y β) hFm hFi]
    change _ = ∫ q, _ ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β))
    simp only [m2s_ofCoord_update]
  have hfst_int : ∀ g : (Fin M × Fin N → ℝ) → ℂ,
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        g (Prod.fst ω) = ∫ x, g x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    intro g
    change ∫ q, g q.1 ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) = _
    rw [integral_fun_fst, probReal_univ, one_smul]
  have hA' : ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
        + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
          α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) =
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        (fCoeff p (resCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z v α.1 α.2) 0
        + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace
          (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z v α.1 α.2) 2) := by
    rw [hfst_int (fun x => fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) 0
      + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) 2)]
    simp only [m2s_ofCoord_update]
  have hIn : ∀ n : ℕ,
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        fCoeff p (resCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z v α.1 α.2) n =
      ∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n
        ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := fun n =>
    hfst_int (fun x => fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hYn : ∀ n : ℕ,
      ‖∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        ((Prod.snd ω : ℝ) : ℂ) ^ n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n := by
    intro n
    have e : ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
        (entryLaw Y β), ((Prod.snd ω : ℝ) : ℂ) ^ n =
        ((∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Prod.snd ω : ℝ) ^ n : ℝ) : ℂ) := by
      simp_rw [← Complex.ofReal_pow]
      exact integral_complex_ofReal
    rw [e, Complex.norm_real, Real.norm_eq_abs, m2s_rpow_neg_half hN1]
    calc |∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Prod.snd ω : ℝ) ^ n|
        ≤ ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), |(Prod.snd ω : ℝ) ^ n| := abs_integral_le_integral_abs
      _ = ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Real.sqrt N)⁻¹ ^ n * |Real.sqrt N * Prod.snd ω| ^ n := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only
          rw [abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne',
            one_pow, one_mul, abs_pow]
      _ = (Real.sqrt N)⁻¹ ^ n * ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
          (entryLaw X) (entryLaw Y β), |Real.sqrt N * Prod.snd ω| ^ n := integral_const_mul _ _
      _ ≤ (Real.sqrt N)⁻¹ ^ n * momMax C n :=
          mul_le_mul_of_nonneg_left (hym n).2 (by positivity)
  rw [hE, hA']
  set Sn := ∑ n ∈ Finset.Icc 3 (4 * p),
      (∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        fCoeff p (resCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z v α.1 α.2) n) *
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        ((Prod.snd ω : ℝ) : ℂ) ^ n with hSn
  calc _ = ‖(_ - _ - Sn) + Sn‖ := by rw [sub_add_cancel]
    _ ≤ ‖_ - _ - Sn‖ + ‖Sn‖ := norm_add_le _ _
    _ ≤ _ := by
        refine add_le_add hmm ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, hIn n]
        exact mul_le_mul_of_nonneg_left (hYn n) (norm_nonneg _)

/-- Lemma 7.11 (`lem:main_comparison2`) for all `X` (the `n = 3` term included), `u ∈ {0, 1}`. -/
theorem main_comparison2_gen (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N (momMax C) allModels Sig S C₀ δ (m - 1) (δ / 4) (dPrevTwo τ p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ u : Bool,
          ‖∑ α : Fin M × Fin N,
              ((∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (if u then entryLaw X α else gaussLaw N)))
                - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
                    + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                      α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)))‖ ≤
            Cstar * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
              ⨆ w : Option (Fin N), ∫ x, Fv Sig (ofCoord x) z (vfam v w) ^ p
                ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)))
  := by
  have h25 : 25 ≤ C₀ := (m2s_czero_ge hτ hτ1).trans hC₀
  obtain ⟨N₁, h₁⟩ := m2s_key τ c C p C₀ δ hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ
  obtain ⟨K₂, hK₂, N₂, h₂⟩ := zero_to_theta3 τ c (momMax C) p C₀ δ (δ / 4) (dPrevTwo τ p) hτ hτ1
    hc hp hp2 hδ h25 hC₀δ (by linarith) le_rfl (m2s_dPrev_le τ p)
  obtain ⟨K₃, hK₃, N₃, h₃⟩ := m2s_coeff τ c (momMax C) p C₀ δ (dPrevTwo τ p) hτ hτ1 hc hp hp2
    hδ hC₀ hC₀δ le_rfl
  have hmom0 : ∀ n, 0 ≤ momMax C n := fun n =>
    le_trans (by unfold gaussMoment; exact integral_nonneg fun x => by positivity)
      (le_max_right _ _)
  set SC : ℝ := ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n with hSC
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg fun n _ => hmom0 n
  refine ⟨2 * τ⁻¹ + SC * K₂ * (K₃ + 1), by have := hτ.le; positivity,
    max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv θ hθ u
  have hN1 : 1 ≤ N := by omega
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNN₃ : N₃ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzS : z ∈ S := hz.1
  have : IsProbabilityMeasure (gaussLaw N) := m2s_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) β) :=
    fun _ => m2s_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (entryLaw X β) := m2s_entryLaw_prob hX
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (mixMeasure θ (gaussLaw N) (entryLaw X β)) :=
    fun β => isProbabilityMeasure_mixMeasure _ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X))) := hIP
  have hX₀ : EntryAssumption (momMax C)
      (Ω := InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord :=
    (entryAssumption_interp hX hN1 hθ.1 hθ.2).mono fun q => by
      unfold momMax; exact max_le le_rfl (le_max_right _ _)
  set Ψ := Psi N (specOf Sig) z with hΨ
  have hΨ0 : 0 ≤ Ψ := le_trans (by have := hset.pos; positivity)
    (m2t_Psi_ge (σ := specOf Sig) hN1 hset.pos (hset.domain.1 hzS))
  set b := ((N : ℝ) ^ (C₀ * δ) * Ψ) ^ p with hb
  set EF := ⨆ w : Option (Fin N), ∫ x, Fv Sig (ofCoord x) z (vfam v w) ^ p
    ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) with hEF
  have hb0 : 0 ≤ b := pow_nonneg (mul_nonneg (Real.rpow_nonneg hNp.le _) hΨ0) p
  obtain ⟨hEF0, hB⟩ := h₃ N hNN₃ M Sig S m hset hm hA
    (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord hX₀ z hz v hv
  have hEF0' : 0 ≤ EF := hEF0
  have hZ := h₂ N hNN₂ M Sig S allModels m hset hm hA
    (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord hX₀ trivial z hz
    v hv (K₃ * (b + EF)) (by positivity) hB
  have hG : EntryAssumption (momMax C) (gaussX 1 N) :=
    ((gaussX_isGaussianEnsemble 1 N).entryAssumption hN1).mono fun q => le_max_right _ _
  have hkey : ∀ α : Fin M × Fin N,
      ‖(∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (if u then entryLaw X α else gaussLaw N)))
                - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
                    + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                      α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ ≤
            2 * (N : ℝ) ^ (δ - 2) * Ψ ^ p +
              ∑ n ∈ Finset.Icc 3 (4 * p),
                ‖∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n
                    ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
                  ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) := by
    intro α
    cases u
    · have := h₁ N hNN₁ M Sig S m hset hm hA Ω X hX z hz v hv θ hθ 1 (GaussSpace 1 N)
        (gaussX 1 N) ((0 : Fin 1), (⟨0, hN1⟩ : Fin N)) hG α
      rw [← m2s_gaussLaw_eq hN1] at this
      simpa only [Bool.false_eq_true, ↓reduceIte] using this
    · simpa only [↓reduceIte] using
        h₁ N hNN₁ M Sig S m hset hm hA Ω X hX z hz v hv θ hθ M Ω X α hX α
  have hsplit : ∑ α : Fin M × Fin N, ∑ n ∈ Finset.Icc 3 (4 * p),
      ‖∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n
          ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
        ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) =
      ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
        ∑ i, ∑ μ, ‖∫ ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X),
          fCoeff p (resCoeff Sig (Xupd (ofCoord ω) i μ 0) z v i μ) n‖) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    change _ = momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) i μ 0) z v i μ) n
        ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖)
    ring
  have hMN : (M : ℝ) * N * (N : ℝ) ^ (δ - 2) ≤ τ⁻¹ * (N : ℝ) ^ δ := by
    have hM : (M : ℝ) ≤ τ⁻¹ * N := by
      have := hset.ratio_le
      rwa [div_le_iff₀ hNp] at this
    have e : (N : ℝ) ^ (δ - 2) = (N : ℝ) ^ δ / (N : ℝ) ^ 2 := by
      rw [Real.rpow_sub hNp, Real.rpow_two]
    rw [e]
    have hNd : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hNp.le _
    calc (M : ℝ) * N * ((N : ℝ) ^ δ / (N : ℝ) ^ 2) = (M : ℝ) * ((N : ℝ) ^ δ / N) := by
          field_simp
      _ ≤ τ⁻¹ * N * ((N : ℝ) ^ δ / N) := mul_le_mul_of_nonneg_right hM (by positivity)
      _ = τ⁻¹ * (N : ℝ) ^ δ := by field_simp
  have hNδ : (N : ℝ) ^ δ * Ψ ^ p ≤ b := by
    rw [hb, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hΨ0 p)
    calc (N : ℝ) ^ δ ≤ (N : ℝ) ^ (C₀ * δ) := Real.rpow_le_rpow_of_exponent_le hN1r (by nlinarith)
      _ ≤ ((N : ℝ) ^ (C₀ * δ)) ^ p :=
          le_self_pow₀ (Real.one_le_rpow hN1r (by nlinarith)) (by omega)
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  calc _ ≤ ∑ α : Fin M × Fin N, ‖(∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p
              ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α
                (if u then entryLaw X α else gaussLaw N)))
            - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
                + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                  α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α : Fin M × Fin N, (2 * (N : ℝ) ^ (δ - 2) * Ψ ^ p +
              ∑ n ∈ Finset.Icc 3 (4 * p),
                ‖∫ x, fCoeff p (resCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z v α.1 α.2) n
                    ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
                  ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n)) :=
        Finset.sum_le_sum fun α _ => hkey α
    _ = (M : ℝ) * N * (2 * (N : ℝ) ^ (δ - 2) * Ψ ^ p) +
          ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X),
              fCoeff p (resCoeff Sig (Xupd (ofCoord ω) i μ 0) z v i μ) n‖) := by
        rw [Finset.sum_add_distrib, hsplit, Finset.sum_const, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * (τ⁻¹ * (N : ℝ) ^ δ) * Ψ ^ p +
          ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n *
            (K₂ * (K₃ * (b + EF) + (N : ℝ) ^ δ * Ψ ^ p)) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (hZ n hn) (hmom0 n))
        have := mul_le_mul_of_nonneg_right hMN (by positivity : (0 : ℝ) ≤ 2 * Ψ ^ p)
        linarith
    _ = 2 * τ⁻¹ * ((N : ℝ) ^ δ * Ψ ^ p) +
          SC * K₂ * (K₃ * (b + EF) + (N : ℝ) ^ δ * Ψ ^ p) := by
        rw [hSC, Finset.sum_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ 2 * τ⁻¹ * b + SC * K₂ * (K₃ * (b + EF) + b) := by gcongr
    _ ≤ (2 * τ⁻¹ + SC * K₂ * (K₃ + 1)) * (b + EF) := by
        have h1 : 0 ≤ (2 * τ⁻¹ + SC * K₂) * EF := by positivity
        nlinarith

/-- Lemma 7.10 (`lem:main_comparison`) for all `X`, with `max_{w ∈ 𝒱_v} E F_w^p(X^θ)`. -/
theorem main_comparison_gen (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N (momMax C) allModels Sig S C₀ δ (m - 1) (δ / 4) (dPrevTwo τ p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          |∑ α : Fin M × Fin N,
              ((∫ x, Fv Sig (ofCoord x) z v ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (entryLaw X α)))
                - ∫ x, Fv Sig (ofCoord x) z v ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (gaussLaw N)))| ≤
            Cstar * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
              ⨆ w : Option (Fin N), ∫ x, Fv Sig (ofCoord x) z (vfam v w) ^ p
                ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)))
  := by
  obtain ⟨Cs, hCs, N₀, h⟩ := main_comparison2_gen τ c C p C₀ δ hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ
  refine ⟨2 * Cs, by positivity, N₀, ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv θ hθ
  have h1 := h N hN M Sig S m hset hm hA Ω X hX z hz v hv θ hθ true
  have h0 := h N hN M Sig S m hset hm hA Ω X hX z hz v hv θ hθ false
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h0
  have hc : ∀ ν : Measure (Fin M × Fin N → ℝ),
      ∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ p ∂ν =
        ((∫ x, Fv Sig (ofCoord x) z v ^ p ∂ν : ℝ) : ℂ) := by
    intro ν
    simp_rw [← Complex.ofReal_pow]
    exact integral_complex_ofReal
  simp only [hc] at h1 h0
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  calc _ = ‖(∑ α : Fin M × Fin N,
          (((∫ x, Fv Sig (ofCoord x) z v ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
            (entryLaw X) α (entryLaw X α)) : ℝ) : ℂ)
          - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
              + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))))
        - ∑ α : Fin M × Fin N,
          (((∫ x, Fv Sig (ofCoord x) z v ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
            (entryLaw X) α (gaussLaw N)) : ℝ) : ℂ)
          - ∫ x, (fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
              + (N : ℂ)⁻¹ * fCoeff p (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)))‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun α _ => ?_
        ring
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-! ## Lemma 7.5 for all `X`: Grönwall over `𝒱_v` -/

/-- The moment conditions of the entry assumptions for the law of one entry. -/
private theorem m2m_entryLaw_props {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N) :
    (∫ t, t ∂(entryLaw Y β) = 0) ∧ (∫ t, t ^ 2 ∂(entryLaw Y β) = 1 / (N : ℝ)) ∧
      (∀ q : ℕ, Integrable (fun t : ℝ => |Real.sqrt N * t| ^ q) (entryLaw Y β)) ∧
      (∀ q : ℕ, ∫ t, |Real.sqrt N * t| ^ q ∂(entryLaw Y β) ≤ C q) := by
  have hm : AEMeasurable (fun ω => Y ω β.1 β.2) (ℙ : Measure Ω) :=
    (hY.measurable β.1 β.2).aemeasurable
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∫ t, f t ∂(entryLaw Y β) = ∫ ω, f (Y ω β.1 β.2) :=
    fun f hf => integral_map hm hf.aestronglyMeasurable
  refine ⟨(key (fun t => t) continuous_id).trans (hY.mean _ _),
    (key (fun t => t ^ 2) (by fun_prop)).trans (hY.var _ _), fun q => ?_,
    fun q => (key (fun t => |Real.sqrt N * t| ^ q) (by fun_prop)).trans_le (hY.moment q _ _)⟩
  exact (integrable_map_measure
    ((by fun_prop : Continuous fun t : ℝ => |Real.sqrt N * t| ^ q).aestronglyMeasurable) hm).2
    (hY.integrable_moment q _ _)

/-- At `θ = 1` the interpolating law between `ν` and itself is `∏_α ν_α`. -/
private theorem m2m_interpLaw_one (ν : Fin M × Fin N → Measure ℝ) :
    interpLaw 1 ν ν = Measure.pi ν := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

/-- The coordinate matrix under `∏_α ν_α` satisfies the entry assumptions with moment function
`C` when every `ν_α` satisfies them. -/
private theorem m2m_entryAssumption_pi {C : ℕ → ℝ} (ν : Fin M × Fin N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)]
    (h : ∀ α, (∫ t, t ∂(ν α) = 0) ∧ (∫ t, t ^ 2 ∂(ν α) = 1 / (N : ℝ)) ∧
      (∀ q : ℕ, Integrable (fun t : ℝ => |Real.sqrt N * t| ^ q) (ν α)) ∧
      (∀ q : ℕ, ∫ t, |Real.sqrt N * t| ^ q ∂(ν α) ≤ C q)) :
    EntryAssumption C (Ω := InterpSpace (Fin M × Fin N) 1 ν ν) ofCoord := by
  have hP : (ℙ : Measure (InterpSpace (Fin M × Fin N) 1 ν ν)) = Measure.pi ν :=
    m2m_interpLaw_one ν
  have key : ∀ (i : Fin M) (μ : Fin N) (f : ℝ → ℝ), Continuous f →
      ∫ ω : InterpSpace (Fin M × Fin N) 1 ν ν, f (ofCoord ω i μ) = ∫ t, f t ∂(ν (i, μ)) := by
    intro i μ f hf
    rw [hP]
    exact integral_comp_eval (μ := ν) (i := (i, μ)) hf.aestronglyMeasurable
  refine ⟨fun i μ => measurable_pi_apply (X := fun _ : Fin M × Fin N => ℝ) (i, μ), ?_,
    fun i μ => (key i μ (fun t => t) continuous_id).trans (h (i, μ)).1,
    fun i μ => (key i μ (fun t => t ^ 2) (by fun_prop)).trans (h (i, μ)).2.1,
    fun q i μ => ?_,
    fun q i μ => (key i μ (fun t => |Real.sqrt N * t| ^ q) (by fun_prop)).trans_le
      ((h (i, μ)).2.2.2 q)⟩
  · rw [hP]
    exact iIndepFun_pi (μ := ν) (X := fun _ x => x) fun _ => aemeasurable_id
  · rw [hP]
    exact integrable_comp_eval (μ := ν) (i := (i, μ))
      (f := fun t : ℝ => |Real.sqrt N * t| ^ q) ((h (i, μ)).2.2.1 q)

/-- `F_v^p ∘ ofCoord` is integrable under every vertex law `∏_α ρ^{u_α}_α` of the interpolation
between `X⁰` and `X` (the expectations in (interpol) of Lemma 7.9 exist), for `z ∈ S`,
`|v| = 1`. -/
private theorem m2m_integrable_vertex (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting τ c M N Sig S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ S, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → ∀ u : Fin M × Fin N → Bool,
          Integrable (fun x => Fv Sig (ofCoord x) z v ^ p)
            (vertexLaw (fun _ => gaussLaw N) (entryLaw X) u) := by
  obtain ⟨N₁, h₁⟩ := integral_Fv_pow_le τ c (momMax C) p hτ hτ1 hc
  refine ⟨max N₁ 1, fun N hN M Sig S hset Ω _ _ X hX z hz v hv u => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨ν, hν⟩ : ∃ ν : Fin M × Fin N → Measure ℝ,
      ν = fun α => if u α then entryLaw X α else gaussLaw N := ⟨_, rfl⟩
  have hG : EntryAssumption (momMax C) (gaussX M N) :=
    ((gaussX_isGaussianEnsemble M N).entryAssumption hN1).mono fun q => le_max_right _ _
  have hlaw : ∀ α : Fin M × Fin N, gaussLaw N = entryLaw (gaussX M N) α := fun α =>
    ((gaussX_isGaussianEnsemble M N).law α.1 α.2).symm
  have hprob : ∀ α, IsProbabilityMeasure (ν α) := by
    intro α
    rw [hν]
    by_cases h : u α
    · simp only [h, ite_true]
      exact ⟨by simp [entryLaw, Measure.map_apply (hX.measurable α.1 α.2) MeasurableSet.univ]⟩
    · simp only [h, Bool.false_eq_true, ite_false]
      unfold gaussLaw
      infer_instance
  have hprops : ∀ α, (∫ t, t ∂(ν α) = 0) ∧ (∫ t, t ^ 2 ∂(ν α) = 1 / (N : ℝ)) ∧
      (∀ q : ℕ, Integrable (fun t : ℝ => |Real.sqrt N * t| ^ q) (ν α)) ∧
      (∀ q : ℕ, ∫ t, |Real.sqrt N * t| ^ q ∂(ν α) ≤ momMax C q) := by
    intro α
    rw [hν]
    by_cases h : u α
    · simp only [h, ite_true]
      exact m2m_entryLaw_props hX α
    · simp only [h, Bool.false_eq_true, ite_false]
      rw [hlaw α]
      exact m2m_entryLaw_props hG α
  have hE := m2m_entryAssumption_pi ν hprops
  have hIP : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) 1 ν ν)) := by
    change IsProbabilityMeasure (interpLaw 1 ν ν)
    rw [m2m_interpLaw_one]
    infer_instance
  have hmod : IsModel τ (momMax C) M N Sig (Ω := InterpSpace (Fin M × Fin N) 1 ν ν) ofCoord :=
    ⟨hset.ratio_ge, hset.ratio_le, hE, hset.sigma⟩
  have hi := (h₁ N hNN₁ (Ω := InterpSpace (Fin M × Fin N) 1 ν ν) M Sig ofCoord S hmod
    hset.domain hset.oneXm z hz v hv).1
  have e : vertexLaw (fun _ => gaussLaw N) (entryLaw X) u = interpLaw 1 ν ν := by
    rw [m2m_interpLaw_one, hν]
    rfl
  rw [e]
  exact hi

/-- `Q ≤ N^a` once `⌈Q^{1/a}⌉ ≤ N`. -/
private theorem m2m_le_rpow {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

/-- Lemma 7.5 (`lem:moment_bound_1`) for all `X`, through Grönwall over `𝒱_v`. -/
theorem moment_bound_gen (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ Kp : ℝ, 0 < Kp ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      AnisotropicLawAt N δ (gaussD p) Sig (gaussX M N) S →
      PropA N (momMax C) allModels Sig S C₀ δ (m - 1) (δ / 4) (dPrevTwo τ p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          Integrable (fun ω => Fv Sig (X ω) z v ^ p) ∧
            ∫ ω, Fv Sig (X ω) z v ^ p ≤ Kp * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p := by
  have h25 : 25 ≤ C₀ := (m2s_czero_ge hτ hτ1).trans hC₀
  obtain ⟨Cs, hCs, N₁, h₁⟩ := main_comparison_gen τ c C p C₀ δ hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ
  obtain ⟨N₂, h₂⟩ := comparison_zero τ c p hτ hτ1 hc
  obtain ⟨N₃, h₃⟩ := integral_Fv_pow_le τ c (momMax C) p hτ hτ1 hc
  obtain ⟨N₄, h₄⟩ := m2m_integrable_vertex τ c C p hτ hτ1 hc
  refine ⟨2 * Real.exp Cs, by positivity,
    max (max (max N₁ N₂) (max N₃ N₄)) (max ⌈(2 : ℝ) ^ δ⁻¹⌉₊ 1), ?_⟩
  intro N hN M Sig S m hset hm hgauss hA Ω _ _ X hX z hz v hv
  have hN1 : 1 ≤ N := by omega
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNN₃ : N₃ ≤ N := by omega
  have hNN₄ : N₄ ≤ N := by omega
  have hN2δ : ⌈(2 : ℝ) ^ δ⁻¹⌉₊ ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hzS : z ∈ S := hz.1
  have hzim : 0 < z.im := (hset.domain.1 hzS).1
  have hmodX : IsModel τ (momMax C) M N Sig X := ⟨hset.ratio_ge, hset.ratio_le, hX, hset.sigma⟩
  obtain ⟨hintX, -⟩ := h₃ N hNN₃ M Sig X S hmodX hset.domain hset.oneXm z hzS v hv
  refine ⟨hintX, ?_⟩
  have hg : IsProbabilityMeasure (gaussLaw N) := by
    unfold gaussLaw
    infer_instance
  have : ∀ α : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) α) := fun _ => hg
  have : ∀ α, IsProbabilityMeasure (entryLaw X α) := fun α =>
    ⟨by simp [entryLaw, Measure.map_apply (hX.measurable α.1 α.2) MeasurableSet.univ]⟩
  have hΨ : 0 < Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
    linarith [Real.sqrt_nonneg ((mFun N (specOf Sig) z).im / (N * z.im))]
  set a : ℝ := ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p with ha
  have hb0 : 0 ≤ (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) hΨ.le
  have ha0 : 0 ≤ a := pow_nonneg hb0 p
  -- the family `𝒱_v` and the functions `Φ_w(θ) = E F_w^p(X^θ)`
  have hvw : ∀ w : Option (Fin N), testNorm (vfam v w) = 1 := by
    intro w
    cases w with
    | none => exact hv
    | some μ => exact m2sR_testNorm_eI (Sum.inr μ)
  set F : Option (Fin N) → (Fin M × Fin N → ℝ) → ℝ :=
    fun w x => Fv Sig (ofCoord x) z (vfam v w) ^ p with hFdef
  have hFm : ∀ w, Measurable (F w) := fun w =>
    (((m2s_continuous_Fv hset.sigma.posDef hzim (vfam v w)).comp
      m2s_continuous_ofCoord).pow _).measurable
  have hint : ∀ w u, Integrable (F w) (vertexLaw (fun _ => gaussLaw N) (entryLaw X) u) :=
    fun w => h₄ N hNN₄ M Sig S hset Ω X hX z hzS (vfam v w) (hvw w)
  set cl : ℝ → ℝ := fun θ => max (-1) (min θ 2) with hcl
  set Φ : Option (Fin N) → ℝ → ℝ :=
    fun w θ => interpPoly (fun _ => gaussLaw N) (entryLaw X) (F w) (cl θ) with hΦ
  set Φ' : Option (Fin N) → ℝ → ℝ := fun w θ => ∑ α : Fin M × Fin N,
      ((∫ x, F w x ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (entryLaw X α)))
        - ∫ x, F w x ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (gaussLaw N)))
    with hΦ'
  have hcl01 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, cl θ = θ := fun θ hθ => by
    simp only [hcl]
    rw [min_eq_left (by linarith [hθ.2]), max_eq_right (by linarith [hθ.1])]
  have hΦeq : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      Φ w θ = ∫ x, F w x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    intro w θ hθ
    simp only [hΦ, hcl01 θ hθ]
    exact (integral_interpLaw_eq_interpPoly hθ.1 hθ.2 (hFm w) (hint w)).symm
  -- `Φ_w` is bounded on `ℝ` (the weight is clamped to `[−1, 2]`)
  set B : ℝ := ∑ w : Option (Fin N), ∑ u : Fin M × Fin N → Bool,
      2 ^ Fintype.card (Fin M × Fin N) *
        |∫ x, F w x ∂(vertexLaw (fun _ => gaussLaw N) (entryLaw X) u)| with hBdef
  have hB : ∀ w θ, |Φ w θ| ≤ B := by
    intro w θ
    have hc1 : -1 ≤ cl θ := le_max_left _ _
    have hc2 : cl θ ≤ 2 := max_le (by norm_num) (min_le_right _ _)
    have hfac : ∀ (u : Fin M × Fin N → Bool) (α : Fin M × Fin N),
        |if u α then cl θ else 1 - cl θ| ≤ 2 := by
      intro u α
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    have hprod : ∀ u : Fin M × Fin N → Bool,
        |∏ α, (if u α then cl θ else 1 - cl θ)| ≤ 2 ^ Fintype.card (Fin M × Fin N) := by
      intro u
      rw [Finset.abs_prod]
      calc ∏ α, |if u α then cl θ else 1 - cl θ| ≤ ∏ _α : Fin M × Fin N, (2 : ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun α _ => hfac u α
        _ = 2 ^ Fintype.card (Fin M × Fin N) := by rw [Finset.prod_const, Finset.card_univ]
    have h1 : |Φ w θ| ≤ ∑ u : Fin M × Fin N → Bool, 2 ^ Fintype.card (Fin M × Fin N) *
        |∫ x, F w x ∂(vertexLaw (fun _ => gaussLaw N) (entryLaw X) u)| := by
      simp only [hΦ, interpPoly]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hprod u) (abs_nonneg _)
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun w => ∑ u : Fin M × Fin N → Bool,
      2 ^ Fintype.card (Fin M × Fin N) *
        |∫ x, F w x ∂(vertexLaw (fun _ => gaussLaw N) (entryLaw X) u)|)
      (fun w _ => Finset.sum_nonneg fun u _ => by positivity) (Finset.mem_univ w)
  -- the derivative on `[0, 1]` (Remark 7.18)
  have hderiv : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Φ w) (Φ' w θ) θ := by
    intro w θ hθ
    have h := hasDerivAt_interpPoly hθ.1 hθ.2 (hFm w) (hint w)
    refine h.congr_of_eventuallyEq ?_
    have hmem : Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 θ :=
      Ioo_mem_nhds (by linarith [hθ.1]) (by linarith [hθ.2])
    filter_upwards [hmem] with t ht
    simp only [hΦ, hcl]
    rw [min_eq_left ht.2.le, max_eq_right ht.1.le]
  -- Lemma 7.10 at `w ∈ 𝒱_v`, and `𝒱_w ⊆ 𝒱_v`
  have hbdd : ∀ θ, BddAbove (Set.range fun w' : Option (Fin N) => Φ w' θ) := fun θ =>
    (Set.finite_range _).bddAbove
  have hbound : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ' w θ| ≤ Cs * (a + ⨆ w', Φ w' θ) := by
    intro w θ hθ
    have hmc := h₁ N hNN₁ M Sig S m hset hm hA Ω X hX z hz (vfam v w) (hvw w) θ hθ
    refine hmc.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hCs)
    refine ciSup_le fun u => ?_
    obtain ⟨u', hu'⟩ := vfam_closed v w u
    calc ∫ x, Fv Sig (ofCoord x) z (vfam (vfam v w) u) ^ p
          ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) = Φ u' θ := by
          rw [hu', hΦeq u' θ hθ]
      _ ≤ ⨆ w', Φ w' θ := le_ciSup (hbdd θ) u'
  -- `Φ_w(0) = E F_w^p(X⁰) ≤ (N^{C₀δ} Ψ)^p` (Lemma 7.8 with `ε₁ = δ`, `D₁ = gaussD p`)
  have hlaw0 : interpLaw 0 (fun _ => gaussLaw N) (entryLaw X) =
      Measure.pi fun _ : Fin M × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    unfold interpLaw
    congr 1
    funext α
    simp [mixMeasure, unitClamp, gaussLaw]
  have h2δ : (2 : ℝ) ≤ (N : ℝ) ^ δ := m2m_le_rpow (Q := 2) (a := δ) (by norm_num) hδ hN2δ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hC1 : (1 : ℝ) ≤ (C₀ - 1) * p := by nlinarith
  have h0 : ∀ w, Φ w 0 ≤ a := by
    intro w
    have h0eq : Φ w 0 = ∫ ω, Fv Sig (gaussX M N ω) z (vfam v w) ^ p := by
      rw [hΦeq w 0 ⟨le_rfl, zero_le_one⟩, hlaw0]
      rfl
    rw [h0eq]
    have hz0 := h₂ N hNN₂ M Sig S δ (gaussD p) hset.ratio_ge hset.ratio_le hset.sigma
      hset.domain hset.oneXm hδ.le (by unfold gaussD; linarith) hgauss z hzS (vfam v w) (hvw w)
    refine hz0.trans ?_
    have h24 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ ((C₀ - 1) * δ * p) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by nlinarith)
    have hsplit : (N : ℝ) ^ (C₀ * δ * p) =
        (N : ℝ) ^ ((p : ℝ) * δ) * (N : ℝ) ^ ((C₀ - 1) * δ * p) := by
      rw [← Real.rpow_add hNpos]
      ring_nf
    have hpow : ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p =
        (N : ℝ) ^ (C₀ * δ * p) * Psi N (specOf Sig) z ^ p := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (C₀ * δ)), ← Real.rpow_mul hNpos.le]
    rw [ha, hpow, hsplit]
    have hA0 : 0 ≤ (N : ℝ) ^ ((p : ℝ) * δ) := Real.rpow_nonneg hNpos.le _
    have hP0 : 0 ≤ Psi N (specOf Sig) z ^ p := pow_nonneg hΨ.le _
    have : 2 * (N : ℝ) ^ ((p : ℝ) * δ) ≤
        (N : ℝ) ^ ((p : ℝ) * δ) * (N : ℝ) ^ ((C₀ - 1) * δ * p) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right this hP0
  -- Grönwall over `𝒱_v`
  have hgr := gronwall_sup (Φ := Φ) (Φ' := Φ') (K := Cs) (a := a) (B := B) hCs ha0 hB hderiv
    hbound h0 none
  -- `Φ_v(1) = E F_v^p(X)`: the entries of `X` are independent
  have h1 : ∫ ω, Fv Sig (X ω) z v ^ p = Φ none 1 := by
    rw [hΦeq none 1 ⟨zero_le_one, le_rfl⟩]
    have hg1 : Measurable fun ω (β : Fin M × Fin N) => X ω β.1 β.2 :=
      measurable_pi_iff.2 fun β => hX.measurable β.1 β.2
    have hlaw1 : interpLaw 1 (fun _ => gaussLaw N) (entryLaw X) =
        (ℙ : Measure Ω).map (fun ω (β : Fin M × Fin N) => X ω β.1 β.2) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map
        (fun β : Fin M × Fin N => (hX.measurable β.1 β.2).aemeasurable)).1 hX.indep]
      unfold interpLaw
      congr 1
      funext α
      simp [mixMeasure, unitClamp, entryLaw]
    rw [hlaw1, integral_map hg1.aemeasurable (hFm none).aestronglyMeasurable]
    rfl
  rw [h1]
  refine hgr.trans ?_
  have := Real.exp_pos Cs
  nlinarith

/-! ## Lemma 7.4 and Proposition 8.1 -/

/-- Lemma 7.4 (`lem:induction`) for all `X`: (A_{m−1}) at `(δ/4, D_{m−1})` gives (C_m) at `(δ/8, D)`. -/
theorem propC_of_propA_gen (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (m : ℕ),
      CompSetting τ c M N Sig S → 1 ≤ m →
      AnisotropicLawAt N δ (gaussD (markovPow δ D)) Sig (gaussX M N) S →
      PropA N (momMax C) allModels Sig S C₀ δ (m - 1) (δ / 4) (dPrevTwo τ (markovPow δ D)) →
      PropC N (momMax C) allModels Sig S C₀ δ m (δ / 8) D := by
  have _hD := hD
  have hpE : Even (markovPow δ D) := ⟨max 1 ⌈8 * D / δ⌉₊, by unfold markovPow; ring⟩
  have hp2 : 2 ≤ markovPow δ D := by
    unfold markovPow
    have := le_max_left 1 ⌈8 * D / δ⌉₊
    omega
  obtain ⟨Kp, hKp, N₁, h₁⟩ := moment_bound_gen τ c C (markovPow δ D) C₀ δ hτ hτ1 hc hpE hp2 hδ
    hC₀ hC₀δ
  refine ⟨max (max N₁ ⌈Kp ^ (δ / 16)⁻¹⌉₊) 1, fun N hN M Sig S m hset hm hgauss hA => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNN₁ : N₁ ≤ N := by omega
  have hNK : ⌈Kp ^ (δ / 16)⁻¹⌉₊ ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine propC_of_moment (ε := δ / 16) (Kp := Kp) hset hN1 ?_ ?_
    (fun Ω _ _ X hX _ => h₁ N hNN₁ M Sig S m hset hm hgauss hA Ω X hX)
  · -- `D ≤ (δ/8 − δ/16) p`, since `p ≥ 16 D / δ`.
    have hc1 : 8 * D / δ ≤ (⌈8 * D / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hc2 : (⌈8 * D / δ⌉₊ : ℝ) ≤ (max 1 ⌈8 * D / δ⌉₊ : ℕ) := by
      exact_mod_cast le_max_right _ _
    have hpc : ((markovPow δ D : ℕ) : ℝ) = 2 * ((max 1 ⌈8 * D / δ⌉₊ : ℕ) : ℝ) := by
      unfold markovPow
      push_cast
      ring
    have h8 : 8 * D = (8 * D / δ) * δ := by field_simp
    rw [hpc]
    nlinarith
  · -- `K_p ≤ N^{δ/16} ≤ N^{p δ/16}`.
    have hK := m2m_le_rpow hKp.le (by positivity : (0 : ℝ) < δ / 16) hNK
    refine hK.trans (Real.rpow_le_rpow_of_exponent_le hNr ?_)
    have : (1 : ℝ) ≤ (markovPow δ D : ℝ) := by exact_mod_cast (by omega : 1 ≤ markovPow δ D)
    nlinarith

/-- The anisotropic law at `(ε, D)` gives it at `(ε, D')` for `D' ≤ D`. -/
private theorem m2m_aniso_mono {Ω : Type*} [MeasureSpace Ω] {Sig : Matrix (Fin M) (Fin M) ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} {ε D D' : ℝ} (hN : 1 ≤ N) (hD : D' ≤ D)
    (h : AnisotropicLawAt N ε D Sig X S) : AnisotropicLawAt N ε D' Sig X S := by
  intro z hz v w
  have h1 := h z hz v w
  unfold DomAt at h1 ⊢
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- Proposition 8.1 (`prop:comparison_2`) at fixed `N`: the anisotropic law for `X^Gauss` at
`(ε₁, D₁)` gives the anisotropic law for `X` at `(ε, D)`, with no condition on third moments. -/
theorem prop_comparison_two (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S → AnisotropicLawAt N ε₁ D₁ Sig (gaussX M N) S →
      AnisotropicLawAt N ε D Sig X S := by
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = czero τ := ⟨_, rfl⟩
  have hC₀ : czero τ ≤ C₀ := hC₀def.symm.le
  have h25 : 25 ≤ C₀ := (m2s_czero_ge hτ hτ1).trans hC₀
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = deltaTwo ε τ := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef, deltaTwo, ← hC₀def]
    exact div_pos (lt_min hε hτ) (by linarith)
  have hC₀δe : C₀ * δ = min ε τ / 4 := by
    rw [hδdef, deltaTwo, ← hC₀def]
    field_simp
  have hC₀δ : C₀ * δ ≤ τ / 4 := by
    rw [hC₀δe]
    linarith [min_le_right ε τ]
  have hC₀δε : C₀ * δ ≤ ε / 4 := by
    rw [hC₀δe]
    linarith [min_le_left ε τ]
  have hδε : δ ≤ ε / 100 := by nlinarith
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ, D' = max D 0 := ⟨_, rfl⟩
  have hD'0 : 0 ≤ D' := hD' ▸ le_max_right _ _
  have hDD' : D ≤ D' := hD' ▸ le_max_left _ _
  obtain ⟨ms, hms⟩ : ∃ ms : ℕ, ms = topLevel τ δ := ⟨_, rfl⟩
  have hms1 : 1 ≤ ms := hms ▸ le_max_left _ _
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ,
      D₁ = ∑ k ∈ Finset.range ms, gaussD (markovPow δ (levelDTwo τ δ D' k)) := ⟨_, rfl⟩
  have hgD : ∀ k < ms, gaussD (markovPow δ (levelDTwo τ δ D' k)) ≤ D₁ := fun k hk => by
    rw [hD₁]
    exact Finset.single_le_sum (f := fun k => gaussD (markovPow δ (levelDTwo τ δ D' k)))
      (fun j _ => by unfold gaussD; positivity) (Finset.mem_range.2 hk)
  have hlev : ∀ k, 0 ≤ levelDTwo τ δ D' k := by
    intro k
    cases k with
    | zero => simp only [levelDTwo]; linarith
    | succ k => simp only [levelDTwo, dPrevTwo, dPrev]; positivity
  refine ⟨δ, D₁, hδ, ?_⟩
  -- (A_k) at `(δ/4, D_k)` for `k ≤ m* − 1`, with `D_k = levelDTwo τ δ D' (m* − k)`.
  have ind : ∀ k, k ≤ ms - 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
      (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), CompSetting τ c M N Sig S →
      AnisotropicLawAt N δ D₁ Sig (gaussX M N) S →
      PropA N (momMax C) allModels Sig S C₀ δ k (δ / 4) (levelDTwo τ δ D' (ms - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨N₀, h⟩ := propA_zero τ c (momMax C) (δ / 4) (levelDTwo τ δ D' (ms - 0)) hτ hτ1 hc
        (by positivity)
      exact ⟨N₀, fun N hN M Sig S hset _ => h N hN M Sig S allModels C₀ δ hset (by linarith)
        hδ.le⟩
    | succ k ih =>
      intro hk
      obtain ⟨N₁, h₁⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, j = ms - (k + 1) := ⟨_, rfl⟩
      have hjk : ms - k = j + 1 := by omega
      have hjm : j < ms := by omega
      obtain ⟨N₂, h₂⟩ := propC_of_propA_gen τ c C C₀ δ (levelDTwo τ δ D' j) hτ hτ1 hc hδ hC₀ hC₀δ
        (hlev j)
      refine ⟨max (max N₁ N₂) (max ⌈(max (c⁻¹ ^ 2) 1) ^ (δ / 8)⁻¹⌉₊ 1),
        fun N hN M Sig S hset hg => ?_⟩
      have hN1 : 1 ≤ N := by omega
      have hNN₁ : N₁ ≤ N := by omega
      have hNN₂ : N₂ ≤ N := by omega
      have hNc : ⌈(max (c⁻¹ ^ 2) 1) ^ (δ / 8)⁻¹⌉₊ ≤ N := by omega
      have hA := h₁ N hNN₁ M Sig S hset hg
      rw [hjk] at hA
      have hg' : AnisotropicLawAt N δ (gaussD (markovPow δ (levelDTwo τ δ D' j))) Sig
          (gaussX M N) S :=
        m2m_aniso_mono hN1 (hgD j hjm) hg
      have hC := h₂ N hNN₂ M Sig S (k + 1) hset (by omega) hg' hA
      have hcN : max (c⁻¹ ^ 2) 1 ≤ (N : ℝ) ^ (δ / 8) :=
        m2m_le_rpow (by positivity) (by positivity) hNc
      rw [← hj]
      exact PropA.mono hset hN1 (by linarith) le_rfl (propA_of_propC hset hN1 hcN hC)
  obtain ⟨N₁, h₁⟩ := ind (ms - 1) le_rfl
  obtain ⟨N₂, h₂⟩ := propC_of_propA_gen τ c C C₀ δ (D' + 1) hτ hτ1 hc hδ hC₀ hC₀δ (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun N hN Ω _ _ M Sig X S hm hS hx hg => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hset : CompSetting τ c M N Sig S :=
    ⟨hτ, hτ1, hc, hm.ratio_ge, hm.ratio_le, hm.sigma, hS, hx⟩
  have hA := h₁ N hNN₁ M Sig S hset hg
  have e1 : ms - (ms - 1) = 0 + 1 := by omega
  rw [e1] at hA
  have hg' : AnisotropicLawAt N δ (gaussD (markovPow δ (D' + 1))) Sig (gaussX M N) S :=
    m2m_aniso_mono hN1 (hgD 0 (by omega)) hg
  have hC := h₂ N hNN₂ M Sig S ms hset hms1 hg' hA
  have hX : EntryAssumption (momMax C) X := hm.entries.mono fun q => le_max_left _ _
  have hεK : (N : ℝ) ^ (δ / 8) * (N : ℝ) ^ (C₀ * δ) ≤ (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  refine aniso_of_diag_bound hset.sigma.posDef (fun z hz => (hS.1 hz).1) (ε₀ := δ / 8)
    (K := (N : ℝ) ^ (C₀ * δ)) hN2 (Real.rpow_nonneg hNpos.le _) hεK ?_
  intro z hz u hu
  -- `S_{m*} = S`, since `δ m* ≥ 1 − τ`.
  have hzm : z ∈ levelSet N δ S ms := by
    refine ⟨hz, ?_⟩
    have hzD := hS.1 hz
    have hc1 : (1 - τ) / δ ≤ (ms : ℝ) := by
      rw [hms]
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have hc2 : 1 - τ ≤ δ * ms := by
      rw [div_le_iff₀ hδ] at hc1
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)).trans hzD.2.2.2.1
  have hd := hC Ω X hX trivial z hzm u hu
  unfold ODomAt at hd
  simp_rw [ent_vbar_eq_testBilin hset.sigma.posDef] at hd
  have hΨ : 0 ≤ (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z := by
    have hzim : 0 < z.im := (hS.1 hz).1
    unfold Psi
    have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
    have := Real.sqrt_nonneg ((mFun N (specOf Sig) z).im / (N * z.im))
    exact mul_nonneg (Real.rpow_nonneg hNpos.le _) (by linarith)
  exact DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => hΨ) le_rfl
    (by linarith) hd

/-! ## Instances of the statements

The parameters are `τ = 1/2`, `c = 1`, `C_q = 2`, `p = 2`, `C₀ = C₀(1/2) = 4800`,
`δ = δ(1, 1/2) = min(1, 1/2)/(4 C₀(1/2)) = 1/38400` (so `C₀ δ = τ/4`), `ε_A = δ/4` and
`D_A = dPrevTwo (1/2) 2`. The `∃ N₀` statements are instantiated with the setting, (A_{m−1}),
the entry conditions and the remaining model hypotheses as binders (conditional instances): at
`N = 2` the level `N^{C₀δ} Ψ` exceeds `1`, so these bounds carry content only for large `N`. -/

section Checks

/-- The moment-matching expansion without (zero_third_moment) at the parameters above. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption (fun _ => 2) X →
        P Ω X → IndepFun X y → Measurable y → ∫ ω, y ω = 0 → ∫ ω, y ω ^ 2 = 1 / (N : ℝ) →
        (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
          ∫ ω, |Real.sqrt N * y ω| ^ q ≤ (fun _ => (2 : ℝ)) q) →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ (i : Fin M) (μ : Fin N)
          (v : Fin M ⊕ Fin N → ℝ), testNorm v = 1 →
          ‖(∫ ω, (Fv Sig (Xupd (X ω) i μ (y ω)) z v : ℂ) ^ 2)
              - (∫ ω, (fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 0
                  + (N : ℂ)⁻¹ * fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) 2))
              - ∑ n ∈ Finset.Icc 3 (4 * 2),
                  (∫ ω, fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n) *
                    ∫ ω, (y ω : ℂ) ^ n‖
            ≤ 2 * (N : ℝ) ^ (deltaTwo 1 (1 / 2) - 2) * Psi N (specOf Sig) z ^ 2 := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact moment_matching3 (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two
    le_rfl (by rw [hd]; norm_num) (by rw [hc]; norm_num) (by rw [hc, hd]; norm_num)
    (by rw [hd]; norm_num) le_rfl (m2s_dPrev_le _ _)

/-- Lemma 7.16 for `n ∈ [3, 4p]` at the parameters above. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ B : ℝ, 0 ≤ B →
          (∀ n ∈ Finset.Icc (3 : ℕ) (4 * 2), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (resCoeff Sig (X ω) z v i μ) n‖ ≤ B) →
          ∀ n ∈ Finset.Icc (3 : ℕ) (4 * 2), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n‖ ≤
              K * (B + (N : ℝ) ^ deltaTwo 1 (1 / 2) * Psi N (specOf Sig) z ^ 2) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact zero_to_theta3 (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two
    le_rfl (by rw [hd]; norm_num) (by rw [hc]; norm_num) (by rw [hc, hd]; norm_num)
    (by rw [hd]; norm_num) le_rfl (m2s_dPrev_le _ _)

/-- Lemma 7.11 for all `X` at the parameters above. -/
example : ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
      (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S →
      1 ≤ m →
      PropA N (momMax fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax fun _ => 2) X →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ u : Bool,
          ‖∑ α : Fin M × Fin N,
              ((∫ x, (Fv Sig (ofCoord x) z v : ℂ) ^ 2 ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (if u then entryLaw X α else gaussLaw N)))
                - ∫ x, (fCoeff 2 (resCoeff Sig (ofCoord (Function.update x α 0)) z v α.1 α.2) 0
                    + (N : ℂ)⁻¹ * fCoeff 2 (resCoeff Sig (ofCoord (Function.update x α 0)) z v
                      α.1 α.2) 2) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)))‖ ≤
            Cstar * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) *
              Psi N (specOf Sig) z) ^ 2 +
              ⨆ w : Option (Fin N), ∫ x, Fv Sig (ofCoord x) z (vfam v w) ^ 2
                ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact main_comparison2_gen (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (by norm_num) (by norm_num) one_pos even_two le_rfl (by rw [hd]; norm_num) le_rfl
    (by rw [hc, hd]; norm_num)

/-- Lemma 7.10 for all `X` at the parameters above. -/
example : ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
      (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S →
      1 ≤ m →
      PropA N (momMax fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax fun _ => 2) X →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          |∑ α : Fin M × Fin N,
              ((∫ x, Fv Sig (ofCoord x) z v ^ 2 ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (entryLaw X α)))
                - ∫ x, Fv Sig (ofCoord x) z v ^ 2 ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (gaussLaw N)))| ≤
            Cstar * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) *
              Psi N (specOf Sig) z) ^ 2 +
              ⨆ w : Option (Fin N), ∫ x, Fv Sig (ofCoord x) z (vfam v w) ^ 2
                ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact main_comparison_gen (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (by norm_num) (by norm_num) one_pos even_two le_rfl (by rw [hd]; norm_num) le_rfl
    (by rw [hc, hd]; norm_num)

/-- Lemma 7.5 for all `X` at the parameters above. -/
example : ∃ Kp : ℝ, 0 < Kp ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      AnisotropicLawAt N (deltaTwo 1 (1 / 2)) (gaussD 2) Sig (gaussX M N) S →
      PropA N (momMax fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax fun _ => 2) X →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          Integrable (fun ω => Fv Sig (X ω) z v ^ 2) ∧
            ∫ ω, Fv Sig (X ω) z v ^ 2 ≤ Kp * ((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) *
              Psi N (specOf Sig) z) ^ 2 := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact moment_bound_gen (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (by norm_num) (by norm_num) one_pos even_two le_rfl (by rw [hd]; norm_num) le_rfl
    (by rw [hc, hd]; norm_num)

/-- Lemma 7.4 for all `X` at the parameters above and `D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (m : ℕ),
      CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      AnisotropicLawAt N (deltaTwo 1 (1 / 2)) (gaussD (markovPow (deltaTwo 1 (1 / 2)) 1)) Sig
        (gaussX M N) S →
      PropA N (momMax fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) (markovPow (deltaTwo 1 (1 / 2)) 1)) →
      PropC N (momMax fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) m
        (deltaTwo 1 (1 / 2) / 8) 1 := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact propC_of_propA_gen (1 / 2) 1 (fun _ => 2) (czero (1 / 2)) (deltaTwo 1 (1 / 2)) 1
    (by norm_num) (by norm_num) one_pos (by rw [hd]; norm_num) le_rfl (by rw [hc, hd]; norm_num)
    zero_le_one

/-- Proposition 8.1 at `τ = 1/2`, `c = 1`, `C_q = 2`, `ε = 1`, `D = 1`. -/
example :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel (1 / 2) (fun _ => 2) M N Sig X → SpectralDomain (1 / 2) N S →
      OneXmOn 1 N (specOf Sig) S → AnisotropicLawAt N ε₁ D₁ Sig (gaussX M N) S →
      AnisotropicLawAt N 1 1 Sig X S :=
  prop_comparison_two (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Proposition 8.1 at `τ = 1/2`, `c = 1`, `C_q = 2^q`, `ε = 1`, `D = 1`; this moment function
allows entries with nonzero third moment, e.g. `√N X_{iμ} ∈ {2, −1/2}` with probabilities
`(1/5, 4/5)` (third moment `3/2`). -/
example :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel (1 / 2) (fun q => 2 ^ q) M N Sig X → SpectralDomain (1 / 2) N S →
      OneXmOn 1 N (specOf Sig) S → AnisotropicLawAt N ε₁ D₁ Sig (gaussX M N) S →
      AnisotropicLawAt N 1 1 Sig X S :=
  prop_comparison_two (1 / 2) 1 (fun q => 2 ^ q) 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The two-point law `{2, −1/2}` with weights `(1/5, 4/5)`: mean `0`, variance `1`, third
moment `3/2`, and `E|ξ|^q = (2^q + 4 · 2^{−q})/5 ≤ 2^q`. -/
example : (1 / 5 : ℝ) * 2 + 4 / 5 * (-1 / 2) = 0 ∧ (1 / 5 : ℝ) * 2 ^ 2 + 4 / 5 * (-1 / 2) ^ 2 = 1 ∧
    (1 / 5 : ℝ) * 2 ^ 3 + 4 / 5 * (-1 / 2) ^ 3 = 3 / 2 ∧
    ∀ q : ℕ, (1 / 5 : ℝ) * 2 ^ q + 4 / 5 * (1 / 2) ^ q ≤ 2 ^ q := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun q => ?_⟩
  have h1 : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  nlinarith

set_option pp.parens true in
#check @moment_matching3

end Checks

end Anisotropic

#print axioms Anisotropic.moment_matching3
#print axioms Anisotropic.zero_to_theta3
#print axioms Anisotropic.main_comparison2_gen
#print axioms Anisotropic.main_comparison_gen
#print axioms Anisotropic.moment_bound_gen
#print axioms Anisotropic.propC_of_propA_gen
#print axioms Anisotropic.prop_comparison_two
