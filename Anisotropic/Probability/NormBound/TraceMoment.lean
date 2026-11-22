module

public import Anisotropic.Probability.NormBound.WalkCount
public import Anisotropic.Framework.Model

@[expose] public section

/-!
# Trace moment of `Y Yᵀ`

Two steps of the moment method in the proof of Lemma 4.8 (`lem:norm_XX`): the spectral bound
`‖Y Yᵀ‖^k ≤ tr (Y Yᵀ)^k`, and the trace moment bound `E tr (Y Yᵀ)^k ≤ 2 τ⁻¹ (9/τ)^k N` for a
`K × N` matrix with independent centred entries, `E Y² ≤ 1/N`, `|Y| ≤ b`, `b² N ≥ 1`,
`2 (2k)^6 b² ≤ 1` and `K ≤ τ⁻¹ N`. In the walk expansion of the trace only even walks have
nonzero expectation; an even walk with `v` vertices has weight at most `b^{2k} (b² N)^{1-v}`,
and the count of even walks with `v` vertices gives a geometric series in `v` with ratio at
most `1/2`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- a product over `Fin k` grouped by the values of `g` -/
private lemma traceMoment_prod_fiber {k : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (g : Fin k → α) (F : α → ℝ) :
    ∏ t, F (g t) = ∏ p, F p ^ (Finset.univ.filter fun t => g t = p).card := by
  rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ) (g := g)
    (fun _ _ => Finset.mem_univ _) F]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_const]

/-- the weight of a walk as a product over edges with multiplicities -/
private lemma traceMoment_prod_eq {k K N : ℕ} (Y : Matrix (Fin K) (Fin N) ℝ)
    (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    ∏ t, Y (i t) (μ t) * Y (i (finRotate k t)) (μ t) =
      ∏ p : Fin K × Fin N, Y p.1 p.2 ^ walkMult i μ p.1 p.2 := by
  rw [Finset.prod_mul_distrib]
  have h1 := traceMoment_prod_fiber (fun t => (i t, μ t)) (fun p => Y p.1 p.2)
  have h2 := traceMoment_prod_fiber (fun t => (i (finRotate k t), μ t)) (fun p => Y p.1 p.2)
  simp only [Prod.ext_iff] at h1 h2
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [walkMult, pow_add]

/-- the multiplicities of a closed walk of length `2k` sum to `2k` -/
private lemma traceMoment_sum_mult {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    ∑ e : Fin K × Fin N, walkMult i μ e.1 e.2 = 2 * k := by
  have hf : ∀ {α : Type} [Fintype α] [DecidableEq α] (g : Fin k → α),
      ∑ e : α, (Finset.univ.filter fun t => g t = e).card = k := by
    intro α _ _ g
    have := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin k))
      (Finset.univ : Finset α) g
    simpa using this
  unfold walkMult
  rw [Finset.sum_add_distrib]
  have h1 := hf (fun t => (i t, μ t))
  have h2 := hf (fun t => (i (finRotate k t), μ t))
  simp only [Prod.ext_iff] at h1 h2
  rw [h1, h2]
  ring

/-- every edge of a walk has positive multiplicity -/
private lemma traceMoment_mult_pos {k K N : ℕ} (i : Fin k → Fin K) (μ : Fin k → Fin N)
    {e : Fin K × Fin N} (he : e ∈ walkEdges i μ) : walkMult i μ e.1 e.2 ≠ 0 := by
  unfold walkMult
  unfold walkEdges at he
  rcases Finset.mem_union.1 he with he | he
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 he
    have : 0 < (Finset.univ.filter fun s => i s = (i t, μ t).1 ∧ μ s = (i t, μ t).2).card :=
      Finset.card_pos.2 ⟨t, by simp⟩
    omega
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 he
    have : 0 < (Finset.univ.filter fun s => i (finRotate k s) = (i (finRotate k t), μ t).1 ∧
        μ s = (i (finRotate k t), μ t).2).card :=
      Finset.card_pos.2 ⟨t, by simp⟩
    omega

/-- moment bound for one centred bounded entry -/
private lemma traceMoment_abs_integral_pow_le {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} {c : ℝ} (hc : 0 < c) (X : Ω → ℝ)
    (hX : Measurable X) (hmean : ∫ ω, X ω = 0) (hvar : ∫ ω, X ω ^ 2 ≤ 1 / (N : ℝ))
    (hbd : ∀ ω, |X ω| ≤ c) (m : ℕ) :
    |∫ ω, X ω ^ m| ≤ if m = 1 then 0 else c ^ m * (if m = 0 then 1 else (c ^ 2 * N)⁻¹) := by
  rcases m with _ | _ | j
  · simp
  · simp [hmean]
  · simp only [show j + 2 ≠ 1 by omega, show j + 2 ≠ 0 by omega, ite_false]
    have hint : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) := fun n =>
      Integrable.of_bound (hX.pow_const n).aestronglyMeasurable (c ^ n)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω) n)
    calc |∫ ω, X ω ^ (j + 2)| ≤ ∫ ω, |X ω ^ (j + 2)| := abs_integral_le_integral_abs
      _ ≤ ∫ ω, c ^ j * X ω ^ 2 := by
          refine integral_mono (hint _).abs ((hint 2).const_mul _) fun ω => ?_
          rw [abs_pow, pow_add, ← sq_abs (X ω)]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hbd ω) j)
            (sq_nonneg _)
      _ = c ^ j * ∫ ω, X ω ^ 2 := integral_const_mul _ _
      _ ≤ c ^ j * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hvar (pow_nonneg hc.le _)
      _ = c ^ (j + 2) * (c ^ 2 * N)⁻¹ := by
          rw [mul_inv, pow_add, mul_assoc, ← mul_assoc (c ^ 2), mul_inv_cancel₀ (by positivity),
            one_mul, one_div]


open Classical in
/-- product of the entry bounds over the edges of a walk -/
private lemma traceMoment_prod_le {k K N : ℕ} (hk : 1 ≤ k) {c β : ℝ} (hc : 0 ≤ c) (hβ : 1 ≤ β)
    (i : Fin k → Fin K) (μ : Fin k → Fin N) :
    ∏ p : Fin K × Fin N, (if walkMult i μ p.1 p.2 = 1 then 0 else
        c ^ walkMult i μ p.1 p.2 * (if walkMult i μ p.1 p.2 = 0 then 1 else β⁻¹)) ≤
      if IsEvenWalk i μ then c ^ (2 * k) * β * β⁻¹ ^ walkVerts i μ else 0 := by
  split_ifs with hev
  · have h : ∀ p ∈ (Finset.univ : Finset (Fin K × Fin N)),
        (if walkMult i μ p.1 p.2 = 1 then 0 else
          c ^ walkMult i μ p.1 p.2 * (if walkMult i μ p.1 p.2 = 0 then 1 else β⁻¹)) =
        c ^ walkMult i μ p.1 p.2 * (if walkMult i μ p.1 p.2 = 0 then 1 else β⁻¹) := by
      intro p _
      simp only [hev p.1 p.2, ite_false]
    rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      traceMoment_sum_mult, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc _)
    have hv := (walkVerts_le hk i μ).1
    have hsub : walkEdges i μ ⊆
        (Finset.univ : Finset (Fin K × Fin N)).filter fun p => ¬ walkMult i μ p.1 p.2 = 0 :=
      fun e he => Finset.mem_filter.2 ⟨Finset.mem_univ _, traceMoment_mult_pos i μ he⟩
    have hcard := Finset.card_le_card hsub
    have h0 : 0 ≤ β⁻¹ := inv_nonneg.2 (by linarith)
    have h1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
    have hβ0 : β ≠ 0 := by positivity
    calc β⁻¹ ^ ((Finset.univ : Finset (Fin K × Fin N)).filter
            fun p => ¬ walkMult i μ p.1 p.2 = 0).card
        = β * β⁻¹ ^ (((Finset.univ : Finset (Fin K × Fin N)).filter
            fun p => ¬ walkMult i μ p.1 p.2 = 0).card + 1) := by
          rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hβ0, mul_one]
      _ ≤ β * β⁻¹ ^ walkVerts i μ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 (by omega)) (by linarith)
  · simp only [IsEvenWalk, not_forall, not_not] at hev
    obtain ⟨a, b, hab⟩ := hev
    exact (Finset.prod_eq_zero (Finset.mem_univ (a, b)) (by simp [hab])).le

section E1

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- `‖Y Yᵀ‖^k ≤ tr (Y Yᵀ)^k`. -/
theorem opNorm_pow_le_trace {K N : ℕ} (Y : Matrix (Fin K) (Fin N) ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ‖Y * Yᵀ‖ ^ k ≤ trace ((Y * Yᵀ) ^ k) := by
  have hpsd : (Y * Yᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose Y
  set hH := hpsd.isHermitian
  set U := hH.eigenvectorUnitary
  set lam := hH.eigenvalues
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set D : Matrix (Fin K) (Fin K) ℝ := diagonal (RCLike.ofReal ∘ lam)
  have hnorm : ‖Y * Yᵀ‖ = ‖(RCLike.ofReal ∘ lam : Fin K → ℝ)‖ := by
    rw [hspec, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  have htr : trace ((Y * Yᵀ) ^ k) = ∑ j, lam j ^ k := by
    have hUU : star (U : Matrix (Fin K) (Fin K) ℝ) * U = 1 := Unitary.star_mul_self_of_mem U.2
    have hpow : ∀ m : ℕ, (Y * Yᵀ) ^ m =
        (U : Matrix (Fin K) (Fin K) ℝ) * D ^ m * star (U : Matrix (Fin K) (Fin K) ℝ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ih, hspec, pow_succ]
        simp only [mul_assoc]
        rw [← mul_assoc (star (U : Matrix (Fin K) (Fin K) ℝ)) (U : Matrix (Fin K) (Fin K) ℝ), hUU,
          one_mul]
    rw [hpow, mul_assoc, trace_mul_comm, mul_assoc, hUU, mul_one, diagonal_pow, trace_diagonal]
    rfl
  have hlam : ∀ j, 0 ≤ lam j := hpsd.eigenvalues_nonneg
  have hlam' : (RCLike.ofReal ∘ lam : Fin K → ℝ) = lam := rfl
  rw [hnorm, htr, hlam']
  rcases isEmpty_or_nonempty (Fin K) with hK | hK
  · rw [Subsingleton.elim lam 0, norm_zero, zero_pow (by omega : k ≠ 0)]
    simp
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
    fun b => ‖lam b‖₊
  rw [Pi.norm_def, hj]
  have : ((‖lam j‖₊ : ℝ≥0) : ℝ) = lam j := by
    simp [abs_of_nonneg (hlam j)]
  rw [this]
  exact Finset.single_le_sum (fun i _ => pow_nonneg (hlam i) k) (Finset.mem_univ j)

/-- Trace moment for bounded centred independent entries:
`E tr (Y Yᵀ)^k ≤ 2 τ^{-1} (9/τ)^k N` when `2 (2k)^6 b² ≤ 1`, `b² N ≥ 1`, `K ≤ τ⁻¹ N`. -/
theorem integral_trace_pow_le {τ b : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {k K N : ℕ} (hk : 1 ≤ k)
    (hK : (K : ℝ) ≤ τ⁻¹ * N) (Y : Ω → Matrix (Fin K) (Fin N) ℝ)
    (hmeas : ∀ i μ, Measurable fun ω => Y ω i μ)
    (hind : iIndepFun (fun (p : Fin K × Fin N) ω => Y ω p.1 p.2) ℙ)
    (hmean : ∀ i μ, ∫ ω, Y ω i μ = 0) (hvar : ∀ i μ, ∫ ω, Y ω i μ ^ 2 ≤ 1 / (N : ℝ))
    (hbd : ∀ ω i μ, |Y ω i μ| ≤ b) (hbN : 1 ≤ b ^ 2 * N)
    (hsmall : 2 * ((2 * k : ℕ) : ℝ) ^ 6 * b ^ 2 ≤ 1) :
    ∫ ω, trace ((Y ω * (Y ω)ᵀ) ^ k) ≤ 2 * τ⁻¹ * (9 / τ) ^ k * N := by
  classical
  set c := |b| with hc_def
  have hcb : c ^ 2 = b ^ 2 := sq_abs b
  have hbd' : ∀ ω i μ, |Y ω i μ| ≤ c := fun ω i μ => (hbd ω i μ).trans (le_abs_self b)
  set β := c ^ 2 * (N : ℝ) with hβ_def
  have hβ : 1 ≤ β := by rw [hβ_def, hcb]; exact hbN
  have hc : 0 < c := by
    by_contra h
    have h0 : c = 0 := le_antisymm (not_lt.1 h) (abs_nonneg b)
    rw [hβ_def, h0] at hβ
    norm_num at hβ
  have hτ1' : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hpt : ∀ ω, trace ((Y ω * (Y ω)ᵀ) ^ k) = ∑ i : Fin k → Fin K, ∑ μ : Fin k → Fin N,
      ∏ p : Fin K × Fin N, Y ω p.1 p.2 ^ walkMult i μ p.1 p.2 := by
    intro ω
    rw [trace_pow_eq_sum_walks hk]
    simp_rw [traceMoment_prod_eq]
  have hint : ∀ (i : Fin k → Fin K) (μ : Fin k → Fin N),
      Integrable (fun ω => ∏ p : Fin K × Fin N, Y ω p.1 p.2 ^ walkMult i μ p.1 p.2) := by
    intro i μ
    refine Integrable.of_bound ?_ (∏ p : Fin K × Fin N, c ^ walkMult i μ p.1 p.2)
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Finset.measurable_prod _ fun p _ => (hmeas p.1 p.2).pow_const _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) fun p _ => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd' ω p.1 p.2) _
  have hE : ∀ (i : Fin k → Fin K) (μ : Fin k → Fin N),
      ∫ ω, ∏ p : Fin K × Fin N, Y ω p.1 p.2 ^ walkMult i μ p.1 p.2 =
        ∏ p : Fin K × Fin N, ∫ ω, Y ω p.1 p.2 ^ walkMult i μ p.1 p.2 := by
    intro i μ
    exact iIndepFun.integral_fun_prod_comp (𝕜 := ℝ) (μ := ℙ) (𝓧 := fun _ => ℝ)
      (X := fun (p : Fin K × Fin N) ω => Y ω p.1 p.2)
      (f := fun (p : Fin K × Fin N) (x : ℝ) => x ^ walkMult i μ p.1 p.2) hind
      (fun p => (hmeas p.1 p.2).aemeasurable)
      (fun p => (continuous_pow (walkMult i μ p.1 p.2)).aestronglyMeasurable)
  have hstep : ∫ ω, trace ((Y ω * (Y ω)ᵀ) ^ k) ≤ ∑ i : Fin k → Fin K, ∑ μ : Fin k → Fin N,
      (if IsEvenWalk i μ then c ^ (2 * k) * β * β⁻¹ ^ walkVerts i μ else 0) := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ => hint i μ]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ fun μ _ => hint i μ]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [hE]
    refine (le_abs_self _).trans ?_
    rw [Finset.abs_prod]
    refine (Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) fun p _ =>
      traceMoment_abs_integral_pow_le hc _ (hmeas p.1 p.2) (hmean p.1 p.2) (hvar p.1 p.2)
        (fun ω => hbd' ω p.1 p.2) _).trans ?_
    exact traceMoment_prod_le hk hc.le hβ i μ
  refine hstep.trans ?_
  rw [← Fintype.sum_prod_type' (f := fun i μ =>
    if IsEvenWalk i μ then c ^ (2 * k) * β * β⁻¹ ^ walkVerts i μ else 0), ← Finset.sum_filter]
  have hmaps : ∀ w ∈ (Finset.univ : Finset ((Fin k → Fin K) × (Fin k → Fin N))).filter
      (fun w => IsEvenWalk w.1 w.2), walkVerts w.1 w.2 ∈ Finset.range (k + 2) := by
    intro w hw
    have hev := (Finset.mem_filter.1 hw).2
    have h := walkVerts_le hk w.1 w.2
    have := h.2 hev
    exact Finset.mem_range.2 (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun v => c ^ (2 * k) * β * β⁻¹ ^ v)]
  simp_rw [Finset.sum_const, Finset.filter_filter, nsmul_eq_mul]
  have hMN : max (K : ℝ) N ≤ τ⁻¹ * N :=
    max_le hK (le_mul_of_one_le_left (Nat.cast_nonneg _) hτ1')
  have hsm : ((2 * k : ℕ) : ℝ) ^ 6 * c ^ 2 ≤ 1 / 2 := by rw [hcb]; linarith
  have hβ0 : β ≠ 0 := by positivity
  have hterm : ∀ v ∈ Finset.range (k + 2),
      (((Finset.univ : Finset ((Fin k → Fin K) × (Fin k → Fin N))).filter
          fun w => IsEvenWalk w.1 w.2 ∧ walkVerts w.1 w.2 = v).card : ℝ) *
        (c ^ (2 * k) * β * β⁻¹ ^ v) ≤
      9 ^ k * τ⁻¹ ^ (k + 1) * N * (1 / 2) ^ (k + 1 - v) := by
    intro v hv
    obtain ⟨s, hs⟩ : ∃ s, k + 1 = v + s := ⟨k + 1 - v, by rw [Finset.mem_range] at hv; omega⟩
    have hsv : k + 1 - v = s := by omega
    have hcard := card_evenWalk_le (K := K) (N := N) hk v
    rw [hsv] at hcard ⊢
    have hW : 0 ≤ c ^ (2 * k) * β * β⁻¹ ^ v := by positivity
    have hMv : (max (K : ℝ) N) ^ v ≤ τ⁻¹ ^ (k + 1) * (N : ℝ) ^ v := by
      calc (max (K : ℝ) N) ^ v ≤ (τ⁻¹ * N) ^ v :=
            pow_le_pow_left₀ (le_max_of_le_right (Nat.cast_nonneg _)) hMN v
        _ = τ⁻¹ ^ v * (N : ℝ) ^ v := mul_pow _ _ _
        _ ≤ τ⁻¹ ^ (k + 1) * (N : ℝ) ^ v :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hτ1' (by omega)) (by positivity)
    have hkey : (N : ℝ) ^ v * (c ^ 2) ^ v * β⁻¹ ^ v = 1 := by
      rw [← mul_pow, ← mul_pow, mul_comm (N : ℝ), ← hβ_def, mul_inv_cancel₀ hβ0, one_pow]
    have hcβ : c ^ (2 * k) * β = (c ^ 2) ^ v * (c ^ 2) ^ s * N := by
      rw [← pow_add, ← hs, pow_mul, hβ_def, pow_succ]
      ring
    have hgeo : (((2 * k : ℕ) : ℝ) ^ 6 * c ^ 2) ^ s ≤ (1 / 2) ^ s :=
      pow_le_pow_left₀ (by positivity) hsm s
    calc _ ≤ 9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * s) * (max (K : ℝ) N) ^ v *
            (c ^ (2 * k) * β * β⁻¹ ^ v) := by
          refine mul_le_mul_of_nonneg_right (le_of_eq_of_le ?_ hcard) hW
          congr 2
      _ ≤ 9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * s) * (τ⁻¹ ^ (k + 1) * (N : ℝ) ^ v) *
            (c ^ (2 * k) * β * β⁻¹ ^ v) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMv (by positivity)) hW
      _ = 9 ^ k * τ⁻¹ ^ (k + 1) * N * (((2 * k : ℕ) : ℝ) ^ 6 * c ^ 2) ^ s := by
          rw [hcβ, mul_pow, ← pow_mul]
          linear_combination (9 ^ k * ((2 * k : ℕ) : ℝ) ^ (6 * s) * τ⁻¹ ^ (k + 1) *
            (c ^ 2) ^ s * N) * hkey
      _ ≤ 9 ^ k * τ⁻¹ ^ (k + 1) * N * (1 / 2) ^ s :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
  calc _ ≤ ∑ v ∈ Finset.range (k + 2), 9 ^ k * τ⁻¹ ^ (k + 1) * N * (1 / 2 : ℝ) ^ (k + 1 - v) :=
        Finset.sum_le_sum hterm
    _ = 9 ^ k * τ⁻¹ ^ (k + 1) * N * ∑ v ∈ Finset.range (k + 2), (1 / 2 : ℝ) ^ v := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_reflect (fun v => (1 / 2 : ℝ) ^ v) (k + 2)
    _ ≤ 9 ^ k * τ⁻¹ ^ (k + 1) * N * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = 2 * τ⁻¹ * (9 / τ) ^ k * N := by
        rw [div_eq_mul_inv, mul_pow, pow_succ]
        ring

end E1

/-- `Y = [[1, 0], [1, 1]]`, `k = 2`: `Y Yᵀ = [[1, 1], [1, 2]]` and `tr (Y Yᵀ)^2 = 7`. -/
example :
    ‖(!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; 1, 1])ᵀ‖ ^ 2 ≤
      trace (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; 1, 1])ᵀ) ^ 2) ∧
    trace (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; 1, 1])ᵀ) ^ 2) = 7 := by
  refine ⟨opNorm_pow_le_trace _ (by norm_num), ?_⟩
  have hY : ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; 1, 1])ᵀ) =
      !![1, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]
  rw [hY, pow_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

end Anisotropic
