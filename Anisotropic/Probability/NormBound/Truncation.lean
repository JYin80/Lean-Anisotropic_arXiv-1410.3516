module

public import Anisotropic.Framework.DominationUnion

@[expose] public section

/-!
# Truncation of the entries

Truncation `X̂_{iμ} = X_{iμ} 1(|X_{iμ}| ≤ N^{-1/2+δ})` of the entries of `X` and re-centring, a
step of the proof of Lemma 4.8 (`lem:norm_XX`) under the entry conditions of Assumption 2.1:
the probability that the truncation changes `X` (union bound and Markov's inequality for the
moments `E|√N X_{iμ}|^q ≤ C_q`), and the size of the mean of a truncated entry, which equals minus
the mean of the discarded tail since `E X_{iμ} = 0`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- Truncation `X̂_{iμ} = X_{iμ} 1(|X_{iμ}| ≤ N^{-1/2+δ})`. -/
def truncX {Ω : Type*} {K N : ℕ} (δ : ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) :
    Ω → Matrix (Fin K) (Fin N) ℝ :=
  fun ω i μ => if |X ω i μ| ≤ (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) then X ω i μ else 0

section E1

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

private lemma truncX_natCast_pos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < N := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

private lemma truncX_sqrt_mul_thr {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) :
    Real.sqrt N * (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) = (N : ℝ) ^ δ := by
  have hpos := truncX_natCast_pos hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
  congr 1
  ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The entries are integrable. -/
private lemma truncX_integrable_entry {C : ℕ → ℝ} {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (i : Fin K) (μ : Fin N) : Integrable fun ω => X ω i μ := by
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (truncX_natCast_pos hN)
  have h1 : Integrable (fun ω => Real.sqrt N * X ω i μ) := by
    have hm : Measurable fun ω => Real.sqrt N * X ω i μ := (hX.measurable i μ).const_mul _
    rw [← integrable_norm_iff hm.aestronglyMeasurable]
    simpa [Real.norm_eq_abs] using hX.integrable_moment 1 i μ
  have := h1.const_mul (Real.sqrt N)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  field_simp

/-- Markov's inequality for one entry: `P(|X_{iμ}| > N^{-1/2+δ}) ≤ C_q N^{-qδ}`. -/
private lemma truncX_measure_tail_le {C : ℕ → ℝ} {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N) (δ : ℝ)
    (q : ℕ) (i : Fin K) (μ : Fin N) :
    ℙ {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω i μ|} ≤
      ENNReal.ofReal (C q * (N : ℝ) ^ (-(q * δ))) := by
  have hpos := truncX_natCast_pos hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hpos
  set ε : ℝ := (N : ℝ) ^ (q * δ) with hε
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hpos _
  have hsub : {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω i μ|} ⊆
      {ω | ε ≤ |Real.sqrt N * X ω i μ| ^ q} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : (N : ℝ) ^ δ ≤ |Real.sqrt N * X ω i μ| := by
      rw [abs_mul, abs_of_pos hs, ← truncX_sqrt_mul_thr hN δ]
      exact mul_le_mul_of_nonneg_left hω.le hs.le
    rw [hε, mul_comm (q : ℝ) δ, Real.rpow_mul_natCast hpos.le]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) h1 q
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (ℙ : Measure Ω))
    (f := fun ω => |Real.sqrt N * X ω i μ| ^ q)
    (Filter.Eventually.of_forall fun ω => by positivity) (hX.integrable_moment q i μ) ε
  have hmom := hX.moment q i μ
  have hreal : (ℙ : Measure Ω).real {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω i μ|} ≤
      C q * (N : ℝ) ^ (-(q * δ)) := by
    have h1 : (ℙ : Measure Ω).real {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω i μ|} ≤
        (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * X x i μ| ^ q} :=
      measureReal_mono hsub
    have h2 : ε * (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * X x i μ| ^ q} ≤ C q :=
      hmark.trans hmom
    have h3 : (N : ℝ) ^ (-(q * δ)) = ε⁻¹ := by
      rw [hε, ← Real.rpow_neg hpos.le]
    rw [h3]
    have : (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * X x i μ| ^ q} ≤ C q * ε⁻¹ := by
      rw [le_mul_inv_iff₀ hεpos]
      linarith
    exact h1.trans this
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Truncation: `P(X̂ ≠ X) ≤ K N C_q N^{-qδ}`. -/
theorem measure_truncX_ne_le {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (δ : ℝ) (q : ℕ) :
    ℙ {ω | truncX δ X ω ≠ X ω} ≤
      ENNReal.ofReal (K * N * C q * (N : ℝ) ^ (-(q * δ))) := by
  have hpos := truncX_natCast_pos hN
  have hsub : {ω | truncX δ X ω ≠ X ω} ⊆
      ⋃ p : Fin K × Fin N, {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω p.1 p.2|} := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
    ext i μ
    have h := hcon (i, μ)
    simp only [truncX, h, ite_true]
  have hbound := fun p : Fin K × Fin N => truncX_measure_tail_le hX hN δ q p.1 p.2
  calc ℙ {ω | truncX δ X ω ≠ X ω}
      ≤ ℙ (⋃ p : Fin K × Fin N, {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω p.1 p.2|}) :=
        measure_mono hsub
    _ ≤ ∑ p : Fin K × Fin N,
        ℙ {ω | (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) < |X ω p.1 p.2|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin K × Fin N, ENNReal.ofReal (C q * (N : ℝ) ^ (-(q * δ))) :=
        Finset.sum_le_sum fun p _ => hbound p
    _ = ENNReal.ofReal (K * N * C q * (N : ℝ) ^ (-(q * δ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos K with hK | hK
        · subst hK
          simp
        · have hCq : 0 ≤ C q :=
            (integral_nonneg fun ω => by positivity).trans (hX.moment q ⟨0, hK⟩ ⟨0, hN⟩)
          have hb : 0 ≤ C q * (N : ℝ) ^ (-(q * δ)) :=
            mul_nonneg hCq (Real.rpow_nonneg hpos.le _)
          have h : (K : ℝ) * N * C q * (N : ℝ) ^ (-(q * δ)) =
              ((K * N : ℕ) : ℝ) * (C q * (N : ℝ) ^ (-(q * δ))) := by
            push_cast
            ring
          rw [h, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

private lemma truncX_const_eq {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (n : ℕ) :
    (((N : ℝ) ^ (-(1 / 2 : ℝ) + δ)) ^ n)⁻¹ * (Real.sqrt N ^ (n + 1))⁻¹ =
      (N : ℝ) ^ (-(1 / 2 : ℝ) - δ * n) := by
  have hpos := truncX_natCast_pos hN
  rw [← Real.rpow_mul_natCast hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le, ← mul_inv, ← Real.rpow_add hpos, ← Real.rpow_neg hpos.le]
  congr 1
  push_cast
  ring

/-- Re-centring: `|E X̂_{iμ}| ≤ C_q N^{-1/2 - δ(q-1)}` for `q ≥ 1`. -/
theorem abs_integral_truncX_le {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (δ : ℝ) {q : ℕ} (hq : 1 ≤ q) (i : Fin K)
    (μ : Fin N) :
    |∫ ω, truncX δ X ω i μ| ≤ C q * (N : ℝ) ^ (-(1 / 2 : ℝ) - δ * (q - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have hpos := truncX_natCast_pos hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hpos
  set t : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hpos _
  set c : ℝ := (t ^ n)⁻¹ * (Real.sqrt N ^ (n + 1))⁻¹ with hc
  have hcpos : 0 ≤ c := by positivity
  have hcN : c = (N : ℝ) ^ (-(1 / 2 : ℝ) - δ * n) := truncX_const_eq hN δ n
  have hint := truncX_integrable_entry hX hN i μ
  have hmeas := hX.measurable i μ
  set A : Set Ω := {ω | t < |X ω i μ|} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hmeas.abs
  have htr : (fun ω => truncX δ X ω i μ) = fun ω => X ω i μ - A.indicator (fun ω => X ω i μ) ω := by
    funext ω
    have e : truncX δ X ω i μ = if |X ω i μ| ≤ t then X ω i μ else 0 := rfl
    by_cases h : |X ω i μ| ≤ t
    · have : ω ∉ A := by simp [hA, h]
      rw [e, Set.indicator_of_notMem this]
      simp [h]
    · have : ω ∈ A := by simpa [hA] using not_le.1 h
      rw [e, Set.indicator_of_mem this]
      simp [h]
  have hind : Integrable (A.indicator fun ω => X ω i μ) := hint.indicator hAm
  have hmean : ∫ ω, truncX δ X ω i μ = -∫ ω, A.indicator (fun ω => X ω i μ) ω := by
    rw [htr, integral_sub hint hind, hX.mean i μ, zero_sub]
  have hg : Integrable fun ω => c * |Real.sqrt N * X ω i μ| ^ (n + 1) :=
    (hX.integrable_moment (n + 1) i μ).const_mul c
  have hpt : ∀ ω, ‖A.indicator (fun ω => X ω i μ) ω‖ ≤ c * |Real.sqrt N * X ω i μ| ^ (n + 1) := by
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
      have h1 : t < |X ω i μ| := h
      have h2 : t ^ n ≤ |X ω i μ| ^ n := pow_le_pow_left₀ htpos.le h1.le n
      have htn : 0 < t ^ n := pow_pos htpos n
      have h3 : |Real.sqrt N * X ω i μ| ^ (n + 1) =
          Real.sqrt N ^ (n + 1) * (|X ω i μ| ^ n * |X ω i μ|) := by
        rw [abs_mul, abs_of_pos hs, mul_pow, pow_succ |X ω i μ| n]
      rw [h3, hc]
      have h4 : (0 : ℝ) < Real.sqrt N ^ (n + 1) := pow_pos hs _
      calc |X ω i μ| = (t ^ n)⁻¹ * (Real.sqrt N ^ (n + 1))⁻¹ *
            (Real.sqrt N ^ (n + 1) * (t ^ n * |X ω i μ|)) := by
            field_simp
        _ ≤ (t ^ n)⁻¹ * (Real.sqrt N ^ (n + 1))⁻¹ *
            (Real.sqrt N ^ (n + 1) * (|X ω i μ| ^ n * |X ω i μ|)) := by
            gcongr
    · rw [Set.indicator_of_notMem h]
      simp only [norm_zero]
      positivity
  calc |∫ ω, truncX δ X ω i μ| = ‖∫ ω, A.indicator (fun ω => X ω i μ) ω‖ := by
        rw [hmean, abs_neg, Real.norm_eq_abs]
    _ ≤ ∫ ω, c * |Real.sqrt N * X ω i μ| ^ (n + 1) :=
        norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
    _ = c * ∫ ω, |Real.sqrt N * X ω i μ| ^ (n + 1) := integral_const_mul _ _
    _ ≤ c * C (n + 1) := mul_le_mul_of_nonneg_left (hX.moment (n + 1) i μ) hcpos
    _ = C (n + 1) * (N : ℝ) ^ (-(1 / 2 : ℝ) - δ * ((n + 1 : ℕ) - 1)) := by
        rw [hcN, mul_comm]
        push_cast
        ring_nf

end E1

end Anisotropic
