module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model
public import Anisotropic.GeneralT.Model
public import Anisotropic.GeneralT.Spectra
public import Anisotropic.Instances.MarchenkoPastur
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The two model families used to instantiate the main theorems: the Rademacher `n × 2n` model under (T_diag) and `T = (I_n; 0)` with singular `Σ`, with the regularity hypotheses of the main theorems discharged -/

/-- The `n × 2n` Rademacher matrix with entries `±(2n)^{-1/2}`. -/
def radXn (n : ℕ) : SignSpace (Fin n × Fin (2 * n)) → Matrix (Fin n) (Fin (2 * n)) ℝ :=
  fun ω i μ => signVal (ω (i, μ)) / Real.sqrt (2 * n)

private theorem radXn_moment {n : ℕ} (hn : 0 < n) (p : ℕ) (i : Fin n) (μ : Fin (2 * n)) :
    (fun ω => |Real.sqrt ((2 * n : ℕ) : ℝ) * radXn n ω i μ| ^ p) = fun _ => (1 : ℝ) := by
  funext ω
  have h : Real.sqrt (2 * n) ≠ 0 := by positivity
  simp only [radXn, Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel₀ _ h, abs_signVal, one_pow]

private theorem radXn_entries {n : ℕ} (hn : 0 < n) :
    EntryAssumption (Ω := SignSpace (Fin n × Fin (2 * n))) (fun _ => 1) (radXn n) where
  measurable := fun i μ => measurable_eval_sign (i, μ) fun b => signVal b / Real.sqrt (2 * n)
  indep := iIndepFun_pi (μ := fun _ : Fin n × Fin (2 * n) => coinMeasure)
    (X := fun _ b => signVal b / Real.sqrt (2 * n)) fun _ => Measurable.of_discrete.aemeasurable
  mean := fun i μ => by
    rw [show (fun ω => radXn n ω i μ) = fun ω => signVal (ω (i, μ)) / Real.sqrt (2 * n) from rfl,
      integral_eval_sign (i, μ) fun b => signVal b / Real.sqrt (2 * n)]
    simp [signVal]
    ring
  var := fun i μ => by
    rw [show (fun ω => radXn n ω i μ ^ 2)
        = fun ω => (signVal (ω (i, μ)) / Real.sqrt (2 * n)) ^ 2 from rfl,
      integral_eval_sign (i, μ) fun b => (signVal b / Real.sqrt (2 * n)) ^ 2]
    have h2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp [signVal, div_pow]
    field_simp
    rw [h2, h3]
    ring
  integrable_moment := fun p i μ => by
    rw [radXn_moment hn]
    exact integrable_const _
  moment := fun p i μ => by
    rw [radXn_moment hn]
    simp

theorem isModel_radXn {n : ℕ} (hn : 0 < n) :
    IsModel (Ω := SignSpace (Fin n × Fin (2 * n))) (1 / 5) (fun _ => 1) n (2 * n) 1
      (radXn n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (n : ℝ) / ((2 * n : ℕ) : ℝ) = 1 / 2 := by
    push_cast
    field_simp
  refine ⟨?_, ?_, radXn_entries hn, Matrix.PosDef.one, fun i => ?_, ?_⟩
  · rw [hr]; norm_num
  · rw [hr]; norm_num
  · rw [eigenvalues_one]
    norm_num
  · have h : {i : Fin n | (Matrix.PosDef.one :
        (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).isHermitian.eigenvalues i
          ∈ Set.Icc 0 (1 / 5 : ℝ)} = ∅ := by
      ext i
      simp only [eigenvalues_one, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      norm_num
    rw [h]
    simp
    positivity

theorem specOf_one_eq (n : ℕ) : specOf (1 : Matrix (Fin n) (Fin n) ℝ) = fun _ => 1 := by
  funext i
  rw [specOf_eq Matrix.PosDef.one.isHermitian]
  exact eigenvalues_one i

/-- `T = (I_n; 0)`, an `2n × n` matrix; `Σ = T Tᵀ = diag(I_n, 0)` is singular. -/
def tPad (n : ℕ) : Matrix (Fin (2 * n)) (Fin n) ℝ := fun i j => if (i : ℕ) = j then 1 else 0

private theorem tPad_transpose_mul (n : ℕ) : (tPad n)ᵀ * tPad n = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hj : (j : ℕ) < 2 * n := by omega
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin (2 * n))]
  · simp only [tPad, Matrix.transpose_apply, ite_true, one_mul]
    by_cases h : j = k
    · subst h; simp
    · have h' : (j : ℕ) ≠ k := fun h' => h (Fin.ext h')
      simp [h, h']
  · intro i _ hi
    have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
    simp [tPad, this]
  · simp

private theorem nzEq_tPad_aux (n : ℕ) :
    NzEq (specOf (tPad n * (tPad n)ᵀ)) (fun _ : Fin n => (1 : ℝ)) := by
  have h := nzEq_specOf_mul_transpose (tPad n)
  rwa [tPad_transpose_mul, specOf_one_eq] at h

private theorem tPad_card_one (n : ℕ) :
    (Finset.univ.filter fun i => specOf (tPad n * (tPad n)ᵀ) i = 1).card = n := by
  rw [nzEq_tPad_aux n 1 one_ne_zero]
  simp

theorem isModelT_tPad {n : ℕ} (hn : 0 < n) :
    IsModelT (Ω := SignSpace (Fin n × Fin (2 * n))) (1 / 5) (fun _ => 1) (2 * n) n (2 * n)
      (tPad n) (radXn n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : ((2 * n : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  have hr' : (n : ℝ) / ((2 * n : ℕ) : ℝ) = 1 / 2 := by
    push_cast
    field_simp
  refine ⟨?_, ?_, ?_, ?_, radXn_entries hn, fun i => ?_, ?_⟩
  · rw [hr]; norm_num
  · rw [hr]; norm_num
  · rw [hr']; norm_num
  · rw [hr']; norm_num
  · by_cases h0 : specOf (tPad n * (tPad n)ᵀ) i = 0
    · rw [h0]; norm_num
    · have hc := nzEq_tPad_aux n _ h0
      have hpos : 0 < (Finset.univ.filter fun i' => specOf (tPad n * (tPad n)ᵀ) i' =
          specOf (tPad n * (tPad n)ᵀ) i).card :=
        Finset.card_pos.2 ⟨i, by simp⟩
      rw [hc] at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
      have hj' : (1 : ℝ) = specOf (tPad n * (tPad n)ᵀ) i := by simpa using (Finset.mem_filter.1 hj).2
      rw [← hj']
      norm_num
  · have hsub : {i | specOf (tPad n * (tPad n)ᵀ) i ∈ Set.Icc 0 (1 / 5 : ℝ)} ⊆
        ↑(Finset.univ.filter fun i => ¬ (specOf (tPad n * (tPad n)ᵀ) i = 1)) := by
      intro i hi
      simp only [Set.mem_Icc, Set.mem_ofPred_eq] at hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      intro h
      rw [h] at hi
      norm_num at hi
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * n))))
      (fun i => specOf (tPad n * (tPad n)ᵀ) i = 1)
    rw [tPad_card_one, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ((Finset.univ.filter fun i => ¬ (specOf (tPad n * (tPad n)ᵀ) i = 1)).card : ℝ)
        = n := by
      have : (Finset.univ.filter fun i => ¬ (specOf (tPad n * (tPad n)ᵀ) i = 1)).card = n := by
        omega
      exact_mod_cast this
    have h4 : (({i | specOf (tPad n * (tPad n)ᵀ) i ∈ Set.Icc 0 (1 / 5 : ℝ)}.ncard : ℕ) : ℝ)
        ≤ n := by
      rw [← h3]; exact_mod_cast h1
    push_cast
    linarith

theorem nzEq_tPad (n : ℕ) : NzEq (specOf (tPad n * (tPad n)ᵀ)) (fun _ : Fin n => (1 : ℝ)) :=
  nzEq_tPad_aux n

/-- The regularity hypotheses of Theorem 3.6 at `τ = 1/5` (every edge with `a_k ≥ τ/2` regular at `τ/2`) at the family. -/
theorem mp_hyps {n : ℕ} (hn : 0 < n) :
    (∀ k, 1 ≤ k → k ≤ 2 * numBands (2 * n) (fun _ : Fin n => (1 : ℝ)) →
        1 / 5 / 2 ≤ edgeVal (2 * n) (fun _ : Fin n => (1 : ℝ)) k →
        RegularEdge (1 / 5 / 2) (2 * n) (fun _ : Fin n => (1 : ℝ)) k) ∧
      (∀ k, 1 ≤ k → k ≤ numBands (2 * n) (fun _ : Fin n => (1 : ℝ)) →
        RegularBulk (fun t => min t 1 / 50) (2 * n) (fun _ : Fin n => (1 : ℝ)) k) := by
  rw [numBands_mp hn]
  refine ⟨fun k hk1 hk2 hka => ?_, fun k hk1 hk2 => ?_⟩
  · obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    · exact regularEdge_mono (regularEdge_mp hn) (by norm_num)
    · have := edgeVal_mp_two_lt hn
      exact absurd hka (by linarith)
  · obtain rfl : k = 1 := by omega
    exact regularBulk_mp hn

/-- The same hypotheses for `Σ = T Tᵀ`, `T = tPad n`. -/
theorem mpT_hyps {n : ℕ} (hn : 0 < n) :
    (∀ k, 1 ≤ k → k ≤ 2 * numBands (2 * n) (specOf (tPad n * (tPad n)ᵀ)) →
        1 / 5 / 2 ≤ edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k →
        RegularEdge (1 / 5 / 2) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k) ∧
      (∀ k, 1 ≤ k → k ≤ numBands (2 * n) (specOf (tPad n * (tPad n)ᵀ)) →
        RegularBulk (fun t => min t 1 / 50) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k) ∧
      RegularEdge (1 / 5) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 ∧
      RegularBulk (fun t => min t 1 / 50) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 := by
  have e := nzEq_tPad n
  have h := mp_hyps hn
  rw [e.numBands_eq, e.edgeVal_eq]
  refine ⟨fun k hk1 hk2 hka => (e.regularEdge_iff _ _ _).2 (h.1 k hk1 hk2 hka),
    fun k hk1 hk2 => (e.regularBulk_iff _ _ _).2 (h.2 k hk1 hk2),
    (e.regularEdge_iff _ _ _).2 (regularEdge_mp hn), (e.regularBulk_iff _ _ _).2 (regularBulk_mp hn)⟩

/-- The (T_diag) family at `n = 1` (`M = 1`, `N = 2`). -/
example : IsModel (Ω := SignSpace (Fin 1 × Fin (2 * 1))) (1 / 5) (fun _ => 1) 1 (2 * 1) 1
    (radXn 1) :=
  isModel_radXn (by norm_num)

/-- The (T_diag) family at `n = 3` (`M = 3`, `N = 6`, `Σ = I₃`). -/
example : IsModel (Ω := SignSpace (Fin 3 × Fin (2 * 3))) (1 / 5) (fun _ => 1) 3 (2 * 3) 1
    (radXn 3) :=
  isModel_radXn (by norm_num)

/-- The eigenvalues of `I₃` are all `1`. -/
example : specOf (1 : Matrix (Fin 3) (Fin 3) ℝ) = fun _ => 1 := specOf_one_eq 3

/-- The general-`T` family at `n = 3`: `M = N = 6`, `K = 3`, `Σ = diag(I₃, 0)`. -/
example : IsModelT (Ω := SignSpace (Fin 3 × Fin (2 * 3))) (1 / 5) (fun _ => 1) (2 * 3) 3 (2 * 3)
    (tPad 3) (radXn 3) :=
  isModelT_tPad (by norm_num)

/-- The nonzero spectrum of `T Tᵀ` at `n = 3` is `1` with multiplicity `3`. -/
example : NzEq (specOf (tPad 3 * (tPad 3)ᵀ)) (fun _ : Fin 3 => (1 : ℝ)) := nzEq_tPad 3

/-- The regularity hypotheses at `n = 3`, `N = 6`. -/
example := mp_hyps (n := 3) (by norm_num)

/-- The regularity hypotheses for `Σ = T Tᵀ` at `n = 3`, `N = 6`, including the top edge at
`τ = 1/5` and the bulk at the first band. -/
example :
    RegularEdge (1 / 5) (2 * 3) (specOf (tPad 3 * (tPad 3)ᵀ)) 1 ∧
      RegularBulk (fun t => min t 1 / 50) (2 * 3) (specOf (tPad 3 * (tPad 3)ᵀ)) 1 :=
  ⟨(mpT_hyps (n := 3) (by norm_num)).2.2.1, (mpT_hyps (n := 3) (by norm_num)).2.2.2⟩

end Anisotropic

#print axioms Anisotropic.isModel_radXn
#print axioms Anisotropic.specOf_one_eq
#print axioms Anisotropic.isModelT_tPad
#print axioms Anisotropic.nzEq_tPad
#print axioms Anisotropic.mp_hyps
#print axioms Anisotropic.mpT_hyps
