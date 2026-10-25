import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Stability.Domains
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.Density.Varrho
import Anisotropic.Endpoints.Main
import Anisotropic.Endpoints.Regions
import Anisotropic.Endpoints.Resolvents
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Edges
import Anisotropic.GeneralT.Main
import Anisotropic.GeneralT.Model
import Anisotropic.GeneralT.Rigidity
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.Models
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Main
import Anisotropic.Rigidity.Outside

/-! # The window `tauEdge` common to Theorem 3.14 (i)–(iii), and each main theorem instantiated at the model families -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-- The window `τ'(τ)` of Theorem 3.14, the same for items (i), (ii), (iii). -/
def tauEdge (τ : ℝ) : ℝ := min (edgeTau' τ / 2) (tauGen τ)

theorem tauEdge_pos {τ : ℝ} (hτ : 0 < τ) : 0 < tauEdge τ :=
  lt_min (half_pos (edgeTau'_pos hτ)) (div_pos (edgeTau'_pos (tauE_pos hτ)) (by norm_num))

/-- Theorem 3.14 (i) at `τ' = tauEdge τ`. -/
theorem edge_law_tauEdge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      AnisotropicLawAt N ε D Sig X (edgeDomain τ (tauEdge τ) N (specOf Sig) k) ∧
        AveragedLawAt N ε D Sig X (edgeDomain τ (tauEdge τ) N (specOf Sig) k) :=
  edge_law τ (tauEdge τ) C ε D hτ (tauEdge_pos hτ)
    ((min_le_left _ _).trans (half_le_self (edgeTau'_pos hτ).le)) hε

/-- Theorem 3.14 (ii) for a general `T` at `τ' = tauEdge τ`. -/
theorem edge_law_R_gen_tauEdge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      RNLawAt N ε D (T * Tᵀ) T X (edgeDomain τ (tauEdge τ) N (specOf (T * Tᵀ)) k) ∧
        RMLawAt N ε D (T * Tᵀ) T X (edgeDomain τ (tauEdge τ) N (specOf (T * Tᵀ)) k) :=
  edge_law_R_gen τ (tauEdge τ) C ε D hτ (tauEdge_pos hτ) (min_le_right _ _) hε

/-- Theorem 3.14 (iii) for a general `T` at `τ' = tauEdge τ`. -/
theorem rigidity_edge_gen_tauEdge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      HighProbAt N D {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2) →
        gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i ∈
          Set.Icc (edgeVal N (specOf (T * Tᵀ)) k - tauEdge τ)
            (edgeVal N (specOf (T * Tᵀ)) k + tauEdge τ) →
        |lamBandT T (X ω) ((k + 1) / 2) i - gammaBand N (specOf (T * Tᵀ)) ((k + 1) / 2) i| ≤
          rigBound N (bandNat N (specOf (T * Tᵀ)) ((k + 1) / 2)) i ε} := by
  obtain ⟨N₀, h⟩ := rigidity_edge_gen τ C ε D hτ hε
  refine ⟨N₀, fun N hN Ω _ _ M K T X k hm hk => le_trans (measure_mono ?_) (h N hN M K T X k hm hk)⟩
  intro ω hω hall
  apply hω
  intro i h1 h2 hg
  have ht : tauEdge τ ≤ tauGen τ := min_le_right _ _
  exact hall i h1 h2 ⟨by linarith [hg.1], by linarith [hg.2]⟩

section Family

/-- Theorem 3.6. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    AnisotropicLawAt (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n)
        (specDomain (1 / 5) (2 * n)) ∧
      AveragedLawAt (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n)
        (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨N₀, h⟩ := LL_G (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hh := mp_hyps hn
  rw [← specOf_one_eq n] at hh
  exact h (2 * n) hN n 1 (radXn n) (isModel_radXn hn) hh.1 hh.2

/-- Corollary 3.9 under (T_diag). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    RNLawAt (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ) (sigPow 1 (1 / 2)) (radXn n)
        (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨N₀, h⟩ := cor_GM_GN (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hh := mp_hyps hn
  rw [← specOf_one_eq n] at hh
  exact (h (2 * n) hN n 1 (radXn n) (isModel_radXn hn) hh.1 hh.2).1

/-- Theorem 3.7. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n → ∀ z : ℂ, z.re ∈ Set.Icc (1 / 5) (1 / 5)⁻¹ →
    0 < z.im → z.im ≤ (1 / 5)⁻¹ →
    ((2 * n : ℕ) : ℝ) ^ (-2 / 3 + 1 / 5 : ℝ) ≤
      Metric.infDist z.re (varrho (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ))).support →
    ODomMatAt (2 * n) 1 1 (fun ω => lawMat (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω) z)
      (fun _ => √((mFun (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) z).im /
        ((2 * n : ℕ) * z.im))) := by
  obtain ⟨N₀, h⟩ := G_outside (1 / 5) (fun _ => 1) 1 1 (by norm_num) (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hh := mp_hyps hn
  rw [← specOf_one_eq n] at hh
  exact h (2 * n) hN n 1 (radXn n) (isModel_radXn hn) hh.1

/-- Theorems 3.14 (i), 3.15 (i), 3.16 (i) and (ii) under (T_diag), 3.12, 3.14 (iii), 3.15 (iii)
under (T_diag): the hypotheses at the family. -/
example {n : ℕ} (hn : 0 < n) :
    IsModel (Ω := SignSpace (Fin n × Fin (2 * n))) (1 / 5) (fun _ => 1) n (2 * n) 1 (radXn n) ∧
      RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 ∧
      RegularBulk (fun t => min t 1 / 50) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 ∧
      (RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) (2 * 1) ∨
        RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) (2 * 1 - 1)) := by
  rw [specOf_one_eq n]
  exact ⟨isModel_radXn hn, regularEdge_mp hn, regularBulk_mp hn, Or.inr (regularEdge_mp hn)⟩

/-- Theorem 3.14 (i). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    AnisotropicLawAt (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n)
      (edgeDomain (1 / 5) (tauEdge (1 / 5)) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) := by
  obtain ⟨N₀, h⟩ := edge_law_tauEdge (1 / 5) (fun _ => 1) 1 1 (by norm_num) (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hk := regularEdge_mp hn
  rw [← specOf_one_eq n] at hk
  exact (h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk).1

/-- Theorem 3.15 (i). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    AnisotropicLawAt (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n)
      (bulkDomain (1 / 5) (1 / 10) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) := by
  obtain ⟨N₀, h⟩ := bulk_law (1 / 5) (1 / 10) (fun t => min t 1 / 50) (fun _ => 1) 1 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hk := regularBulk_mp hn
  rw [← specOf_one_eq n] at hk
  exact (h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk).1

/-- Theorem 3.12 under (T_diag). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    HighProbAt (2 * n) 1 {ω | ∀ k, 1 ≤ k → k ≤ numBands (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) k →
        1 / 5 ≤ gammaBand (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) k i →
          |lamBand 1 (radXn n ω) k i - gammaBand (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) k i| ≤
            rigBound (2 * n) (bandNat (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) k) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hh := mp_hyps hn
  rw [← specOf_one_eq n] at hh
  exact h (2 * n) hN n 1 (radXn n) (isModel_radXn hn) hh.1 hh.2

/-- Proposition 11.1 (general `T`, singular `Σ`, `M̂ < M`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    AnisotropicLawTAt (2 * n) 1 1 (tPad n) (radXn n) (specDomain (1 / 5) (2 * n)) ∧
      AveragedLawTAt (2 * n) 1 1 (tPad n) (radXn n) (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨N₀, h⟩ := LL_G_gen (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun n hn hN => h (2 * n) hN (2 * n) n (tPad n) (radXn n) (isModelT_tPad hn)
    (mpT_hyps hn).1 (mpT_hyps hn).2.1⟩

/-- Corollary 3.9 (general `T`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    RMLawAt (2 * n) 1 1 (tPad n * (tPad n)ᵀ) (tPad n) (radXn n) (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨N₀, h⟩ := cor_GM_GN_gen (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun n hn hN => (h (2 * n) hN (2 * n) n (tPad n) (radXn n) (isModelT_tPad hn)
    (mpT_hyps hn).1 (mpT_hyps hn).2.1).2.1⟩

/-- Theorem 3.12 (general `T`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    HighProbAt (2 * n) 1 {ω | ∀ k, 1 ≤ k → k ≤ numBands (2 * n) (specOf (tPad n * (tPad n)ᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k →
        1 / 5 ≤ gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k i →
          |lamBandT (tPad n) (radXn n ω) k i - gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k i| ≤
            rigBound (2 * n) (bandNat (2 * n) (specOf (tPad n * (tPad n)ᵀ)) k) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_gen (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun n hn hN => h (2 * n) hN (2 * n) n (tPad n) (radXn n) (isModelT_tPad hn)
    (mpT_hyps hn).1 (mpT_hyps hn).2.1⟩

/-- Theorem 3.14 (ii), (iii) (general `T`, one window `tauEdge`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    RNLawAt (2 * n) 1 1 (tPad n * (tPad n)ᵀ) (tPad n) (radXn n)
        (edgeDomain (1 / 5) (tauEdge (1 / 5)) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) ∧
      HighProbAt (2 * n) 1 {ω | ∀ i, 1 ≤ i →
        i ≤ bandNat (2 * n) (specOf (tPad n * (tPad n)ᵀ)) ((1 + 1) / 2) →
        gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) ((1 + 1) / 2) i ∈
          Set.Icc (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 - tauEdge (1 / 5))
            (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 + tauEdge (1 / 5)) →
        |lamBandT (tPad n) (radXn n ω) ((1 + 1) / 2) i -
            gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) ((1 + 1) / 2) i| ≤
          rigBound (2 * n) (bandNat (2 * n) (specOf (tPad n * (tPad n)ᵀ)) ((1 + 1) / 2)) i 1} := by
  obtain ⟨N₁, h₁⟩ := edge_law_R_gen_tauEdge (1 / 5) (fun _ => 1) 1 1 (by norm_num) (by norm_num)
  obtain ⟨N₂, h₂⟩ := rigidity_edge_gen_tauEdge (1 / 5) (fun _ => 1) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨max N₁ N₂, fun n hn hN =>
    ⟨(h₁ (2 * n) (le_of_max_le_left hN) (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn)
      (mpT_hyps hn).2.2.1).1,
     h₂ (2 * n) (le_of_max_le_right hN) (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn)
      (mpT_hyps hn).2.2.1⟩⟩

/-- Theorem 3.15 (ii), (iii) (general `T`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    RNLawAt (2 * n) 1 1 (tPad n * (tPad n)ᵀ) (tPad n) (radXn n)
        (bulkDomain (1 / 5) (1 / 10) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1) ∧
      HighProbAt (2 * n) 1 {ω | ∀ i, 1 ≤ i → i ≤ bandNat (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 →
        gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 i ∈
          Set.Icc (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) (2 * 1) + 1 / 10)
            (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) (2 * 1 - 1) - 1 / 10) →
        |lamBandT (tPad n) (radXn n ω) 1 i - gammaBand (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 i| ≤
          ((2 * n : ℕ) : ℝ) ^ (1 : ℝ) * ((2 * n : ℕ) : ℝ)⁻¹} := by
  obtain ⟨N₁, h₁⟩ := bulk_law_R_gen (1 / 5) (1 / 10) (fun t => min t 1 / 50) (fun _ => 1) 1 1
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨N₂, h₂⟩ := rigidity_bulk_gen (1 / 5) (1 / 10) (fun t => min t 1 / 50) (fun _ => 1) 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨max N₁ N₂, fun n hn hN =>
    ⟨(h₁ (2 * n) (le_of_max_le_left hN) (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn)
      (mpT_hyps hn).2.2.2).1,
     h₂ (2 * n) (le_of_max_le_right hN) (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn)
      (mpT_hyps hn).2.2.2 (Or.inr (mpT_hyps hn).2.2.1)⟩⟩

/-- Theorem 3.16 (ii) (general `T`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    RMLawAt (2 * n) 1 1 (tPad n * (tPad n)ᵀ) (tPad n) (radXn n)
      (outsideDomain (1 / 5) (1 / 10) (2 * n) (specOf (tPad n * (tPad n)ᵀ))) := by
  obtain ⟨N₀, h⟩ := outside_law_R_gen (1 / 5) (1 / 10) (fun _ => 1) 1 1 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨N₀, fun n hn hN => (h (2 * n) hN (2 * n) n (tPad n) (radXn n) (isModelT_tPad hn)).2⟩

end Family

end Anisotropic
