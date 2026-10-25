import Anisotropic.Density.Count
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.GOEEdge
import Anisotropic.EdgeUniv.GeneralT
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Model
import Anisotropic.Instances.Models

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Corollary 3.19 (i), β = 1, for a general `T`: the comparison with the GOE and the convergence in distribution -/

/-- Corollary 3.19 (i) (`cor:TWA`), `β = 1`, for a general `T` (§11.1), the comparison form. -/
theorem twaT_cmp (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) (hcmp : HCmp1 τ l)
    (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0) (hB : ∀ x, |h x| ≤ B) (hL : LipschitzWith L h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) 1 →
      |(∫ ω, h (qVecT T (X ω) 1 l)) - (∫ ω, h (goeEdge N l ω))| ≤ ε := by
  obtain ⟨K₀, N₁, hK⟩ := edge_univT_lip τ C l hτ
  obtain ⟨N₂, hN₂⟩ := hcmp h B L hB hL (ε / 2) (half_pos hε)
  obtain ⟨N₃, hN₃⟩ := edgeRate_eventually K₀ B L l (half_pos hε)
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M K T X hm hk => ?_⟩
  have h1 := hK N (le_of_max_le_left hN) M K T X 1 hm hk h B L hB hL
  have h2 := hN₂ N (le_of_max_le_left (le_of_max_le_right hN)) M (specOf (T * Tᵀ))
    (refClass_of_isModelT hm hk)
  have h3 := hN₃ N (le_of_max_le_right (le_of_max_le_right hN))
  calc |(∫ ω, h (qVecT T (X ω) 1 l)) - (∫ ω, h (goeEdge N l ω))|
      ≤ |(∫ ω, h (qVecT T (X ω) 1 l)) - bRef N (specOf (T * Tᵀ)) 1 l h| +
        |(bRef N (specOf (T * Tᵀ)) 1 l h) - (∫ ω, h (goeEdge N l ω))| := abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- Corollary 3.19 (i) (`cor:TWA`), `β = 1`, for a general `T` (§11.1), the convergence form. -/
theorem twaT_conv (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) (hcmp : HCmp1 τ l)
    (ν : ProbabilityMeasure (Fin l → ℝ)) (htw : Tendsto (fun N => goeEdgeLaw N l) atTop (𝓝 ν))
    (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
    (Ms Ks Ns : ℕ → ℕ) (T : ∀ n, Matrix (Fin (Ms n)) (Fin (Ks n)) ℝ)
    (X : ∀ n, Ω n → Matrix (Fin (Ks n)) (Fin (Ns n)) ℝ) (hN : Tendsto Ns atTop atTop)
    (hm : ∀ n, IsModelT τ C (Ms n) (Ks n) (Ns n) (T n) (X n))
    (hk : ∀ n, RegularEdge τ (Ns n) (specOf (T n * (T n)ᵀ)) 1) :
    TendstoInDistribution (fun n ω => qVecT (T n) (X n ω) 1 l) atTop id
      (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin l → ℝ)) := by
  refine tendstoInDistribution_of_goeCmp ν htw Ns hN Ω _ (fun n => measurable_qVecT_of_entries (hm n).entries l) ?_
  intro f B L hB hL ε hε
  obtain ⟨N₀, hN₀⟩ := twaT_cmp τ C l hτ hcmp f B L hB hL ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hN.eventually (eventually_ge_atTop N₀))
  exact ⟨n₀, fun n hn => hN₀ (Ns n) (hn₀ n hn) (Ms n) (Ks n) (T n) (X n) (hm n) (hk n)⟩

/-- Corollary 3.19 (i) for a general `T` at `T = (I_{n+1}; 0)` (`Σ = T Tᵀ` singular,
`M_n = 2(n + 1)`, `K_n = n + 1`, `N_n = 2(n + 1)`): every non-external hypothesis holds;
`H_cmp¹` and the convergence `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1 (1 / 5) 1) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) =>
        qVecT (tPad (n + 1)) (radXn (n + 1) ω) 1 1)
      atTop id (fun n => (ℙ : Measure (SignSpace (Fin (n + 1) × Fin (2 * (n + 1))))))
      (ν : Measure (Fin 1 → ℝ)) := by
  have hN : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id
  exact twaT_conv (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp ν htw
    (fun n => SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (fun n => 2 * (n + 1))
    (fun n => n + 1) (fun n => 2 * (n + 1)) (fun n => tPad (n + 1)) (fun n => radXn (n + 1)) hN
    (fun n => isModelT_tPad n.succ_pos) (fun n => (mpT_hyps n.succ_pos).2.2.1)

/-- The comparison form of Corollary 3.19 (i) for a general `T` at `T = (I_{n+1}; 0)`
(`M_n = 2(n + 1)`, `K_n = n + 1`, `N_n = 2(n + 1)`, Rademacher entries) for the nonconstant bounded
Lipschitz test function `x ↦ max (-1) (min (x 0) 1)`: `E h(q_{1,1})` and `E h` of the GOE edge
vector differ by at most `ε` for all large `n`; `H_cmp¹` is a hypothesis. -/
example (hcmp : HCmp1 (1 / 5) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |(∫ ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1))),
          max (-1) (min (qVecT (tPad (n + 1)) (radXn (n + 1) ω) 1 1 0) 1)) -
        (∫ ω, max (-1) (min (goeEdge (2 * (n + 1)) 1 ω 0) 1))| ≤ ε := by
  have hB : ∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1 := fun x => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
  have hL : LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
    have h0 : LipschitzWith 1 (fun x : Fin 1 → ℝ => x 0) := LipschitzWith.eval (0 : Fin 1)
    have h1 : LipschitzWith 1 (fun x : Fin 1 → ℝ => min (x 0) 1) :=
      by simpa using h0.min (LipschitzWith.const (1 : ℝ))
    simpa using (LipschitzWith.const (-1 : ℝ)).max h1
  obtain ⟨N₀, hN₀⟩ := twaT_cmp (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp
    (fun x => max (-1) (min (x 0) 1)) 1 1 hB hL ε hε
  exact ⟨N₀, fun n hn => hN₀ (2 * (n + 1)) (by omega) (2 * (n + 1)) (n + 1) (tPad (n + 1))
    (radXn (n + 1)) (isModelT_tPad n.succ_pos) (mpT_hyps n.succ_pos).2.2.1⟩

#print axioms twaT_cmp
#print axioms twaT_conv

end Anisotropic
