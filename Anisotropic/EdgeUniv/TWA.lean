module

public import Anisotropic.Density.Count
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.GOEEdge
public import Anisotropic.EdgeUniv.Main
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Instances.MarchenkoPastur
public import Anisotropic.Instances.Models

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Corollary 3.19 (i), β = 1, under (T_diag): the comparison with the GOE and the convergence in distribution -/

/-- Corollary 3.19 (i) (`cor:TWA`), `β = 1`, under (T_diag), the comparison form: under
`H_cmp¹`, for bounded Lipschitz `h`, `E h(q_{1,l})` and `E h` of the GOE edge vector differ by
at most `ε` for `N ≥ N₀`, uniformly over the models with edge `1` regular. -/
theorem twa_cmp (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) (hcmp : HCmp1 τ l)
    (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0) (hB : ∀ x, |h x| ≤ B) (hL : LipschitzWith L h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) 1 →
      |(∫ ω, h (qVec Sig (X ω) 1 l)) - (∫ ω, h (goeEdge N l ω))| ≤ ε := by
  obtain ⟨K, N₁, hK⟩ := edge_univ_lip τ C l hτ
  obtain ⟨N₂, hN₂⟩ := hcmp h B L hB hL (ε / 2) (half_pos hε)
  obtain ⟨N₃, hN₃⟩ := edgeRate_eventually K B L l (half_pos hε)
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M Sig X hm hk => ?_⟩
  have h1 := hK N (le_of_max_le_left hN) M Sig X 1 hm hk h B L hB hL
  have h2 := hN₂ N (le_of_max_le_left (le_of_max_le_right hN)) M (specOf Sig)
    (refClass_of_isModel hm hk)
  have h3 := hN₃ N (le_of_max_le_right (le_of_max_le_right hN))
  calc |(∫ ω, h (qVec Sig (X ω) 1 l)) - (∫ ω, h (goeEdge N l ω))|
      ≤ |(∫ ω, h (qVec Sig (X ω) 1 l)) - bRef N (specOf Sig) 1 l h| +
        |(bRef N (specOf Sig) 1 l h) - (∫ ω, h (goeEdge N l ω))| := abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- Corollary 3.19 (i) (`cor:TWA`), `β = 1`, under (T_diag), the convergence form: under
`H_cmp¹` and `γ_N → ν` (`H_TW¹` with limit `ν = q_l^1`), along every sequence of models with
`N_n → ∞` and edge `1` regular, `q_{1,l}` converges in distribution to `ν`. -/
theorem twa_conv (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) (hcmp : HCmp1 τ l)
    (ν : ProbabilityMeasure (Fin l → ℝ)) (htw : Tendsto (fun N => goeEdgeLaw N l) atTop (𝓝 ν))
    (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
    (Ms Ns : ℕ → ℕ) (Sig : ∀ n, Matrix (Fin (Ms n)) (Fin (Ms n)) ℝ)
    (X : ∀ n, Ω n → Matrix (Fin (Ms n)) (Fin (Ns n)) ℝ) (hN : Tendsto Ns atTop atTop)
    (hm : ∀ n, IsModel τ C (Ms n) (Ns n) (Sig n) (X n))
    (hk : ∀ n, RegularEdge τ (Ns n) (specOf (Sig n)) 1) :
    TendstoInDistribution (fun n ω => qVec (Sig n) (X n ω) 1 l) atTop id
      (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin l → ℝ)) := by
  refine tendstoInDistribution_of_goeCmp ν htw Ns hN Ω _ (fun n => measurable_qVec_of_entries (hm n).entries l) ?_
  intro f B L hB hL ε hε
  obtain ⟨N₀, hN₀⟩ := twa_cmp τ C l hτ hcmp f B L hB hL ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hN.eventually (eventually_ge_atTop N₀))
  exact ⟨n₀, fun n hn => hN₀ (Ns n) (hn₀ n hn) (Ms n) (Sig n) (X n) (hm n) (hk n)⟩

/-- Corollary 3.19 (i) under (T_diag) with `H_TW¹` in its existential form: there is one
`q_l^1`, the limit of the GOE edge laws, to which `q_{1,l}` converges along every sequence. -/
example (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) (hcmp : HCmp1 τ l) (htw : HTW1 l) :
    ∃ ν : ProbabilityMeasure (Fin l → ℝ), Tendsto (fun N => goeEdgeLaw N l) atTop (𝓝 ν) ∧
      ∀ (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
        (Ms Ns : ℕ → ℕ) (Sig : ∀ n, Matrix (Fin (Ms n)) (Fin (Ms n)) ℝ)
        (X : ∀ n, Ω n → Matrix (Fin (Ms n)) (Fin (Ns n)) ℝ), Tendsto Ns atTop atTop →
        (∀ n, IsModel τ C (Ms n) (Ns n) (Sig n) (X n)) →
        (∀ n, RegularEdge τ (Ns n) (specOf (Sig n)) 1) →
        TendstoInDistribution (fun n ω => qVec (Sig n) (X n ω) 1 l) atTop id
          (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin l → ℝ)) := by
  obtain ⟨ν, hν⟩ := htw
  exact ⟨ν, hν, fun Ω _ _ Ms Ns Sig X hN hm hk => twa_conv τ C l hτ hcmp ν hν Ω Ms Ns Sig X hN hm hk⟩

/-- Corollary 3.19 (i) under (T_diag) at the Marchenko–Pastur point (`Σ = I`, `M_n = n + 1`,
`N_n = 2(n + 1)`, Rademacher entries): every non-external hypothesis holds; `H_cmp¹` and the
convergence `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1 (1 / 5) 1) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) =>
        qVec (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (radXn (n + 1) ω) 1 1)
      atTop id (fun n => (ℙ : Measure (SignSpace (Fin (n + 1) × Fin (2 * (n + 1))))))
      (ν : Measure (Fin 1 → ℝ)) := by
  have hN : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id
  refine twa_conv (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp ν htw
    (fun n => SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (fun n => n + 1)
    (fun n => 2 * (n + 1)) (fun n => 1) (fun n => radXn (n + 1)) hN
    (fun n => isModel_radXn n.succ_pos) (fun n => ?_)
  rw [specOf_one_eq]
  exact regularEdge_mp n.succ_pos

/-- The comparison form of Corollary 3.19 (i) at the Marchenko–Pastur point (`Σ = I`,
`M_n = n + 1`, `N_n = 2(n + 1)`, Rademacher entries) for the nonconstant bounded Lipschitz test
function `x ↦ max (-1) (min (x 0) 1)`: `E h(q_{1,1})` and `E h` of the GOE edge vector differ by
at most `ε` for all large `n`; `H_cmp¹` is a hypothesis. -/
example (hcmp : HCmp1 (1 / 5) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |(∫ ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1))),
          max (-1) (min (qVec (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (radXn (n + 1) ω) 1 1 0) 1)) -
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
  obtain ⟨N₀, hN₀⟩ := twa_cmp (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp
    (fun x => max (-1) (min (x 0) 1)) 1 1 hB hL ε hε
  refine ⟨N₀, fun n hn => hN₀ (2 * (n + 1)) (by omega) (n + 1) 1 (radXn (n + 1))
    (isModel_radXn n.succ_pos) ?_⟩
  rw [specOf_one_eq]
  exact regularEdge_mp n.succ_pos

#print axioms twa_cmp
#print axioms twa_conv

end Anisotropic
