module

public import Anisotropic

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `Anisotropic` named in its proof. The
definitions that occur in the statements are those of `Anisotropic/MainDefs.lean`.
-/

section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}

/-- Theorem 3.6, the anisotropic local law (edge_G_result) and the averaged local law (edge_G_avg_result) on the domain `𝐃(τ, N)`, under (T_diag), at fixed `N ≥ N₀`. -/
theorem thm_3_6 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      AnisotropicLawAt N ε D Sig X (specDomain τ N) ∧
        AveragedLawAt N ε D Sig X (specDomain τ N) :=
  LL_G τ C c ε D hτ hε

/-- Theorem 3.7, the anisotropic local law outside the spectrum. -/
theorem thm_3_7 (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      ∀ z : ℂ, z.re ∈ Set.Icc τ τ⁻¹ → 0 < z.im → z.im ≤ τ⁻¹ →
        (N : ℝ) ^ (-2 / 3 + τ) ≤ Metric.infDist z.re (varrho N (specOf Sig)).support →
        ODomMatAt N ε D (fun ω => lawMat Sig (X ω) z)
          (fun _ => √((mFun N (specOf Sig) z).im / (N * z.im))) :=
  G_outside τ C ε D hτ hε

/-- Corollary 3.9, for general `T`. -/
theorem cor_3_9 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      RNLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        RMLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) :=
  cor_GM_GN_gen τ C c ε D hτ hε

/-- Theorem 3.12, rigidity of the eigenvalues, for general `T`. -/
theorem thm_3_12 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k → τ ≤ gammaBand N (specOf (T * Tᵀ)) k i →
          |lamBandT T (X ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
            rigBound N (bandNat N (specOf (T * Tᵀ)) k) i ε} :=
  rigidity_gen τ C c ε D hτ hε

/-- Theorem 3.18, edge universality, for general `T` and bounded uniformly continuous test functions. -/
theorem thm_3_18 (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      |(∫ ω, h (qVecT T (X ω) k l)) - bRef N (specOf (T * Tᵀ)) k l h| ≤ ε :=
  edge_univT τ C l h ε hτ hb hu hε

/-- Proposition 11.1, the local laws for general `T`. -/
theorem prop_11_1 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      AnisotropicLawTAt N ε D T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) :=
  LL_G_gen τ C c ε D hτ hε

/-- Theorem 12.2, the anisotropic local law for deformed Wigner matrices. -/
theorem thm_12_2_aniso (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AnisotropicLawWAt N ε D A W S :=
  general_wig_aniso τ c₀ C ε D hτ hc₀ hε

/-- Theorem 12.2, the averaged local law for deformed Wigner matrices. -/
theorem thm_12_2_avg (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε D A W S :=
  general_wig_avg τ c₀ C ε D hτ hc₀ hε

/-- Theorem 12.4, rigidity of the extreme eigenvalues of deformed Wigner matrices. -/
theorem thm_12_4 (τA : ℝ) (C : ℕ → ℝ) (τ₀ ε D : ℝ) (hτA : 0 < τA) (hτ₀ : 0 < τ₀)
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      WignerModel τA C N A W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      RigidExtremesWAt N ε D (specOf A) (fun ω => W ω + A) :=
  wigner_rig τA C τ₀ ε D hτA hτ₀ hε

/-- Theorem 12.5, edge universality for deformed Wigner matrices. -/
theorem thm_12_5 (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ) (hτA : 0 < τA)
    (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (f : (Fin l → ℝ) → ℝ) (B L : ℝ), ContDiff ℝ 1 f → (∀ x, |f x| ≤ B) →
        (∀ x, ‖fderiv ℝ f x‖ ≤ L) → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
        WignerModel τA C N A W →
        StandingBoundW τ (specOf A) (domW τ N) →
        EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
        AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
        RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
        |(∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (W ω + A) (i + 1) - LpW (specOf A)))) -
          (∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (goeW N ω + diagonal (specOf A)) (i + 1) - LpW (specOf A))))| ≤
          (N : ℝ) ^ (-c₀) :=
  wigner_edge_univ τA C τ₀ l hτA hτ₀

end Anisotropic
end
