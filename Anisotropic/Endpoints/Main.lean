module

public import Anisotropic.Averaged.Defs
public import Anisotropic.Averaged.Main
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Bulk
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Density.Stability.EdgeSqRoot
public import Anisotropic.Density.Stability.EdgeStab
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Density.Stability.Outside
public import Anisotropic.Density.Stability.Quadratic
public import Anisotropic.Endpoints.Regions
public import Anisotropic.Endpoints.Resolvents
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Gaussian.Ensemble
public import Anisotropic.Gaussian.Spectral
public import Anisotropic.Probability.NormBound.GaussianLower

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorems 3.14 (i), 3.15 (i), 3.16 (i), Theorem 3.6, and Corollary 3.9 and Theorems 3.14–3.16 (ii) under (T_diag) -/

/-- Theorem 3.14 (i) (`thm:edge`) at fixed `N`, under (T_diag): for a regular edge `k`, the
anisotropic and averaged laws hold on `𝐃^e_k(τ, τ'', N)` for every `τ'' ∈ (0, τ'(τ)]`,
`τ'(τ) = edgeTau' τ`; `N₀` is uniform in `k` and in the model. -/
theorem edge_law (τ τ'' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ'' : 0 < τ'')
    (hτ''τ : τ'' ≤ edgeTau' τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      AnisotropicLawAt N ε D Sig X (edgeDomain τ τ'' N (specOf Sig) k) ∧
        AveragedLawAt N ε D Sig X (edgeDomain τ τ'' N (specOf Sig) k) := by
  have hC : 0 < mBoundConst τ := mBoundConst_pos hτ
  have hmz : 0 < edgeMz τ := lt_min (half_pos hτ) (div_pos (edgeTau'_pos hτ) hC)
  have hc : 0 < oneXmConst (edgeMz τ) (mBoundConst τ) :=
    lt_min (by norm_num) (div_pos hmz (by linarith))
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ _ C ε D hτ hc hε
  obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ _ C ε D hτ hc hε
  obtain ⟨N₃, h₃⟩ := gauss_avg_input τ _ (edgeC0wmin τ) (edgeC1w τ (edgeC0wmin τ))
    (edgeK0w τ (edgeC0wmin τ)) ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := gauss_avg_input τ _ (edgeC0wmin τ) (edgeC1w τ (edgeC0wmin τ))
    (edgeK0w τ (edgeC0wmin τ)) ε₂ D₂ hτ hc hε₂
  obtain ⟨N₅, h₅⟩ := stab_edge2_weak (τ := τ) (C₀ := edgeC0wmin τ) hτ'' hτ''τ le_rfl
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hS := spectralDomain_edgeDomain τ τ'' N (specOf Sig) k
  have hx : OneXmOn (oneXmConst (edgeMz τ) (mBoundConst τ)) N (specOf Sig)
      (edgeDomain τ τ'' N (specOf Sig) k) := fun z hz i =>
    one_add_mul_mFun_edge hda hk hτ''τ hz i
  have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) k hda hk
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm hS hx g₁.1,
    h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm hS hx g₂.1
      (averagedPhiLawAt_inv_iff.1 g₂.2)⟩

/-- Theorem 3.15 (i) (`thm:bulk`) at fixed `N`, under (T_diag): for a regular bulk component
`k` (with the function `c`), the laws hold on `𝐃^b_k(τ, τ', N)`. -/
theorem bulk_law (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularBulk c N (specOf Sig) k →
      AnisotropicLawAt N ε D Sig X (bulkDomain τ τ' N (specOf Sig) k) ∧
        AveragedLawAt N ε D Sig X (bulkDomain τ τ' N (specOf Sig) k) := by
  by_cases hcb : 0 < c (τ' / 2)
  · have hC : 0 < mBoundConst τ := mBoundConst_pos hτ
    have hb : 0 < bulkcb τ τ' c :=
      mul_pos (mul_pos two_pos hcb) (Real.arctan_pos.2 (by positivity))
    have hc : 0 < oneXmConst (bulkcb τ τ' c) (mBoundConst τ) :=
      lt_min (by norm_num) (div_pos hb (by linarith))
    obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ _ C ε D hτ hc hε
    obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ _ C ε D hτ hc hε
    obtain ⟨N₃, h₃⟩ := gauss_avg_input τ _ (bulkC0wmin τ τ' c) (bulkC0wmin τ τ' c) 0 ε₁ D₁ hτ
      hc hε₁
    obtain ⟨N₄, h₄⟩ := gauss_avg_input τ _ (bulkC0wmin τ τ' c) (bulkC0wmin τ τ' c) 0 ε₂ D₂ hτ
      hc hε₂
    obtain ⟨N₅, h₅⟩ := stab_bulk_weak (τ := τ) (τ' := τ') (c := c) (C₀ := bulkC0wmin τ τ' c)
      (C₁ := bulkC0wmin τ τ' c) (K₀ := 0) hτ' le_rfl
    refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
    have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
    have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
    have hN1 : 1 ≤ N := le_of_max_le_right hB
    have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
    have hS := spectralDomain_bulkDomain τ τ' N (specOf Sig) k
    have hx : OneXmOn (oneXmConst (bulkcb τ τ' c) (mBoundConst τ)) N (specOf Sig)
        (bulkDomain τ τ' N (specOf Sig) k) := fun z hz =>
      one_add_mul_ge_of_mz_reg hda.nonneg hb hC (gen_prop_m_specDomain hda hz.1).2.1
        (mz_reg_bulk hda hk hτ' hz)
    have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) k hda hk
    have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
      isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
    have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
    have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
    exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm hS hx g₁.1,
      h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm hS hx g₂.1
        (averagedPhiLawAt_inv_iff.1 g₂.2)⟩
  · exact ⟨0, fun N _ Ω _ _ M Sig X k _ hk =>
      absurd ((hk.2.2 (τ' / 2) (half_pos hτ')).1) hcb⟩

/-- Theorem 3.16 (i) (`thm:outside`) at fixed `N`, under (T_diag): the laws hold on
`𝐃^o(τ, τ', N)`. -/
theorem outside_law (τ τ' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      AnisotropicLawAt N ε D Sig X (outsideDomain τ τ' N (specOf Sig)) ∧
        AveragedLawAt N ε D Sig X (outsideDomain τ τ' N (specOf Sig)) := by
  have hC : 0 < mBoundConst τ := mBoundConst_pos hτ
  have hb : 0 < outMz τ τ' := by
    unfold outMz outcr outImLower
    positivity
  have hc : 0 < oneXmConst (outMz τ τ') (mBoundConst τ) :=
    lt_min (by norm_num) (div_pos hb (by linarith))
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ _ C ε D hτ hc hε
  obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ _ C ε D hτ hc hε
  obtain ⟨N₃, h₃⟩ := gauss_avg_input τ _ (outC0wmin τ τ') (outC0wmin τ τ') 0 ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := gauss_avg_input τ _ (outC0wmin τ τ') (outC0wmin τ τ') 0 ε₂ D₂ hτ hc hε₂
  obtain ⟨N₅, h₅⟩ := stab_outside_weak (τ := τ) (τ' := τ') (C₀ := outC0wmin τ τ')
    (C₁ := outC0wmin τ τ') (K₀ := 0) hτ' le_rfl
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), fun N hN Ω _ _ M Sig X hm => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hS := spectralDomain_outsideDomain τ τ' N (specOf Sig)
  have hx : OneXmOn (oneXmConst (outMz τ τ') (mBoundConst τ)) N (specOf Sig)
      (outsideDomain τ τ' N (specOf Sig)) := fun z hz =>
    one_add_mul_ge_of_mz_reg hda.nonneg hb hC (gen_prop_m_specDomain hda hz.1).2.1
      (mz_reg_outside hda hτ' hz)
  have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) hda
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm hS hx g₁.1,
    h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm hS hx g₂.1
      (averagedPhiLawAt_inv_iff.1 g₂.2)⟩

/-- The laws on the large-`η` domain `{z ∈ 𝐃(τ, N) : η ≥ τ/2}` (no regularity). -/
theorem high_law (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      AnisotropicLawAt N ε D Sig X (highDomain τ N) ∧
        AveragedLawAt N ε D Sig X (highDomain τ N) := by
  have hc : 0 < highc τ := highc_pos hτ
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ (highc τ) C ε D hτ hc hε
  obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ (highc τ) C ε D hτ hc hε
  obtain ⟨N₃, h₃⟩ := gauss_avg_input τ (highc τ) (highC τ) (highC τ) 0 ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := gauss_avg_input τ (highc τ) (highC τ) (highC τ) 0 ε₂ D₂ hτ hc hε₂
  obtain ⟨N₅, h₅⟩ := stab_high τ hτ
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), fun N hN Ω _ _ M Sig X hm => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hS := spectralDomain_highDomain τ N
  have hx : OneXmOn (highc τ) N (specOf Sig) (highDomain τ N) := oneXm_high hda
  have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) hda
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm hS hx g₁.1,
    h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm hS hx g₂.1
      (averagedPhiLawAt_inv_iff.1 g₂.2)⟩

/-- Theorem 3.6 (`thm:LL_G`) at fixed `N`, under (T_diag): if every edge `k` with `a_k ≥ τ/2` is
regular (Definition 2.7 (i)) with parameter `τ/2` and every bulk component is regular
(Definition 2.7 (ii), function `c`), then (edge_G_result) and (edge_G_avg_result) hold on
`𝐃(τ, N)`. -/
theorem LL_G (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      AnisotropicLawAt N ε D Sig X (specDomain τ N) ∧
        AveragedLawAt N ε D Sig X (specDomain τ N) := by
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hτ' : 0 < coverTau τ := coverTau_pos hτ
  have hτ'e : coverTau τ ≤ edgeTau' (τ / 2) := min_le_left _ _
  obtain ⟨N₁, h₁⟩ := edge_law (τ / 2) (coverTau τ) C ε D hτ2 hτ' hτ'e hε
  obtain ⟨N₂, h₂⟩ := bulk_law (τ / 2) (coverTau τ) c C ε D hτ2 hτ' hε
  obtain ⟨N₃, h₃⟩ := outside_law (τ / 2) (coverTau τ) C ε D hτ2 hτ' hε
  obtain ⟨N₄, h₄⟩ := high_law τ C ε D hτ hε
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) 1, fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hm2 : IsModel (τ / 2) C M N Sig X := hm.mono hτ2 (by linarith)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have key : ∀ z ∈ specDomain τ N,
      ODomMatAt N ε D (fun ω => lawMat Sig (X ω) z) (fun _ => Psi N (specOf Sig) z) ∧
        ODomAt N ε D (fun ω => mN Sig (X ω) z - mFun N (specOf Sig) z)
          (fun _ => 1 / (N * z.im)) := by
    intro z hz
    rcases specDomain_cover hτ hN1 hda hz with hh | ho | ⟨k, hk1, hk2, hb⟩ |
      ⟨l, hl1, hl2, hla, he⟩
    · have e := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig X hm
      exact ⟨e.1 z hh, e.2 z hh⟩
    · have e := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig X hm2
      exact ⟨e.1 z ho, e.2 z ho⟩
    · have e := h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X k hm2
        (hbulk k hk1 hk2)
      exact ⟨e.1 z hb, e.2 z hb⟩
    · have e := h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X l hm2
        (hedge l hl1 hl2 hla)
      exact ⟨e.1 z he, e.2 z he⟩
  exact ⟨fun z hz => (key z hz).1, fun z hz => (key z hz).2⟩

/-- Corollary 3.9 (`cor:GM_GN`) at fixed `N`, under (T_diag) (`T = Σ^{1/2}`) and the edge
hypothesis at `τ/2`: (R_N_edge), (R_M_edge) and (edge_G_avg_result) on `𝐃(τ, N)`. -/
theorem cor_GM_GN (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      RNLawAt N ε D Sig (sigPow Sig (1 / 2)) X (specDomain τ N) ∧
        RMLawAt N ε D Sig (sigPow Sig (1 / 2)) X (specDomain τ N) ∧
        AveragedLawAt N ε D Sig X (specDomain τ N) := by
  obtain ⟨N₁, h₁⟩ := LL_G τ C c (ε / 2) D hτ (half_pos hε)
  obtain ⟨N₂, h₂⟩ := LL_G τ C c ε D hτ hε
  refine ⟨max (max N₁ N₂) (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1),
    fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  have hA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  have hr := rLaws_of_aniso hτ (le_of_max_le_right hB) hm.sigma.posDef subset_rfl
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB))
    (h₁ N (le_of_max_le_left hA) M Sig X hm hedge hbulk).1
  exact ⟨hr.1, hr.2, (h₂ N (le_of_max_le_right hA) M Sig X hm hedge hbulk).2⟩

/-- Theorem 3.14 (ii) (`thm:edge`) under (T_diag): (R_N_edge), (R_M_edge) on `𝐃^e_k`. -/
theorem edge_law_R (τ τ'' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ'' : 0 < τ'')
    (hτ''τ : τ'' ≤ edgeTau' τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      RNLawAt N ε D Sig (sigPow Sig (1 / 2)) X (edgeDomain τ τ'' N (specOf Sig) k) ∧
        RMLawAt N ε D Sig (sigPow Sig (1 / 2)) X (edgeDomain τ τ'' N (specOf Sig) k) := by
  obtain ⟨N₁, h₁⟩ := edge_law τ τ'' C (ε / 2) D hτ hτ'' hτ''τ (half_pos hε)
  refine ⟨max N₁ (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  exact rLaws_of_aniso hτ (le_of_max_le_right hB) hm.sigma.posDef (by intro z hz; exact hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB))
    (S := _) (h₁ N (le_of_max_le_left hN) M Sig X k hm hk).1

/-- Theorem 3.15 (ii) (`thm:bulk`) under (T_diag): (R_N_edge), (R_M_edge) on `𝐃^b_k`. -/
theorem bulk_law_R (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularBulk c N (specOf Sig) k →
      RNLawAt N ε D Sig (sigPow Sig (1 / 2)) X (bulkDomain τ τ' N (specOf Sig) k) ∧
        RMLawAt N ε D Sig (sigPow Sig (1 / 2)) X (bulkDomain τ τ' N (specOf Sig) k) := by
  obtain ⟨N₁, h₁⟩ := bulk_law τ τ' c C (ε / 2) D hτ hτ' (half_pos hε)
  refine ⟨max N₁ (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  exact rLaws_of_aniso hτ (le_of_max_le_right hB) hm.sigma.posDef (by intro z hz; exact hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB))
    (S := _) (h₁ N (le_of_max_le_left hN) M Sig X k hm hk).1

/-- Theorem 3.16 (ii) (`thm:outside`) under (T_diag): (R_N_edge), (R_M_edge) on `𝐃^o`. -/
theorem outside_law_R (τ τ' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      RNLawAt N ε D Sig (sigPow Sig (1 / 2)) X (outsideDomain τ τ' N (specOf Sig)) ∧
        RMLawAt N ε D Sig (sigPow Sig (1 / 2)) X (outsideDomain τ τ' N (specOf Sig)) := by
  obtain ⟨N₁, h₁⟩ := outside_law τ τ' C (ε / 2) D hτ hτ' (half_pos hε)
  refine ⟨max N₁ (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M Sig X hm => ?_⟩
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  exact rLaws_of_aniso hτ (le_of_max_le_right hB) hm.sigma.posDef (by intro z hz; exact hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB))
    (S := _) (h₁ N (le_of_max_le_left hN) M Sig X hm).1

/-! ## Conditional instances

Each theorem above is an `∃ N₀` statement with Prop hypotheses, so its instance below keeps the
hypotheses as binders. For the Gaussian model `X = gaussX M N` the hypotheses on the bulk use the
constant `c t = min t 1 / 50`; the bulk hypothesis is satisfiable by the Marchenko–Pastur law
with `φ = 1/2`, `σ ≡ 1`, since there `ρ(E) ≥ 0.0649 √t ≥ min t 1 / 50` on `[a₂ + t, a₁ − t]`. -/

/-- Theorem 3.14 (i) at `τ = 1/5`, `τ'' = edgeTau' (1/5)`, `C = gaussMoment`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) → RegularEdge (1 / 5) N (specOf Sig) k →
    AnisotropicLawAt N 1 1 Sig (gaussX M N)
        (edgeDomain (1 / 5) (edgeTau' (1 / 5)) N (specOf Sig) k) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N)
        (edgeDomain (1 / 5) (edgeTau' (1 / 5)) N (specOf Sig) k) := by
  obtain ⟨N₀, h⟩ := edge_law (1 / 5) (edgeTau' (1 / 5)) gaussMoment 1 1 (by norm_num)
    (edgeTau'_pos (by norm_num)) le_rfl (by norm_num)
  exact ⟨N₀, fun N hN M Sig k hm hk => h N hN M Sig (gaussX M N) k hm hk⟩

/-- Theorem 3.15 (i) at `τ = 1/5`, `τ' = 1/10`, `c t = min t 1 / 50`, `C = gaussMoment`,
`ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k →
    AnisotropicLawAt N 1 1 Sig (gaussX M N) (bulkDomain (1 / 5) (1 / 10) N (specOf Sig) k) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N) (bulkDomain (1 / 5) (1 / 10) N (specOf Sig) k) := by
  obtain ⟨N₀, h⟩ := bulk_law (1 / 5) (1 / 10) (fun t => min t 1 / 50) gaussMoment 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig k hm hk => h N hN M Sig (gaussX M N) k hm hk⟩

/-- Theorem 3.16 (i) at `τ = 1/5`, `τ' = 1/10`, `C = gaussMoment`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    AnisotropicLawAt N 1 1 Sig (gaussX M N) (outsideDomain (1 / 5) (1 / 10) N (specOf Sig)) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N) (outsideDomain (1 / 5) (1 / 10) N (specOf Sig)) := by
  obtain ⟨N₀, h⟩ := outside_law (1 / 5) (1 / 10) gaussMoment 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm => h N hN M Sig (gaussX M N) hm⟩

/-- The large-`η` law at `τ = 1/5`, `C = gaussMoment`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    AnisotropicLawAt N 1 1 Sig (gaussX M N) (highDomain (1 / 5) N) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N) (highDomain (1 / 5) N) := by
  obtain ⟨N₀, h⟩ := high_law (1 / 5) gaussMoment 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm => h N hN M Sig (gaussX M N) hm⟩

/-- Theorem 3.6 at `τ = 1/5`, `C = gaussMoment`, `c t = min t 1 / 50`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → 1 / 5 / 2 ≤ edgeVal N (specOf Sig) k →
      RegularEdge (1 / 5 / 2) N (specOf Sig) k) →
    (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
      RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k) →
    AnisotropicLawAt N 1 1 Sig (gaussX M N) (specDomain (1 / 5) N) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N) (specDomain (1 / 5) N) := by
  obtain ⟨N₀, h⟩ := LL_G (1 / 5) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm he hb => h N hN M Sig (gaussX M N) hm he hb⟩

/-- Corollary 3.9 at `τ = 1/5`, `C = gaussMoment`, `c t = min t 1 / 50`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → 1 / 5 / 2 ≤ edgeVal N (specOf Sig) k →
      RegularEdge (1 / 5 / 2) N (specOf Sig) k) →
    (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
      RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k) →
    RNLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N) (specDomain (1 / 5) N) ∧
      RMLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N) (specDomain (1 / 5) N) ∧
      AveragedLawAt N 1 1 Sig (gaussX M N) (specDomain (1 / 5) N) := by
  obtain ⟨N₀, h⟩ :=
    cor_GM_GN (1 / 5) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm he hb => h N hN M Sig (gaussX M N) hm he hb⟩

/-- Theorem 3.14 (ii) at `τ = 1/5`, `τ'' = edgeTau' (1/5)`, `C = gaussMoment`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) → RegularEdge (1 / 5) N (specOf Sig) k →
    RNLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (edgeDomain (1 / 5) (edgeTau' (1 / 5)) N (specOf Sig) k) ∧
      RMLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (edgeDomain (1 / 5) (edgeTau' (1 / 5)) N (specOf Sig) k) := by
  obtain ⟨N₀, h⟩ := edge_law_R (1 / 5) (edgeTau' (1 / 5)) gaussMoment 1 1 (by norm_num)
    (edgeTau'_pos (by norm_num)) le_rfl (by norm_num)
  exact ⟨N₀, fun N hN M Sig k hm hk => h N hN M Sig (gaussX M N) k hm hk⟩

/-- Theorem 3.15 (ii) at `τ = 1/5`, `τ' = 1/10`, `c t = min t 1 / 50`, `C = gaussMoment`,
`ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k →
    RNLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (bulkDomain (1 / 5) (1 / 10) N (specOf Sig) k) ∧
      RMLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (bulkDomain (1 / 5) (1 / 10) N (specOf Sig) k) := by
  obtain ⟨N₀, h⟩ := bulk_law_R (1 / 5) (1 / 10) (fun t => min t 1 / 50) gaussMoment 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M Sig k hm hk => h N hN M Sig (gaussX M N) k hm hk⟩

/-- Theorem 3.16 (ii) at `τ = 1/5`, `τ' = 1/10`, `C = gaussMoment`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ),
    IsModel (1 / 5) gaussMoment M N Sig (gaussX M N) →
    RNLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (outsideDomain (1 / 5) (1 / 10) N (specOf Sig)) ∧
      RMLawAt N 1 1 Sig (sigPow Sig (1 / 2)) (gaussX M N)
        (outsideDomain (1 / 5) (1 / 10) N (specOf Sig)) := by
  obtain ⟨N₀, h⟩ := outside_law_R (1 / 5) (1 / 10) gaussMoment 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M Sig hm => h N hN M Sig (gaussX M N) hm⟩

end Anisotropic

#print axioms Anisotropic.edge_law
#print axioms Anisotropic.bulk_law
#print axioms Anisotropic.outside_law
#print axioms Anisotropic.high_law
#print axioms Anisotropic.LL_G
#print axioms Anisotropic.cor_GM_GN
#print axioms Anisotropic.edge_law_R
#print axioms Anisotropic.bulk_law_R
#print axioms Anisotropic.outside_law_R
