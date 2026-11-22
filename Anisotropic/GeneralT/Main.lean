module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Bulk
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Endpoints.Local
public import Anisotropic.Endpoints.Main
public import Anisotropic.Endpoints.Regions
public import Anisotropic.Endpoints.Resolvents
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model
public import Anisotropic.GeneralT.Edges
public import Anisotropic.GeneralT.Limit
public import Anisotropic.GeneralT.Masses
public import Anisotropic.GeneralT.Model
public import Anisotropic.GeneralT.Spectra

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Proposition 11.1 (without (T_diag)), Corollary 3.9 and Theorems 3.14–3.16 (ii) for a general `T` -/

/-- The localized law at `τ³` for `Ŝ + κ P₀`, packaged for the bulk cases (`c_b > 0` or vacuous). -/
private theorem locLaw_at (τ cb : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < cb → ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S →
      (∀ z ∈ S, cb ≤ (mFun N (specOf Sig) z).im) →
      AnisotropicLawAt N ε D Sig X S ∧ AveragedLawAt N ε D Sig X S := by
  by_cases hcb : 0 < cb
  · obtain ⟨N₀, h⟩ := loc_law τ cb C ε D hτ hcb hε
    exact ⟨N₀, fun _ => h⟩
  · exact ⟨0, fun h => absurd h hcb⟩

/-- A law on `S ∋ z` restricts to `{z}`. -/
private theorem measure_single {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ε D : ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} {z : ℂ}
    (hz : z ∈ S) (h : AnisotropicLawAt N ε D Sig X S ∧ AveragedLawAt N ε D Sig X S) :
    AnisotropicLawAt N ε D Sig X {z} ∧ AveragedLawAt N ε D Sig X {z} :=
  ⟨fun w hw => h.1 w (by rw [Set.mem_singleton_iff.1 hw]; exact hz),
    fun w hw => h.2 w (by rw [Set.mem_singleton_iff.1 hw]; exact hz)⟩

/-- `𝐃(τ, N) ⊆ 𝐃(τ³, N) ⊆ 𝐃(τ_e, N)`. -/
private theorem tau_cube_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : τ ^ 3 ≤ τ := by
  have : τ ^ 3 = τ * τ ^ 2 := by ring
  rw [this]
  exact mul_le_of_le_one_right hτ.le (pow_le_one₀ hτ.le hτ1)

private theorem tauE_le_cube {τ : ℝ} : tauE τ ≤ τ ^ 3 := min_le_left _ _

/-- `𝐃(τ, N)` lies in a compact rectangle of `ℂ₊`. -/
private theorem specDomain_closure_compact {τ : ℝ} (N : ℕ) (hN : 1 ≤ N) :
    ∃ L : Set ℂ, IsCompact L ∧ (∀ w ∈ L, 0 < w.im) ∧ specDomain τ N ⊆ L := by
  have hpos : 0 < (N : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  refine ⟨(fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (-τ⁻¹) τ⁻¹ ×ˢ Set.Icc ((N : ℝ) ^ (-1 + τ)) τ⁻¹),
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop), ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa using lt_of_lt_of_le hpos hp.2.1
  · intro w hw
    refine ⟨(w.re, w.im), ⟨⟨(abs_le.1 hw.2.2.1).1, (abs_le.1 hw.2.2.1).2⟩,
      ⟨hw.2.2.2.1, hw.2.2.2.2⟩⟩, ?_⟩
    apply Complex.ext <;> simp

/-- Proposition 11.1 (§11.1) at fixed `N`, without (T_diag): for a general `M × K` matrix
`T`, if every edge with `a_k ≥ τ/2` is regular at `τ/2` and every bulk component is regular,
then (edge_G_result) in the weighted form for `G` of (def_block_G) and (edge_G_avg_result) hold
on `𝐃(τ, N)`. -/
theorem LL_G_gen (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      AnisotropicLawTAt N ε D T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) := by
  have hτ3 : 0 < τ ^ 3 := by positivity
  have hτe : 0 < tauE τ := tauE_pos hτ
  have hτc : 0 < tauC τ := tauC_pos hτ
  set cb := bulkcb (τ ^ 3) (tauC τ) c / 2 with hcbdef
  obtain ⟨N₁, h₁⟩ := high_law (τ ^ 3) C ε D hτ3 hε
  obtain ⟨N₂, h₂⟩ := outside_law (τ ^ 3) (tauC τ / 2) C ε D hτ3 (by positivity) hε
  obtain ⟨N₃, h₃⟩ := locLaw_at (τ ^ 3) cb C ε D hτ3 hε
  obtain ⟨N₄, h₄⟩ := edge_law (tauE τ) (edgeTau' (tauE τ)) C ε D hτe (edgeTau'_pos hτe) le_rfl hε
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) 1,
    fun N hN Ω _ _ M K T X hm hedge hbulk => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hN₄ : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hda : DensityAssumptions τ N (specOf (T * Tᵀ)) := hm.densityAssumptions hτ
  have hτ1 : τ ≤ 1 := by
    have h1 := hda.phi_lower
    have h2 := hda.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
    linarith
  have hsub3 : specDomain τ N ⊆ specDomain (τ ^ 3) N :=
    specDomain_subset hτ3 (tau_cube_le hτ hτ1) hN1
  have hsubE : specDomain τ N ⊆ specDomain (tauE τ) N :=
    specDomain_subset hτe (tauE_le_cube.trans (tau_cube_le hτ hτ1)) hN1
  have hev3 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hτ3) fun κ hκ => hκ
  have key : ∀ z ∈ specDomain τ N,
      AnisotropicLawTAt N ε D T X {z} ∧ AveragedLawTAt N ε D T X {z} := by
    intro z hz
    refine lawT_of_regS hN1 T X hz.1 ?_
    rcases specDomain_cover' hτ hτc (min_le_right _ _) hN1 hda hz with hh | ⟨ho, hre⟩ |
      ⟨k, hk1, hk2, hb⟩ | ⟨l, hl1, hl2, hla, he⟩
    · -- large `η`
      filter_upwards [hev3] with κ hκ
      have hmκ := isModel_regS hτ hm hκ.1 hκ.2
      have : τ ^ 3 ≤ τ := tau_cube_le hτ hτ1
      have hzh : z ∈ highDomain (τ ^ 3) N := ⟨hsub3 hz, by linarith [hh.2]⟩
      exact measure_single hzh (h₁ N hN₁ K _ X hmκ)
    · -- outside the spectrum
      have hd := outside_regS hτ hN1 hda hτc (by
          have : tauC τ ≤ τ / 4 := min_le_right _ _
          linarith) ho.2
      filter_upwards [hev3, hd] with κ hκ hdκ
      have hmκ := isModel_regS hτ hm hκ.1 hκ.2
      have hzo : z ∈ outsideDomain (τ ^ 3) (tauC τ / 2) N (specOf (regS κ (Tᵀ * T))) :=
        ⟨hsub3 hz, hdκ⟩
      exact measure_single hzo (h₂ N hN₂ K _ X hmκ)
    · -- bulk: the localized law on `𝐃^b_k(τ³, τ_c)` of `Σ`
      have hbk := hbulk k hk1 hk2
      have hc2 : 0 < c (tauC τ / 2) := (hbk.2.2 (tauC τ / 2) (half_pos hτc)).1
      have hcb0 : 0 < bulkcb (τ ^ 3) (tauC τ) c :=
        mul_pos (mul_pos two_pos hc2) (Real.arctan_pos.2 (by positivity))
      have hcbpos : 0 < cb := by rw [hcbdef]; positivity
      have hda3 : DensityAssumptions (τ ^ 3) N (specOf (T * Tᵀ)) :=
        (hm.mono hτ3 (tau_cube_le hτ hτ1)).densityAssumptions hτ3
      have hzb : z ∈ bulkDomain (τ ^ 3) (tauC τ) N (specOf (T * Tᵀ)) k := ⟨hsub3 hz, hb.2⟩
      obtain ⟨L, hLc, hL0, hRL⟩ := specDomain_closure_compact (τ := τ ^ 3) N hN1
      have hu := (Metric.tendstoUniformlyOn_iff.1
        (tendstoUniformlyOn_mFun_regS hN1 T hLc hL0)) cb hcbpos
      filter_upwards [hev3, hu] with κ hκ huκ
      have hmκ := isModel_regS hτ hm hκ.1 hκ.2
      refine measure_single hzb (h₃ hcbpos N hN₃ K _ X _ hmκ
        (spectralDomain_bulkDomain _ _ _ _ _) fun w hw => ?_)
      have h1 := im_mFun_bulk_ge hda3 hbk hτc hw
      have h2 := huκ w (hRL hw.1)
      rw [Complex.dist_eq] at h2
      have h3 := Complex.abs_im_le_norm
        (mFun N (specOf (T * Tᵀ)) w - mFun N (specOf (regS κ (Tᵀ * T))) w)
      rw [Complex.sub_im] at h3
      have h4 := (abs_le.1 (h3.trans h2.le)).2
      rw [hcbdef] at h4 ⊢
      linarith
    · -- edge: a regular edge of `Ŝ + κ P₀` within `δ_a`
      have hreg := hedge l hl1 hl2 hla
      have hev := regularEdge_regS hτ le_rfl hN1 hda hm.ratioK_le hreg
      filter_upwards [hev3, hev] with κ hκ hl'
      obtain ⟨l', hl', hdist, -, -⟩ := hl'
      have hmκ := (isModel_regS hτ hm hκ.1 hκ.2).mono hτe tauE_le_cube
      refine measure_single (S := edgeDomain (tauE τ) (edgeTau' (tauE τ)) N
        (specOf (regS κ (Tᵀ * T))) l') ⟨hsubE hz, ?_⟩ (h₄ N hN₄ K _ X l' hmκ hl')
      have hE := he.2
      have h1 : tauC τ ≤ edgeTau' (tauE τ) / 2 := min_le_left _ _
      have h2 : deltaA τ ≤ edgeTau' (tauE τ) / 16 := min_le_left _ _
      have h3 : 0 < edgeTau' (tauE τ) := edgeTau'_pos hτe
      rw [abs_le] at hdist
      constructor <;> linarith [hE.1, hE.2, hdist.1, hdist.2]
  exact ⟨fun z hz => (key z hz).1 z rfl, fun z hz => (key z hz).2 z rfl⟩

/-- Corollary 3.9 (`cor:GM_GN`) at fixed `N` for a general `T`: (R_N_edge), (R_M_edge) and
(edge_G_avg_result) on `𝐃(τ, N)`. In (R_M_edge), `Σ^{−1/2}` is read as the Moore–Penrose
pseudo-inverse of `Σ^{1/2}`, i.e. the inverse square root on `ran Σ` and `0` on `ker Σ`; for
`Σ > 0` it is the inverse square root. The regularity hypotheses are conditions on `Σ = T Tᵀ`:
every edge `k` with `a_k ≥ τ/2` is regular (Definition 2.7 (i)) with parameter `τ/2`, and every
bulk component is regular (Definition 2.7 (ii)). -/
theorem cor_GM_GN_gen (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      RNLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        RMLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) := by
  obtain ⟨N₁, h₁⟩ := LL_G_gen τ C c (ε / 2) D hτ (half_pos hε)
  obtain ⟨N₂, h₂⟩ := LL_G_gen τ C c ε D hτ hε
  refine ⟨max (max N₁ N₂) (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1),
    fun N hN Ω _ _ M K T X hm hedge hbulk => ?_⟩
  have hA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  have hr := rLawsT_of_anisoT hτ (le_of_max_le_right hB) T subset_rfl
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB))
    (h₁ N (le_of_max_le_left hA) M K T X hm hedge hbulk).1
  exact ⟨hr.1, hr.2, (h₂ N (le_of_max_le_right hA) M K T X hm hedge hbulk).2⟩

/-- Per-point assembly of (R_N_edge), (R_M_edge) from pointwise weighted laws. -/
private theorem rLaws_of_laws {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} (hτ : 0 < τ) {N : ℕ}
    (hN : 1 ≤ N) {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    {S : Set ℂ} (hS : S ⊆ specDomain τ N) {ε D : ℝ} (hNτ : τ⁻¹ ≤ (N : ℝ) ^ (ε / 2))
    (h : ∀ z ∈ S, AnisotropicLawTAt N (ε / 2) D T X {z}) :
    RNLawAt N ε D (T * Tᵀ) T X S ∧ RMLawAt N ε D (T * Tᵀ) T X S := by
  constructor
  · intro z hz
    exact (rLawsT_of_anisoT hτ hN T (Set.singleton_subset_iff.2 (hS hz)) hNτ (h z hz)).1 z rfl
  · intro z hz
    exact (rLawsT_of_anisoT hτ hN T (Set.singleton_subset_iff.2 (hS hz)) hNτ (h z hz)).2 z rfl

/-- Theorem 3.14 (ii) (`thm:edge`) for a general `T`: (R_N_edge), (R_M_edge) on `𝐃^e_k(τ, τ'')`
for every `τ'' ∈ (0, τ'(τ)]`, `τ'(τ) = tauGen τ`. -/
theorem edge_law_R_gen (τ τ'' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ'' : 0 < τ'')
    (hτ''τ : τ'' ≤ tauGen τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      RNLawAt N ε D (T * Tᵀ) T X (edgeDomain τ τ'' N (specOf (T * Tᵀ)) k) ∧
        RMLawAt N ε D (T * Tᵀ) T X (edgeDomain τ τ'' N (specOf (T * Tᵀ)) k) := by
  have hτe : 0 < tauE τ := tauE_pos hτ
  obtain ⟨N₁, h₁⟩ := edge_law (tauE τ) (edgeTau' (tauE τ)) C (ε / 2) D hτe (edgeTau'_pos hτe)
    le_rfl (half_pos hε)
  refine ⟨max N₁ (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M K T X k hm hk => ?_⟩
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf (T * Tᵀ)) := hm.densityAssumptions hτ
  have hτ1 : τ ≤ 1 := by
    have h1 := hda.phi_lower
    have h2 := hda.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
    linarith
  have hsubE : specDomain τ N ⊆ specDomain (tauE τ) N :=
    specDomain_subset hτe (tauE_le_cube.trans (tau_cube_le hτ hτ1)) hN1
  refine rLaws_of_laws (S := edgeDomain τ τ'' N (specOf (T * Tᵀ)) k) hτ hN1 T (fun z hz => hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB)) fun z hz => (lawT_of_regS hN1 T X hz.1.1 ?_).1
  have hev3 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT (by positivity)) fun κ hκ => hκ
  have hev := regularEdge_regS hτ (by linarith) hN1 hda hm.ratioK_le hk
  filter_upwards [hev3, hev] with κ hκ hl'
  obtain ⟨l', hl', hdist, -, -⟩ := hl'
  have hmκ := (isModel_regS hτ hm hκ.1 hκ.2).mono hτe tauE_le_cube
  refine measure_single (S := edgeDomain (tauE τ) (edgeTau' (tauE τ)) N
    (specOf (regS κ (Tᵀ * T))) l') ⟨hsubE hz.1, ?_⟩ (h₁ N (le_of_max_le_left hN) K _ X l' hmκ hl')
  have hE := hz.2
  have h1 : tauGen τ = edgeTau' (tauE τ) / 4 := rfl
  have h2 : deltaA τ ≤ edgeTau' (tauE τ) / 16 := min_le_left _ _
  have h3 : 0 < edgeTau' (tauE τ) := edgeTau'_pos hτe
  rw [abs_le] at hdist
  constructor <;> linarith [hE.1, hE.2, hdist.1, hdist.2]

/-- Theorem 3.15 (ii) (`thm:bulk`) for a general `T`: (R_N_edge), (R_M_edge) on `𝐃^b_k(τ, τ')`. -/
theorem bulk_law_R_gen (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularBulk c N (specOf (T * Tᵀ)) k →
      RNLawAt N ε D (T * Tᵀ) T X (bulkDomain τ τ' N (specOf (T * Tᵀ)) k) ∧
        RMLawAt N ε D (T * Tᵀ) T X (bulkDomain τ τ' N (specOf (T * Tᵀ)) k) := by
  have hτ3 : 0 < τ ^ 3 := by positivity
  set cb := bulkcb (τ ^ 3) τ' c / 2 with hcbdef
  obtain ⟨N₁, h₁⟩ := locLaw_at (τ ^ 3) cb C (ε / 2) D hτ3 (half_pos hε)
  refine ⟨max N₁ (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M K T X k hm hk => ?_⟩
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf (T * Tᵀ)) := hm.densityAssumptions hτ
  have hτ1 : τ ≤ 1 := by
    have h1 := hda.phi_lower
    have h2 := hda.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
    linarith
  have hsub3 : specDomain τ N ⊆ specDomain (τ ^ 3) N :=
    specDomain_subset hτ3 (tau_cube_le hτ hτ1) hN1
  have hc2 : 0 < c (τ' / 2) := (hk.2.2 (τ' / 2) (half_pos hτ')).1
  have hcb0 : 0 < bulkcb (τ ^ 3) τ' c :=
    mul_pos (mul_pos two_pos hc2) (Real.arctan_pos.2 (by positivity))
  have hcbpos : 0 < cb := by rw [hcbdef]; positivity
  have hda3 : DensityAssumptions (τ ^ 3) N (specOf (T * Tᵀ)) :=
    (hm.mono hτ3 (tau_cube_le hτ hτ1)).densityAssumptions hτ3
  refine rLaws_of_laws (S := bulkDomain τ τ' N (specOf (T * Tᵀ)) k) hτ hN1 T (fun z hz => hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB)) fun z hz => (lawT_of_regS hN1 T X hz.1.1 ?_).1
  have hev3 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hτ3) fun κ hκ => hκ
  have hzb : z ∈ bulkDomain (τ ^ 3) τ' N (specOf (T * Tᵀ)) k := ⟨hsub3 hz.1, hz.2⟩
  obtain ⟨L, hLc, hL0, hRL⟩ := specDomain_closure_compact (τ := τ ^ 3) N hN1
  have hu := (Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_mFun_regS hN1 T hLc hL0)) cb hcbpos
  filter_upwards [hev3, hu] with κ hκ huκ
  have hmκ := isModel_regS hτ hm hκ.1 hκ.2
  refine measure_single hzb (h₁ hcbpos N (le_of_max_le_left hN) K _ X _ hmκ
    (spectralDomain_bulkDomain _ _ _ _ _) fun w hw => ?_)
  have h1 := im_mFun_bulk_ge hda3 hk hτ' hw
  have h2 := huκ w (hRL hw.1)
  rw [Complex.dist_eq] at h2
  have h3 := Complex.abs_im_le_norm
    (mFun N (specOf (T * Tᵀ)) w - mFun N (specOf (regS κ (Tᵀ * T))) w)
  rw [Complex.sub_im] at h3
  have h4 := (abs_le.1 (h3.trans h2.le)).2
  rw [hcbdef] at h4 ⊢
  linarith

/-- Theorem 3.16 (ii) (`thm:outside`) for a general `T`: (R_N_edge), (R_M_edge) on
`𝐃^o(τ, τ')`. -/
theorem outside_law_R_gen (τ τ' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      RNLawAt N ε D (T * Tᵀ) T X (outsideDomain τ τ' N (specOf (T * Tᵀ))) ∧
        RMLawAt N ε D (T * Tᵀ) T X (outsideDomain τ τ' N (specOf (T * Tᵀ))) := by
  have hτ3 : 0 < τ ^ 3 := by positivity
  have ht : 0 < min τ' (τ / 2) := lt_min hτ' (half_pos hτ)
  obtain ⟨N₁, h₁⟩ := high_law (τ ^ 3) C (ε / 2) D hτ3 (half_pos hε)
  obtain ⟨N₂, h₂⟩ := outside_law (τ ^ 3) (min τ' (τ / 2) / 2) C (ε / 2) D hτ3 (half_pos ht)
    (half_pos hε)
  refine ⟨max (max N₁ N₂) (max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1), fun N hN Ω _ _ M K T X hm => ?_⟩
  have hA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hB : max ⌈τ⁻¹ ^ (2 / ε)⌉₊ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf (T * Tᵀ)) := hm.densityAssumptions hτ
  have hτ1 : τ ≤ 1 := by
    have h1 := hda.phi_lower
    have h2 := hda.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
    linarith
  have h3τ : τ ^ 3 ≤ τ := tau_cube_le hτ hτ1
  have hsub3 : specDomain τ N ⊆ specDomain (τ ^ 3) N := specDomain_subset hτ3 h3τ hN1
  have hev3 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hτ3) fun κ hκ => hκ
  refine rLaws_of_laws (S := outsideDomain τ τ' N (specOf (T * Tᵀ))) hτ hN1 T (fun z hz => hz.1)
    (inv_le_rpow_of_ge hτ hε (le_of_max_le_left hB)) fun z hz => (lawT_of_regS hN1 T X hz.1.1 ?_).1
  by_cases hη : τ ^ 3 / 2 ≤ z.im
  · filter_upwards [hev3] with κ hκ
    have hzh : z ∈ highDomain (τ ^ 3) N := ⟨hsub3 hz.1, hη⟩
    exact measure_single hzh
      (h₁ N (le_of_max_le_left hA) K _ X (isModel_regS hτ hm hκ.1 hκ.2))
  · push Not at hη
    have hre := abs_re_gt_of_im_lt hτ hz.1 (by linarith)
    have hd := outside_regS hτ hN1 hda ht (le_trans (min_le_right _ _) hre.le)
      (le_trans (min_le_left _ _) hz.2)
    filter_upwards [hev3, hd] with κ hκ hdκ
    have hzo : z ∈ outsideDomain (τ ^ 3) (min τ' (τ / 2) / 2) N (specOf (regS κ (Tᵀ * T))) :=
      ⟨hsub3 hz.1, hdκ⟩
    exact measure_single hzo
      (h₂ N (le_of_max_le_right hA) K _ X (isModel_regS hτ hm hκ.1 hκ.2))

/-! ### Compiled instances

Each theorem above has an `∃ N₀` conclusion, so no instance fixes a concrete `N ≥ N₀`. The
following instances are conditional: they specialise the fixed parameters
(`τ = 1/5`, `C = gaussMoment`, `c t = min t 1 / 50`, `ε = D = 1`) and the Gaussian ensemble,
and keep the model, edge and bulk hypotheses as binders. -/

/-- Proposition 11.1 without (T_diag) at `τ = 1/5`, `C = gaussMoment`, `c t = min t 1 / 50`,
`ε = D = 1`, Gaussian `X`; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → 1 / 5 / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
      RegularEdge (1 / 5 / 2) N (specOf (T * Tᵀ)) k) →
    (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
      RegularBulk (fun t => min t 1 / 50) N (specOf (T * Tᵀ)) k) →
    AnisotropicLawTAt N 1 1 T (gaussX K N) (specDomain (1 / 5) N) ∧
      AveragedLawTAt N 1 1 T (gaussX K N) (specDomain (1 / 5) N) := by
  obtain ⟨N₀, h⟩ := LL_G_gen (1 / 5) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M K T hm he hb => h N hN M K T (gaussX K N) hm he hb⟩

/-- Corollary 3.9 for a general `T` at the same parameters; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → 1 / 5 / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
      RegularEdge (1 / 5 / 2) N (specOf (T * Tᵀ)) k) →
    (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
      RegularBulk (fun t => min t 1 / 50) N (specOf (T * Tᵀ)) k) →
    RNLawAt N 1 1 (T * Tᵀ) T (gaussX K N) (specDomain (1 / 5) N) ∧
      RMLawAt N 1 1 (T * Tᵀ) T (gaussX K N) (specDomain (1 / 5) N) ∧
      AveragedLawTAt N 1 1 T (gaussX K N) (specDomain (1 / 5) N) := by
  obtain ⟨N₀, h⟩ :=
    cor_GM_GN_gen (1 / 5) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M K T hm he hb => h N hN M K T (gaussX K N) hm he hb⟩

/-- Theorem 3.14 (ii) for a general `T` at `τ = 1/5`, `τ'' = tauGen (1/5)`, `C = gaussMoment`,
`ε = D = 1`; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (k : ℕ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    RegularEdge (1 / 5) N (specOf (T * Tᵀ)) k →
    RNLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (edgeDomain (1 / 5) (tauGen (1 / 5)) N (specOf (T * Tᵀ)) k) ∧
      RMLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (edgeDomain (1 / 5) (tauGen (1 / 5)) N (specOf (T * Tᵀ)) k) := by
  obtain ⟨N₀, h⟩ := edge_law_R_gen (1 / 5) (tauGen (1 / 5)) gaussMoment 1 1 (by norm_num)
    (by have := edgeTau'_pos (tauE_pos (show (0 : ℝ) < 1 / 5 by norm_num))
        unfold tauGen; positivity) le_rfl (by norm_num)
  exact ⟨N₀, fun N hN M K T k hm hk => h N hN M K T (gaussX K N) k hm hk⟩

/-- Theorem 3.15 (ii) for a general `T` at `τ = 1/5`, `τ' = 1/10`, `c t = min t 1 / 50`,
`C = gaussMoment`, `ε = D = 1`; the hypotheses are binders. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (k : ℕ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    RegularBulk (fun t => min t 1 / 50) N (specOf (T * Tᵀ)) k →
    RNLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (bulkDomain (1 / 5) (1 / 10) N (specOf (T * Tᵀ)) k) ∧
      RMLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (bulkDomain (1 / 5) (1 / 10) N (specOf (T * Tᵀ)) k) := by
  obtain ⟨N₀, h⟩ := bulk_law_R_gen (1 / 5) (1 / 10) (fun t => min t 1 / 50) gaussMoment 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M K T k hm hk => h N hN M K T (gaussX K N) k hm hk⟩

/-- Theorem 3.16 (ii) for a general `T` at `τ = 1/5`, `τ' = 1/10`, `C = gaussMoment`,
`ε = D = 1`; the model hypothesis is a binder. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ),
    IsModelT (1 / 5) gaussMoment M K N T (gaussX K N) →
    RNLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (outsideDomain (1 / 5) (1 / 10) N (specOf (T * Tᵀ))) ∧
      RMLawAt N 1 1 (T * Tᵀ) T (gaussX K N)
        (outsideDomain (1 / 5) (1 / 10) N (specOf (T * Tᵀ))) := by
  obtain ⟨N₀, h⟩ := outside_law_R_gen (1 / 5) (1 / 10) gaussMoment 1 1 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN M K T hm => h N hN M K T (gaussX K N) hm⟩

end Anisotropic

#print axioms Anisotropic.LL_G_gen
#print axioms Anisotropic.cor_GM_GN_gen
#print axioms Anisotropic.edge_law_R_gen
#print axioms Anisotropic.bulk_law_R_gen
#print axioms Anisotropic.outside_law_R_gen
