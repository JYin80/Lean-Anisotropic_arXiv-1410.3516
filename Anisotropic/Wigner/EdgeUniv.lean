import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Rigidity.Defs
import Anisotropic.Wigner.AvgMain
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeCompare
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeLocal
import Anisotropic.Wigner.EdgeRegime
import Anisotropic.Wigner.EdgeSym
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.Rigid

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Theorem 12.5: edge universality for `W + A` at both edges -/

/-! ## Monotonicity of the laws and the bound `(Ψ^W)² ≤ 4 (Nη)⁻¹` -/

/-- The entrywise law passes to a smaller domain, a smaller `ε` and a smaller `D`. -/
private lemma aux_entry_mono {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S S' : Set ℂ}
    (hS : S' ⊆ S) (hS0 : ∀ z ∈ S', 0 < z.im) (hε : ε ≤ ε') (hD : D' ≤ D)
    (h : EntrywiseLawWAt N ε D A W S) : EntrywiseLawWAt N ε' D' A W S' := by
  intro z hz s t
  have hz0 := hS0 z hz
  refine DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ?_) hε hD (h z (hS hz) s t)
  unfold PsiW
  positivity

/-- The averaged law gives the averaged law with any control `Φ ≥ (Nη)⁻¹`, on a smaller domain,
at a smaller `ε` and a smaller `D`. -/
private lemma aux_avg_phi {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S S' : Set ℂ}
    {Φ : ℂ → ℝ} (hS : S' ⊆ S) (hΦ : ∀ z ∈ S', 1 / (N * z.im) ≤ Φ z ∧ 0 ≤ Φ z) (hε : ε ≤ ε')
    (hD : D' ≤ D) (h : AveragedLawWAt N ε D A W S) : AveragedPhiLawWAt N ε' D' A W S' Φ :=
  fun z hz => DomAt.mono hN (fun _ => le_rfl) (fun _ => (hΦ z hz).1) (fun _ => (hΦ z hz).2) hε hD
    (h z (hS hz))

/-- The averaged law with control `Φ'` gives the averaged law with any control `Φ ≥ Φ'`. -/
private lemma aux_phi_mono {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} (hN : 1 ≤ N) {ε D : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {Φ Φ' : ℂ → ℝ} (hΦ : ∀ z ∈ S, Φ' z ≤ Φ z ∧ 0 ≤ Φ z) (h : AveragedPhiLawWAt N ε D A W S Φ') :
    AveragedPhiLawWAt N ε D A W S Φ :=
  fun z hz => DomAt.mono hN (fun _ => le_rfl) (fun _ => (hΦ z hz).1) (fun _ => (hΦ z hz).2)
    le_rfl le_rfl (h z hz)

/-- Rigid extremes at `(ε, D)` give rigid extremes at a larger `ε` and a smaller `D`. -/
private lemma aux_rigid_mono {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' Lm Lp : ℝ}
    {H : Ω → Matrix (Fin N) (Fin N) ℝ} (hε : ε ≤ ε') (hD : D' ≤ D)
    (h : RigidExtremesAt N ε D Lm Lp H) : RigidExtremesAt N ε' D' Lm Lp H :=
  ⟨DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by positivity) hε hD h.1,
    DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by positivity) hε hD h.2⟩

/-- On the edge cone, `Nη ≥ 1`. -/
private lemma aux_cone_Neta {N : ℕ} (hN : 1 ≤ N) {τ c K : ℝ} {a : Fin N → ℝ} {z : ℂ}
    (hz : z ∈ edgeConeW τ N a c K) : 1 ≤ (N : ℝ) * z.im := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h2 : (N : ℝ)⁻¹ ≤ z.im := by
    rw [← Real.rpow_neg_one]
    exact h1.trans hz.2.1
  calc (1 : ℝ) = N * (N : ℝ)⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
    _ ≤ N * z.im := mul_le_mul_of_nonneg_left h2 hN0.le

/-- `(Ψ^W)² ≤ 4 (Nη)⁻¹` when `Nη ≥ 1` (`|m^W| < 1`). -/
private lemma aux_psi_sq {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hNz : 1 ≤ (N : ℝ) * z.im) : PsiW a z ^ 2 ≤ 4 / (N * z.im) := by
  have hNz0 : 0 < (N : ℝ) * z.im := by linarith
  set t : ℝ := 1 / (N * z.im) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hNz0]; exact hNz
  have him : (mW a z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_mW_lt_one hN a hz).le
  have hu : (mW a z).im / (N * z.im) ≤ t := by
    rw [ht]
    exact div_le_div_of_nonneg_right him hNz0.le
  have hs : √((mW a z).im / (N * z.im)) ≤ √t := Real.sqrt_le_sqrt hu
  have hst : √t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hs0 : 0 ≤ √((mW a z).im / (N * z.im)) := Real.sqrt_nonneg _
  have hP : PsiW a z ≤ √t + t := by
    unfold PsiW
    rw [← ht]
    linarith
  have hP0 : 0 ≤ PsiW a z := by unfold PsiW; positivity
  have h4 : (√t + t) ^ 2 ≤ 4 * t := by
    have : √t * t ≤ t := by nlinarith [Real.sqrt_nonneg t]
    nlinarith
  calc PsiW a z ^ 2 ≤ (√t + t) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    _ ≤ 4 * t := h4
    _ = 4 / (N * z.im) := by rw [ht]; ring

/-- The GOE matrix is symmetric. -/
private lemma aux_goe_herm (N : ℕ) (ω : GOESpace N) : (goeW N ω).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (isGOE_goeW N).symm ω

/-- The vector of Theorem 12.5 is `edgeQ` with `ϖ = 1` and no eigenvalue beyond the edge. -/
private lemma aux_edgeQ (N : ℕ) (a : ℝ) (l : ℕ) {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    edgeQ N a 1 0 l H = fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig H (i + 1) - a) := by
  funext i
  simp [edgeQ]

/-- `K (B + L) N^{-2c₀} ≤ N^{-c₀}` for `N` large, `c₀ > 0`. -/
private lemma aux_rate (K B L c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (B + L) * (N : ℝ) ^ (-c₀ + -c₀) ≤ (N : ℝ) ^ (-c₀) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (((tendsto_rpow_atTop hc₀).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (K * (B + L)))
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : K * (B + L) ≤ (N : ℝ) ^ c₀ := hN₁ N (le_of_max_le_left hN)
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-c₀) := Real.rpow_nonneg hN0.le _
  rw [Real.rpow_add hN0]
  calc K * (B + L) * ((N : ℝ) ^ (-c₀) * (N : ℝ) ^ (-c₀))
      = K * (B + L) * (N : ℝ) ^ (-c₀) * (N : ℝ) ^ (-c₀) := by ring
    _ ≤ (N : ℝ) ^ c₀ * (N : ℝ) ^ (-c₀) * (N : ℝ) ^ (-c₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hp) hp
    _ = (N : ℝ) ^ (-c₀) := by
        rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, one_mul]

/-- The rate of the bounded Lipschitz form at `l` is `N^{-2c₀}` with `c₀ = 1/(1600(l+1))`. -/
private lemma aux_rate_exp (l : ℕ) :
    (-(1 / (800 * (l + 1)) : ℝ)) = -(1 / (1600 * (l + 1))) + -(1 / (1600 * (l + 1))) := by
  have hl : (0 : ℝ) < l + 1 := by positivity
  field_simp
  ring

/-- A `C¹` function with `‖f'‖ ≤ L` is `max(L, 0)`-Lipschitz, and then
`K (B + max(L, 0)) N^{-1/(800(l+1))} ≤ N^{-1/(1600(l+1))}` for `N` large. -/
private lemma aux_c1 {l : ℕ} (K B : ℝ) {f : (Fin l → ℝ) → ℝ} {L : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    LipschitzWith L.toNNReal f ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁,
      K * (B + L.toNNReal) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤
        (N : ℝ) ^ (-(1 / (1600 * (l + 1)) : ℝ)) := by
  have hc₀ : (0 : ℝ) < 1 / (1600 * (l + 1)) := by positivity
  refine ⟨lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) fun x => ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hL x).trans (Real.le_coe_toNNReal L)
  · obtain ⟨N₁, hN₁⟩ := aux_rate K B (L.toNNReal : ℝ) _ hc₀
    exact ⟨N₁, fun N hN => by rw [aux_rate_exp]; exact hN₁ N hN⟩

/-! ## Theorem 12.5 -/

/-- Theorem 12.5 (`lem:comp Wig`) at the right edge, for the class of entry laws, with rate:
there is `τ ∈ (0, τ₀]` such that, under the hypotheses of Theorem 12.4 at `τ`, for every bounded
Lipschitz `f`, `|E f((N^{2/3}(λ_i(W + A) - L₊))_{i ≤ l}) - E f((N^{2/3}(λ_i(W^Gauss + D) -
L₊))_{i ≤ l})| ≤ K (‖f‖_∞ + Lip f) N^{-1/(800(l+1))}`. -/
theorem wigner_edge_univ_lip_class (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ) (hτA : 0 < τA)
    (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τA⁻¹ → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      ∀ (f : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |f x| ≤ B) → LipschitzWith L f →
        |(∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (W ω + A) (i + 1) - LpW (specOf A)))) -
          (∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (goeW N ω + diagonal (specOf A)) (i + 1) - LpW (specOf A))))| ≤
          K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hδ0 : (0 : ℝ) < (1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) := by positivity
  have hδ3 : (1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hτA0 : 0 < τA⁻¹ := inv_pos.2 hτA
  have hτ₀'0 : 0 < min τ₀ (min (1 / 4) (τA⁻¹ + 3)⁻¹) :=
    lt_min hτ₀ (lt_min (by norm_num) (inv_pos.2 (by linarith)))
  obtain ⟨τ, hτ, hττ₀', εr, Dr, hεr, Nr, hrig⟩ :=
    wigner_rig_class τA C (min τ₀ (min (1 / 4) (τA⁻¹ + 3)⁻¹))
      ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3 hτA hτ₀'0 (by positivity)
  have hττ₀ : τ ≤ τ₀ := hττ₀'.trans (min_le_left _ _)
  have hτ4 : τ ≤ 1 / 4 := hττ₀'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτA3 : τA⁻¹ ≤ τ⁻¹ - 3 := by
    have h1 : τ ≤ (τA⁻¹ + 3)⁻¹ := hττ₀'.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : τA⁻¹ + 3 ≤ τ⁻¹ := by
      calc τA⁻¹ + 3 = ((τA⁻¹ + 3)⁻¹)⁻¹ := (inv_inv _).symm
        _ ≤ τ⁻¹ := inv_anti₀ hτ h1
    linarith
  obtain ⟨c, Kc, r₀, C₀, hc, hKc, hr₀, hC₀, hreg⟩ := edgeRegime_wig hτ hτ4
  obtain ⟨Ng, hg⟩ := hreg ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1))) 6 l hδ0 hδ3
  obtain ⟨Nψ, hψ⟩ := psiSmallW_edgeConeW hτ c (cΨ := 1 / 24) hKc (by norm_num)
  obtain ⟨εa, Da, hεa, Na, havg⟩ := general_wig_avg_phi τ (1 / 24) C
    ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3 hτ (by norm_num) (by positivity)
  obtain ⟨εc, Dc, hεc, Nc, hcmp⟩ :=
    smoothComparable_wig τ C l (1 / 200) hτ hτ4 (by norm_num) le_rfl
  obtain ⟨K, Ne, hred⟩ := edge_reduction l (1 / 200) (1 / 6 - 24 * (1 / 200)) 1 1 C₀ r₀
    (by norm_num) le_rfl (by norm_num) one_pos le_rfl (by linarith) hr₀
  refine ⟨τ, hτ, hττ₀, min (min εr εa) (min εc ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2)),
    max (max Dr Da) (max Dc 3), lt_min (lt_min hεr hεa) (lt_min hεc (by positivity)), K,
    max (max (max Nr Ng) (max Nψ Na)) (max (max Nc Ne) 1), ?_⟩
  intro N hN Ω _ _ A W hAh hAn hWc hsb he ha hr f B L hfB hfL
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hNr, hNg⟩, hNψ, hNa⟩, ⟨hNc, hNe⟩, hN1⟩ := hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hεr' : min (min εr εa) (min εc ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2)) ≤ εr :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hεa' : min (min εr εa) (min εc ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2)) ≤ εa :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hεc' : min (min εr εa) (min εc ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2)) ≤ εc :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : min (min εr εa) (min εc ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2)) ≤
      (1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hDr : Dr ≤ max (max Dr Da) (max Dc 3) := (le_max_left _ _).trans (le_max_left _ _)
  have hDa : Da ≤ max (max Dr Da) (max Dc 3) := (le_max_right _ _).trans (le_max_left _ _)
  have hDc : Dc ≤ max (max Dr Da) (max Dc 3) := (le_max_left _ _).trans (le_max_right _ _)
  have hD3 : (3 : ℝ) ≤ max (max Dr Da) (max Dc 3) := (le_max_right _ _).trans (le_max_right _ _)
  have hAτ : ‖A‖ ≤ τ⁻¹ - 3 := hAn.trans hτA3
  have habs : ∀ i, |specOf A i| ≤ τ⁻¹ - 3 := fun i => (abs_specOf_le_norm hAh i).trans hAτ
  have hWh : ∀ ω, (W ω).IsHermitian := fun ω => by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hWc.symm ω
  have hdom0 : ∀ z ∈ domW τ N, 0 < z.im := fun z hz => hz.1
  have h16 : ∀ z : ℂ, 0 < z.im → 1 / (N * z.im) ≤ 6 / (N * z.im) ∧ 0 ≤ 6 / (N * z.im) :=
    fun z hz => ⟨div_le_div_of_nonneg_right (by norm_num) (by positivity), by positivity⟩
  -- the edge regime for `W + A`
  have hcone : edgeConeW τ N (specOf A) c Kc ⊆ domW τ N := fun z hz => hz.1
  have hrig1 : RigidExtremesWAt N ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3 (specOf A)
      (fun ω => W ω + A) :=
    hrig N hNr A W hAh hAn hWc hsb (aux_entry_mono hN1 subset_rfl hdom0 hεr' hDr he)
      (aux_avg_phi (Φ := fun z => 1 / (N * z.im)) hN1 subset_rfl
        (fun z hz => ⟨le_rfl, by have := hz.1; positivity⟩) hεr' hDr ha)
      (aux_rigid_mono hN1 hεr' hDr hr)
  have havg1 := havg N hNa A W (edgeConeW τ N (specOf A) c Kc) (fun z => 1 / (N * z.im)) hAh
    (by linarith) hWc (spectralDomainW_edgeConeW τ N (specOf A) c hKc.le)
    (fun z hz => hsb z (hcone hz))
    (Or.inr (hψ N hNψ (specOf A) (fun i => (habs i).trans (by linarith)) hsb))
    (fun z hz => ⟨by have := hz.1.1; positivity, le_rfl⟩)
    (aux_entry_mono hN1 hcone (fun z hz => hz.1.1) hεa' hDa he)
    (aux_avg_phi hN1 hcone (fun z hz => ⟨le_rfl, by have := hz.1.1; positivity⟩) hεa' hDa ha)
  have havg1' : AveragedPhiLawWAt N ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3 A W
      (edgeConeW τ N (specOf A) c Kc) (fun z => 6 / (N * z.im)) := by
    refine aux_phi_mono hN1 (fun z hz => ⟨?_, (h16 z hz.1.1).2⟩) havg1
    have hz0 : 0 < z.im := hz.1.1
    have hNz := aux_cone_Neta hN1 hz
    have hNz0 : 0 < (N : ℝ) * z.im := by linarith
    have hψ2 := aux_psi_sq hN1 (specOf A) hz0 hNz
    have hp : (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1' (by norm_num)
    have hp' : (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) / (N * z.im) ≤ 1 / (N * z.im) :=
      div_le_div_of_nonneg_right hp hNz0.le
    calc 1 / (N * z.im) + PsiW (specOf A) z ^ 2 + (N : ℝ) ^ (-(1 / 24 : ℝ) / 2) / (N * z.im)
        ≤ 1 / (N * z.im) + 4 / (N * z.im) + 1 / (N * z.im) := by linarith
      _ = 6 / (N * z.im) := by ring
  have hH1 := hg N hNg A W hAh hWh habs hsb havg1' hrig1
  -- the edge regime for `W^Gauss + D`
  obtain ⟨e, hDe⟩ := exists_perm_specOf_diagonal (specOf A)
  have hLp0 : LpW (specOf (diagonal (specOf A))) = LpW (specOf A) := by
    rw [hDe, LpW_comp_perm]
  have hLm0 : LmW (specOf (diagonal (specOf A))) = LmW (specOf A) := by
    rw [hDe, LmW_comp_perm]
  have hDh : (diagonal (specOf A)).IsHermitian := isHermitian_diagonal _
  have habs0 : ∀ i, |specOf (diagonal (specOf A)) i| ≤ τ⁻¹ - 3 := fun i => by
    rw [hDe]
    exact habs (e i)
  have hsb0 : StandingBoundW τ (specOf (diagonal (specOf A))) (domW τ N) := by
    intro z hz i
    rw [hDe, mW_comp_perm]
    exact hsb z hz (e i)
  have havg0 : AveragedPhiLawWAt N ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3
      (diagonal (specOf A)) (goeW N) (edgeConeW τ N (specOf (diagonal (specOf A))) c Kc)
      (fun z => 6 / (N * z.im)) :=
    aux_avg_phi hN1 (fun z hz => hz.1) (fun z hz => h16 z hz.1.1) hεδ hD3 ha
  have hrig0 : RigidExtremesWAt N ((1 / 200 : ℝ) / (8 * ((l : ℝ) + 1)) / 2) 3
      (specOf (diagonal (specOf A))) (fun ω => goeW N ω + diagonal (specOf A)) := by
    unfold RigidExtremesWAt
    rw [hLp0, hLm0]
    exact aux_rigid_mono hN1 hεδ hD3 hr
  have hH0 := hg N hNg (diagonal (specOf A)) (goeW N) hDh (aux_goe_herm N) habs0 hsb0 havg0 hrig0
  rw [hLp0] at hH0
  -- the comparison and the reduction
  have hSC := hcmp N hNc A W hAh hAτ hWc hsb (aux_entry_mono hN1 subset_rfl hdom0 hεc' hDc he)
  have hmeas1 : Measurable fun ω => W ω + A :=
    Matrix.measurable_iff.2 fun i j => (hWc.measurable i j).add_const _
  have hmeas0 : Measurable fun ω => goeW N ω + diagonal (specOf A) :=
    Matrix.measurable_iff.2 fun i j => ((isGOE_goeW N).measurable i j).add_const _
  have hNC : (N : ℝ) ≤ C₀ * N := by nlinarith
  have := hred N hNe N 0 (LpW (specOf A)) 1 hNC ⟨le_rfl, le_rfl⟩ (fun ω => W ω + A)
    (fun ω => goeW N ω + diagonal (specOf A)) hmeas1 hmeas0 (fun ω => (hWh ω).add hAh)
    (fun ω => (aux_goe_herm N ω).add hDh) hH1 hH0 hSC f B L hfB hfL
  have hx : (1 / 200 : ℝ) / (4 * ((l : ℝ) + 1)) = 1 / (800 * ((l : ℝ) + 1)) := by
    field_simp
    ring
  simp only [aux_edgeQ] at this
  rw [hx] at this
  exact this

/-- Theorem 12.5 (`lem:comp Wig`) at the right edge, for the model of §12.1: for every
`C¹` function `f` that is bounded with bounded derivative there are `c₀ > 0` (depending only on
`l`) and `N₀` with `|E f(…(W + A)…) - E f(…(W^Gauss + D)…)| ≤ N^{-c₀}`. -/
theorem wigner_edge_univ (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ) (hτA : 0 < τA)
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
          (N : ℝ) ^ (-c₀) := by
  obtain ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, K, N₀, h⟩ := wigner_edge_univ_lip_class τA C τ₀ l hτA hτ₀
  refine ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, 1 / (1600 * (l + 1)), by positivity,
    fun f B L hf hB hL => ?_⟩
  obtain ⟨hLip, N₁, hN₁⟩ := aux_c1 (l := l) K B hf hL
  refine ⟨max N₀ N₁, fun N hN Ω _ _ A W hM hsb he ha hr => ?_⟩
  exact (h N (le_of_max_le_left hN) A W hM.symmA hM.normA hM.entries.toClass hsb he ha hr f B
    L.toNNReal hB hLip).trans (hN₁ N (le_of_max_le_right hN))

/-- Theorem 12.5 at the left edge ("a similar result", §12.1), for the class, with rate:
the same for `(N^{2/3}(λ_{N+1-i}(·) - L₋))_{i ≤ l}`. -/
theorem wigner_edge_univ_left_lip_class (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ)
    (hτA : 0 < τA) (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τA⁻¹ → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      ∀ (f : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |f x| ≤ B) → LipschitzWith L f →
        |(∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (W ω + A) (N - i) - LmW (specOf A)))) -
          (∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (goeW N ω + diagonal (specOf A)) (N - i) - LmW (specOf A))))| ≤
          K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  obtain ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, K, N₀, h⟩ := wigner_edge_univ_lip_class τA C τ₀ l hτA hτ₀
  refine ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, K, max N₀ (max l 1), ?_⟩
  intro N hN Ω _ _ A W hAh hAn hWc hsb he ha hr f B L hfB hfL
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨hN₀, hlN, hN1⟩ := hN
  obtain ⟨hLp, -⟩ := LpW_specOf_neg hAh
  have hWh : ∀ ω, (W ω).IsHermitian := fun ω => by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hWc.symm ω
  have hfL' : LipschitzWith L (fun x : Fin l → ℝ => f (-x)) := by
    have h1 : LipschitzWith 1 (fun x : Fin l → ℝ => -x) :=
      LipschitzWith.of_dist_le_mul fun x y => by simp [dist_neg_neg]
    simpa [Function.comp_def] using hfL.comp h1
  have key := h N hN₀ (-A) (fun ω => -W ω) hAh.neg (by rwa [norm_neg]) hWc.neg
    (standingBoundW_specOf_neg hN1 hAh hsb) (entrywiseLawWAt_goe_neg hN1 hAh he)
    (averagedLawWAt_goe_neg hN1 hAh ha) (rigidExtremesWAt_goe_neg hN1 hAh hr)
    (fun x => f (-x)) B L (fun x => hfB _) hfL'
  -- `λ_{i+1}(-X) = -λ_{N-i}(X)` and `L₊(spec(-A)) = -L₋(spec A)`
  have hrefl : ∀ X : Matrix (Fin N) (Fin N) ℝ, X.IsHermitian →
      (-(fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig (-X) (i + 1) - LpW (specOf (-A))))) =
        fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig X (N - i) - LmW (specOf A)) := by
    intro X hX
    funext i
    have hi := i.isLt
    rw [Pi.neg_apply, sortedEig_neg' hX (by omega) (by omega), hLp,
      show N + 1 - ((i : ℕ) + 1) = N - i by omega]
    ring
  -- the `W + A` side
  have e1 : (∫ ω, f (fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) *
      (sortedEig (W ω + A) (N - i) - LmW (specOf A)))) =
      ∫ ω, f (-(fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) *
        (sortedEig (-W ω + -A) (i + 1) - LpW (specOf (-A))))) := by
    congr 1
    funext ω
    rw [← neg_add, hrefl _ ((hWh ω).add hAh)]
  -- the `W^Gauss + D` side
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : Matrix (Fin N) (Fin N) ℝ → ℝ, Φ = fun X =>
      f (fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig X (N - i) - LmW (specOf A))) :=
    ⟨_, rfl⟩
  obtain ⟨Ψ, hΨd⟩ : ∃ Ψ : Matrix (Fin N) (Fin N) ℝ → ℝ, Ψ = fun X =>
      f (-(fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) *
        (sortedEig X (i + 1) - LpW (specOf (-A))))) := ⟨_, rfl⟩
  have hΦm : Measurable Φ := by
    rw [hΦd]
    exact hfL.continuous.measurable.comp (measurable_pi_iff.2 fun i =>
      ((measurable_sortedEig' N _).sub_const _).const_mul _)
  have hΨm : Measurable Ψ := by
    rw [hΨd]
    exact hfL.continuous.measurable.comp (measurable_pi_iff.2 fun i =>
      (((measurable_sortedEig' N _).sub_const _).const_mul _).neg)
  have hΦi : ∀ O : Matrix (Fin N) (Fin N) ℝ, O ∈ Matrix.orthogonalGroup (Fin N) ℝ →
      ∀ X : Matrix (Fin N) (Fin N) ℝ, X.IsHermitian → Φ (O * X * Oᵀ) = Φ X := by
    intro O hO X hX
    simp only [hΦd, sortedEig_conj hO hX]
  have hΨi : ∀ O : Matrix (Fin N) (Fin N) ℝ, O ∈ Matrix.orthogonalGroup (Fin N) ℝ →
      ∀ X : Matrix (Fin N) (Fin N) ℝ, X.IsHermitian → Ψ (O * X * Oᵀ) = Ψ X := by
    intro O hO X hX
    simp only [hΨd, sortedEig_conj hO hX]
  have s1 := integral_goe_add_conj hAh.neg hΨm hΨi
  have s2 := integral_goe_neg hΨm (-A)
  have s3 := integral_goe_add_conj hAh hΦm hΦi
  have s4 : (∫ ω, Ψ (-goeW N ω + -A)) = ∫ ω, Φ (goeW N ω + A) := by
    congr 1
    funext ω
    rw [hΨd, hΦd]
    dsimp only
    rw [← neg_add, hrefl _ ((aux_goe_herm N ω).add hAh)]
  have e0 : (∫ ω, Φ (goeW N ω + diagonal (specOf A))) =
      ∫ ω, Ψ (goeW N ω + diagonal (specOf (-A))) :=
    s3.symm.trans (s4.symm.trans (s2.trans s1))
  rw [hΦd, hΨd] at e0
  rw [e1, e0]
  exact key

/-- Theorem 12.5 at the left edge ("a similar result", §12.1), for the model of §12.1. -/
theorem wigner_edge_univ_left (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ) (hτA : 0 < τA)
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
              (sortedEig (W ω + A) (N - i) - LmW (specOf A)))) -
          (∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (goeW N ω + diagonal (specOf A)) (N - i) - LmW (specOf A))))| ≤
          (N : ℝ) ^ (-c₀) := by
  obtain ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, K, N₀, h⟩ := wigner_edge_univ_left_lip_class τA C τ₀ l hτA hτ₀
  refine ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, 1 / (1600 * (l + 1)), by positivity,
    fun f B L hf hB hL => ?_⟩
  obtain ⟨hLip, N₁, hN₁⟩ := aux_c1 (l := l) K B hf hL
  refine ⟨max N₀ N₁, fun N hN Ω _ _ A W hM hsb he ha hr => ?_⟩
  exact (h N (le_of_max_le_left hN) A W hM.symmA hM.normA hM.entries.toClass hsb he ha hr f B
    L.toNNReal hB hLip).trans (hN₁ N (le_of_max_le_right hN))

/-- The constants at `ε = 1/200`: `c₁ = 1/6 - 24ε ≥ ε`; the rate `ε/(4(l+1)) = 1/(800(l+1))` and
`c₀ = ε/(8(l+1)) = 1/(1600(l+1))`; `c_Ψ = (1/12 - 9ε)/2 > 0` with `-1/3 + 9ε < -1/4 - c_Ψ`;
`η = N^{-2/3-9ε} ≥ N^{-1+τ}` for `τ ≤ 1/4`; `δ = ε/(8(l+1)) ∈ (0, 1/3]`; the cone exponent
`1/24 < 1/12`; the window exponent `-2/3 + ε < 0`. -/
example (l : ℕ) :
    (1 / 200 : ℝ) ≤ 1 / 6 - 24 * (1 / 200) ∧
      (1 / 200 : ℝ) / (4 * (l + 1)) = 1 / (800 * (l + 1)) ∧
      (1 / 200 : ℝ) / (8 * (l + 1)) = 1 / (1600 * (l + 1)) ∧
      0 < (1 / 12 - 9 * (1 / 200 : ℝ)) / 2 ∧
      -1 / 3 + 9 * (1 / 200 : ℝ) < -1 / 4 - (1 / 12 - 9 * (1 / 200)) / 2 ∧
      (-1 + 1 / 4 : ℝ) ≤ -2 / 3 - 9 * (1 / 200) ∧
      0 < (1 / 200 : ℝ) / (8 * (l + 1)) ∧ (1 / 200 : ℝ) / (8 * (l + 1)) ≤ 1 / 3 ∧
      (1 / 24 : ℝ) < 1 / 12 ∧ (-2 / 3 + 1 / 200 : ℝ) < 0 := by
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hl1 : (0 : ℝ) < l + 1 := by linarith
  refine ⟨by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num, by positivity, ?_,
    by norm_num, by norm_num⟩
  · field_simp
    ring
  · field_simp
    ring
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- The vector of Theorem 12.5 is `edgeQ` with `ϖ = 1` and no eigenvalue beyond the edge. -/
example (N : ℕ) (a : ℝ) (l : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) :
    (fun i : Fin l => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig H (i + 1) - a)) = edgeQ N a 1 0 l H := by
  funext i
  simp [edgeQ]

private lemma aux_aEx_le {N : ℕ} (hN : 1 ≤ N) (k : Fin N) : |specOf (aEx N) k| ≤ 1 / 4 :=
  (abs_specOf_le_norm (aEx_isHermitian N) k).trans (norm_aEx_le hN)

private lemma aux_sb {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : τ ≤ 1 / 2) :
    StandingBoundW τ (specOf (aEx N)) (domW τ N) := by
  intro z hz i
  have h1 := standingBoundW_of_lt hN (aux_aEx_le hN) (by norm_num) z hz.1 i
  linarith

/-- The clamp `x ↦ max(-1, min(x₀, 1))` is bounded by `1` and `1`-Lipschitz. -/
private lemma aux_clamp :
    (∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1) ∧
      LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  refine ⟨fun x => ?_, ((LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).min_const 1).const_max (-1)⟩
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

/-- Theorem 12.5 at the right edge along `(wigRad N, aEx N)` with `τ_A = τ₀ = 1/2`, `C_p = 1`,
`l = 1` and the clamp: the model, `‖A‖` and the standing bound at the existential `τ ≤ 1/2` are
discharged; the laws for `(W^Gauss, D)` and the rigid extremes of `W^Gauss + D` stay hypotheses. -/
example : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    RigidExtremesWAt N ε₁ D₁ (specOf (aEx N)) (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
    |(∫ ω, max (-1) (min ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (wigRad N ω + aEx N) 1 - LpW (specOf (aEx N)))) 1)) -
      (∫ ω, max (-1) (min ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (goeW N ω + diagonal (specOf (aEx N))) 1 - LpW (specOf (aEx N)))) 1))| ≤
      K * (1 + 1) * (N : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, K, N₀, h⟩ :=
    wigner_edge_univ_lip_class (1 / 2) (fun _ => 1) (1 / 2) 1 (by norm_num) (by norm_num)
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, K, N₀, fun N hN hN1 hE hA hR => ?_⟩
  have := h N hN (aEx N) (wigRad N) (aEx_isHermitian N) ((norm_aEx_le hN1).trans (by norm_num))
    (wignerEntries_wigRad hN1).toClass (aux_sb hN1 hτ2) hE hA hR _ 1 1 aux_clamp.1
    aux_clamp.2
  simpa using this

/-- Theorem 12.5 at the left edge along `(wigRad N, aEx N)` with the data of the right-edge example
and the clamp of `N^{2/3}(λ_N - L₋)`; the laws for `(W^Gauss, D)` and the rigid extremes of
`W^Gauss + D` stay hypotheses. -/
example : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    RigidExtremesWAt N ε₁ D₁ (specOf (aEx N)) (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
    |(∫ ω, max (-1) (min ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (wigRad N ω + aEx N) N - LmW (specOf (aEx N)))) 1)) -
      (∫ ω, max (-1) (min ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (goeW N ω + diagonal (specOf (aEx N))) N - LmW (specOf (aEx N)))) 1))| ≤
      K * (1 + 1) * (N : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, K, N₀, h⟩ :=
    wigner_edge_univ_left_lip_class (1 / 2) (fun _ => 1) (1 / 2) 1 (by norm_num) (by norm_num)
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, K, N₀, fun N hN hN1 hE hA hR => ?_⟩
  have := h N hN (aEx N) (wigRad N) (aEx_isHermitian N) ((norm_aEx_le hN1).trans (by norm_num))
    (wignerEntries_wigRad hN1).toClass (aux_sb hN1 hτ2) hE hA hR _ 1 1 aux_clamp.1
    aux_clamp.2
  simpa using this

/-- `f(x) = sin x₀` is `C¹`, bounded by `1`, with `‖f'‖ ≤ 1`. -/
private lemma aux_sin :
    ContDiff ℝ 1 (fun x : Fin 1 → ℝ => Real.sin (x 0)) ∧
      (∀ x : Fin 1 → ℝ, |Real.sin (x 0)| ≤ 1) ∧
      ∀ x : Fin 1 → ℝ, ‖fderiv ℝ (fun x : Fin 1 → ℝ => Real.sin (x 0)) x‖ ≤ 1 := by
  refine ⟨by fun_prop, fun x => Real.abs_sin_le_one _,
    fun x => ?_⟩
  have h0 : HasFDerivAt (fun x : Fin 1 → ℝ => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hd := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  rw [show (fun x : Fin 1 → ℝ => Real.sin (x 0)) = Real.sin ∘ (fun x : Fin 1 → ℝ => x 0)
    from rfl, hd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  simp only [_root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, one_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
    (norm_le_pi_norm v 0)

/-- Theorem 12.5 in the form of §12.1 along `(wigRad N, aEx N)` with `f(x) = sin x₀`; the laws for
`(W^Gauss, D)` and the rigid extremes of `W^Gauss + D` stay hypotheses. -/
example : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    RigidExtremesWAt N ε₁ D₁ (specOf (aEx N)) (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
    |(∫ ω, Real.sin ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (wigRad N ω + aEx N) 1 - LpW (specOf (aEx N))))) -
      (∫ ω, Real.sin ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (goeW N ω + diagonal (specOf (aEx N))) 1 - LpW (specOf (aEx N)))))| ≤
      (N : ℝ) ^ (-c₀) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, c₀, hc₀, h⟩ :=
    wigner_edge_univ (1 / 2) (fun _ => 1) (1 / 2) 1 (by norm_num) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h _ 1 1 aux_sin.1 aux_sin.2.1 aux_sin.2.2
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, c₀, hc₀, N₀, fun N hN hN1 hE hA hR => ?_⟩
  have := hN₀ N hN (aEx N) (wigRad N) (wignerModel_rad hN1) (aux_sb hN1 hτ2) hE hA hR
  simpa using this

/-- Theorem 12.5 at the left edge in the form of §12.1 along `(wigRad N, aEx N)` with
`f(x) = sin x₀`, at `N^{2/3}(λ_N - L₋)`; the laws for `(W^Gauss, D)` and the rigid extremes of
`W^Gauss + D` stay hypotheses. -/
example : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
    RigidExtremesWAt N ε₁ D₁ (specOf (aEx N)) (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
    |(∫ ω, Real.sin ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (wigRad N ω + aEx N) N - LmW (specOf (aEx N))))) -
      (∫ ω, Real.sin ((N : ℝ) ^ (2 / 3 : ℝ) *
          (sortedEig (goeW N ω + diagonal (specOf (aEx N))) N - LmW (specOf (aEx N)))))| ≤
      (N : ℝ) ^ (-c₀) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, c₀, hc₀, h⟩ :=
    wigner_edge_univ_left (1 / 2) (fun _ => 1) (1 / 2) 1 (by norm_num) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h _ 1 1 aux_sin.1 aux_sin.2.1 aux_sin.2.2
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, c₀, hc₀, N₀, fun N hN hN1 hE hA hR => ?_⟩
  have := hN₀ N hN (aEx N) (wigRad N) (wignerModel_rad hN1) (aux_sb hN1 hτ2) hE hA hR
  simpa using this

#print axioms wigner_edge_univ_lip_class
#print axioms wigner_edge_univ
#print axioms wigner_edge_univ_left_lip_class
#print axioms wigner_edge_univ_left

end Anisotropic
