module

public import Anisotropic.Averaged.Defs
public import Anisotropic.Averaged.Main
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.Stability.EdgeSqRoot
public import Anisotropic.Density.Stability.EdgeStab
public import Anisotropic.Density.Stability.Outside
public import Anisotropic.Density.Stability.Quadratic
public import Anisotropic.Density.Varrho
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Entrywise.Improved
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Probability.NormBound.Main
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.Exclusion

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 10.1: `gap_window` (localized), `gap_edgeWin`, `gap_outside` -/

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma gap_norm_sig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) : ‖Sig‖ ≤ τ⁻¹ := by
  have hH := hS.posDef.isHermitian
  set U := hH.eigenvectorUnitary with hU
  have hUm : (U : Matrix (Fin M) (Fin M) ℝ) ∈ unitaryGroup (Fin M) ℝ := U.2
  have hUn : ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    have h1 : ‖(U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ)‖ =
        ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ :=
      l2_opNorm_conjTranspose_mul_self _
    have h2 : (U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ) = 1 := by
      rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.1 hUm)
    have h3 : ‖(1 : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun _ => by simp
    rw [h2] at h1
    nlinarith [norm_nonneg (U : Matrix (Fin M) (Fin M) ℝ)]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  rw [hspec]
  have hD : ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin M) (Fin M) ℝ)‖ ≤ τ⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg (inv_pos.2 hτ).le |>.2 fun i => ?_
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
    rw [abs_of_pos (hS.posDef.eigenvalues_pos i)]
    exact hS.eigenvalues_le i
  have hUs : ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact hUn
  calc _ ≤ ‖(U : Matrix (Fin M) (Fin M) ℝ) * diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
        ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ := l2_opNorm_mul _ _
    _ ≤ (‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) :
          Matrix (Fin M) (Fin M) ℝ)‖) * ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * τ⁻¹) * 1 := by gcongr
    _ = τ⁻¹ := by ring

/-- Every eigenvalue of `Q_N = XᵀΣX` is at most `τ⁻¹ ‖XᵀX‖` under (bound_Sigma). -/
private lemma gap_eig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (Xm : Matrix (Fin M) (Fin N) ℝ) (j : Fin N) :
    specOf (QN Sig Xm) j ≤ τ⁻¹ * ‖Xmᵀ * Xm‖ := by
  have hQ : (QN Sig Xm).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Xm hS.posDef.isHermitian
    simpa [QN, conjTranspose_eq_transpose_of_trivial] using this
  rw [specOf_eq hQ]
  have : Nonempty (Fin N) := ⟨j⟩
  have : NormOneClass (Matrix (Fin N) (Fin N) ℝ) :=
    ⟨by rw [← diagonal_one, l2_opNorm_diagonal]; exact norm_one⟩
  have : CompleteSpace (Matrix (Fin N) (Fin N) ℝ) := FiniteDimensional.complete ℝ _
  have h1 : hQ.eigenvalues j ≤ ‖QN Sig Xm‖ := by
    have := spectrum.norm_le_norm_of_mem (hQ.eigenvalues_mem_spectrum_real j)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  refine h1.trans ?_
  have hT : ‖Xmᵀ‖ = ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
  have hXX : ‖Xmᵀ * Xm‖ = ‖Xm‖ * ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self]
  have hSn := gap_norm_sig_le hτ hS
  calc ‖QN Sig Xm‖ ≤ ‖Xmᵀ * Sig‖ * ‖Xm‖ := l2_opNorm_mul _ _
    _ ≤ (‖Xmᵀ‖ * ‖Sig‖) * ‖Xm‖ := mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (‖Xm‖ * τ⁻¹) * ‖Xm‖ := by rw [hT]; gcongr
    _ = τ⁻¹ * ‖Xmᵀ * Xm‖ := by rw [hXX]; ring

/-- `τ'(τ) > 0` (the window of Lemmas A.4 and A.5). -/
private lemma gap_edgeTau'_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau' τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  unfold edgeTau' edgeTau0
  positivity

/-- The constant of (mz_reg) on `𝐃^o(τ, τ')` is positive. -/
private lemma gap_outMz_pos {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ') : 0 < outMz τ τ' := by
  unfold outMz outcr outImLower
  positivity

/-- The points of the domain of Lemma 10.1 that lie in `𝐃^o(τ₀, τ'')` or in `𝐃^e_l(τ₀, τ'')`
for an edge `a_l` regular at `τ₀`. -/
private def gapT (τ₀ τ'' ε : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Set ℂ :=
  {z | z ∈ gapDomain τ₀ ε N σ ∧ (z ∈ outsideDomain τ₀ τ'' N σ ∨
    ∃ l, RegularEdge τ₀ N σ l ∧ z ∈ edgeDomain τ₀ τ'' N σ l)}

/-- The constant `C_up` of the bound `Im m ≤ C_up η/√(κ + η)` on the domain of Lemma 10.1. -/
private def gapCup (τ₀ τ'' : ℝ) : ℝ := max (sqUpper τ₀) (τ''⁻¹ ^ 2 * √(kappaMax τ₀ + τ₀⁻¹))

/-- `C_up ≥ 0`. -/
private lemma gapCup_nonneg (τ₀ τ'' : ℝ) : 0 ≤ gapCup τ₀ τ'' :=
  le_trans (by positivity) (le_max_right _ _)

/-- (im_m_asymp), upper half, on the domain of Lemma 10.1: `Im m ≤ C_up η/√(κ + η)`, from
(m_sq_root) near a regular edge (Lemma A.4) and (im_m_outside) on `𝐃^o` (Lemma A.8). -/
private lemma gap_im_le {τ₀ τ'' ε : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ₀ N σ)
    (hτ'' : 0 < τ'') (hτ''le : τ'' ≤ edgeTau' τ₀) {z : ℂ}
    (hz : z ∈ gapDomain τ₀ ε N σ ∧ (z ∈ outsideDomain τ₀ τ'' N σ ∨
      ∃ l, RegularEdge τ₀ N σ l ∧ z ∈ edgeDomain τ₀ τ'' N σ l)) :
    (mFun N σ z).im ≤ gapCup τ₀ τ'' * (z.im / √(kappa N σ z.re + z.im)) := by
  obtain ⟨hg, hr⟩ := hz
  have hy : 0 < z.im := hg.1.1
  have hq : 0 ≤ z.im / √(kappa N σ z.re + z.im) := by positivity
  rcases hr with ho | ⟨l, hl, he⟩
  · have h1 := (im_m_outside h hτ'' ho).2
    have hκ0 : 0 ≤ kappa N σ z.re := kappa_nonneg N σ z.re
    have hK : kappa N σ z.re + z.im ≤ kappaMax τ₀ + τ₀⁻¹ :=
      add_le_add (kappa_le h hg.1.2.2.1) hg.1.2.2.2.2
    have hs0 : 0 < √(kappa N σ z.re + z.im) := Real.sqrt_pos.2 (by linarith)
    have hs : √(kappa N σ z.re + z.im) ≤ √(kappaMax τ₀ + τ₀⁻¹) := Real.sqrt_le_sqrt hK
    calc (mFun N σ z).im ≤ z.im / τ'' ^ 2 := h1
      _ = τ''⁻¹ ^ 2 * z.im := by rw [inv_pow]; ring
      _ ≤ τ''⁻¹ ^ 2 * (√(kappaMax τ₀ + τ₀⁻¹) * (z.im / √(kappa N σ z.re + z.im))) := by
          gcongr
          rw [mul_div_assoc', le_div_iff₀ hs0]
          exact mul_le_mul_of_nonneg_right hs hy.le |>.trans_eq' (mul_comm _ _)
      _ = τ''⁻¹ ^ 2 * √(kappaMax τ₀ + τ₀⁻¹) * (z.im / √(kappa N σ z.re + z.im)) := by ring
      _ ≤ gapCup τ₀ τ'' * (z.im / √(kappa N σ z.re + z.im)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hq
  · have h1 := ((m_sq_root_edge h hl hτ''le he).2 hg.2.1).2
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)

/-- The intersection of two spectral domains (Definition 3.20) is a spectral domain. -/
private lemma gap_spectral_inter {τ : ℝ} {S T : Set ℂ} (hS : SpectralDomain τ N S)
    (hT : SpectralDomain τ N T) : SpectralDomain τ N (S ∩ T) :=
  ⟨fun _ hz => hS.1 hz.1, fun z hz w hw hre hle =>
    ⟨hS.2 z hz.1 w hw hre hle, hT.2 z hz.2 w hw hre hle⟩⟩

/-- The averaged law with `Φ = (κ + η)^{−1/2} Ψ²` at level `ε/8` at every point of the domain of
Lemma 10.1 lying in `𝐃^o(τ₀, τ'')` or in `𝐃^e_l(τ₀, τ'')` with `a_l` regular at `τ₀`
(proof of Lemma 10.1: (improved_avg_G) for diagonal `Σ` and Proposition 9.1). -/
private lemma gap_law (τ₀ τ'' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ₀ : 0 < τ₀) (hτ₀4 : τ₀ ≤ 1 / 4)
    (hτ'' : 0 < τ'') (hτ''le : τ'' ≤ edgeTau' τ₀) (hε : 0 < ε) (hε2 : ε < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ₀ C M N Sig X → ∀ z ∈ gapT τ₀ τ'' ε N (specOf Sig),
        ODomAt N (ε / 8) (D + 2) (fun ω => mN Sig (X ω) z - mFun N (specOf Sig) z)
          (fun _ => gapPhi N (specOf Sig) z) := by
  have hCm := mBoundConst_pos hτ₀
  have hTp := gap_edgeTau'_pos hτ₀
  set ce := oneXmConst (edgeMz τ₀) (mBoundConst τ₀) with hce
  set co := oneXmConst (outMz τ₀ τ'') (mBoundConst τ₀) with hco
  have hce0 : 0 < ce := by
    rw [hce]; unfold oneXmConst edgeMz; positivity
  have hmz := gap_outMz_pos hτ₀ hτ''
  have hco0 : 0 < co := by
    rw [hco]; unfold oneXmConst; positivity
  set cx := min ce co with hcx
  have hcx0 : 0 < cx := lt_min hce0 hco0
  set cΦ := (kappaMax τ₀ + τ₀⁻¹) ^ (-(1 / 2 : ℝ)) with hcΦ
  have hK0 : 0 < kappaMax τ₀ + τ₀⁻¹ := by unfold kappaMax; positivity
  have hcΦ0 : 0 < cΦ := Real.rpow_pos_of_pos hK0 _
  set Cup := gapCup τ₀ τ'' with hCup
  obtain ⟨ε₁, D₁, hε₁, N₁, hP⟩ := prop_gen_avg τ₀ cx cΦ C (ε / 8) (D + 2) hτ₀ hcx0 hcΦ0
    (by positivity)
  obtain ⟨N₂, hPhi⟩ := phiCond_gap τ₀ ε Cup hτ₀ hτ₀4 hε hε2
  -- edge regions
  set C0w := edgeC0wmin τ₀
  set C0s := edgeC0min τ₀
  obtain ⟨N₃, hGe⟩ := gauss_avg_input τ₀ cx C0w (edgeC1w τ₀ C0w) (edgeK0w τ₀ C0w) ε₁ D₁ hτ₀
    hcx0 hε₁
  obtain ⟨N₄, hIe⟩ := improved_avg_diag τ₀ cx C0w (edgeC1w τ₀ C0w) (edgeK0w τ₀ C0w) C0s
    (edgeC1 τ₀ C0s) (edgeK0 τ₀ C0s) gaussMoment ε₁ D₁ hτ₀ hcx0 hε₁
  obtain ⟨N₅, hSWe⟩ := stab_edge2_weak (τ := τ₀) hτ'' hτ''le le_rfl
  obtain ⟨N₆, hSSe⟩ := stab_edge2 (τ := τ₀) hτ'' hτ''le le_rfl
  -- outside region
  set O0w := outC0wmin τ₀ τ''
  set O0s := outC0min τ₀ τ''
  obtain ⟨N₇, hGo⟩ := gauss_avg_input τ₀ cx O0w 1 1 ε₁ D₁ hτ₀ hcx0 hε₁
  obtain ⟨N₈, hIo⟩ := improved_avg_diag τ₀ cx O0w 1 1 O0s 1 1 gaussMoment ε₁ D₁ hτ₀ hcx0 hε₁
  obtain ⟨N₉, hSWo⟩ := stab_outside_weak (τ := τ₀) (C₁ := 1) (K₀ := 1) hτ'' le_rfl
  obtain ⟨N₁₀, hSSo⟩ := stab_outside (τ := τ₀) (C₁ := 1) (K₀ := 1) hτ'' le_rfl
  refine ⟨max 1 (max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max (max N₇ N₈)
    (max N₉ N₁₀)))), fun N hN Ω _ _ M Sig X hm z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨hN1, ⟨⟨hN₁, hN₂⟩, hN₃, hN₄⟩, ⟨hN₅, hN₆⟩, ⟨hN₇, hN₈⟩, hN₉, hN₁₀⟩ := hN
  set σ := specOf Sig with hσ
  have hD : DensityAssumptions τ₀ N σ := hm.diagModel_specOf.densityAssumptions hτ₀
  have hmG : IsModel τ₀ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  -- the law on `S ∩ gapDomain` from the Gaussian inputs on a full region `S`
  have key : ∀ S : Set ℂ, SpectralDomain τ₀ N S → OneXmOn cx N σ S →
      EntrywiseLawAt N ε₁ D₁ (diagonal σ) (gaussX M N) S →
      (∀ w ∈ S, ODomAt N ε₁ D₁ (fun ω => mN (diagonal σ) (gaussX M N ω) w - mFun N σ w)
        (fun _ => (kappa N σ w.re + w.im) ^ (-(1 / 2 : ℝ)) * Psi N σ w ^ 2)) →
      S ∩ gapDomain τ₀ ε N σ ⊆ gapT τ₀ τ'' ε N σ → z ∈ S ∩ gapDomain τ₀ ε N σ →
      ODomAt N (ε / 8) (D + 2) (fun ω => mN Sig (X ω) z - mFun N σ z)
        (fun _ => gapPhi N σ z) := by
    intro S hS hx hEnt hImp hsub hzS
    have hS' := gap_spectral_inter hS (spectralDomain_gapDomain τ₀ ε N σ)
    have hPC : PhiCond τ₀ cΦ N σ (S ∩ gapDomain τ₀ ε N σ) (gapPhi N σ) :=
      hPhi N hN₂ σ _ hD Set.inter_subset_right fun w hw =>
        gap_im_le hD hτ'' hτ''le (hsub hw)
    have hAvg : AveragedPhiLawAt N ε₁ D₁ (diagonal σ) (gaussX M N) (S ∩ gapDomain τ₀ ε N σ)
        (gapPhi N σ) := by
      intro w hw
      have := hImp w hw.1
      unfold ODomAt at this ⊢
      rw [mFun_specOf_diagonal]
      exact this
    exact hP N hN₁ M Sig X _ (gapPhi N σ) hm hS' (fun w hw => hx w hw.1) hPC
      (fun w hw => hEnt w hw.1) hAvg z hzS
  obtain ⟨hzg, hzr⟩ := hz
  rcases hzr with ho | ⟨l, hl, he⟩
  · set S := outsideDomain τ₀ τ'' N σ
    have hSd : SpectralDomain τ₀ N S := spectralDomain_outsideDomain τ₀ τ'' N σ
    have hx : OneXmOn cx N σ S := fun w hw i => by
      have h1 := one_add_mul_ge_of_mz_reg hD.nonneg hmz hCm
        (gen_prop_m_specDomain hD hw.1).2.1 (mz_reg_outside hD hτ'' hw) i
      exact (min_le_right _ _).trans h1
    have hSt := hSWo N hN₉ σ hD
    have hSSt := hSSo N hN₁₀ σ hD
    have hEnt := (hGo N hN₇ M Sig S hmG hSd hx hSt).1
    have hImp := hIo N hN₈ M σ (gaussX M N) S hmG.diagModel_specOf hSd hx hSt hSSt
    exact key S hSd hx hEnt hImp (fun w hw => ⟨hw.2, Or.inl hw.1⟩) ⟨ho, hzg⟩
  · set S := edgeDomain τ₀ τ'' N σ l
    have hSd : SpectralDomain τ₀ N S := spectralDomain_edgeDomain τ₀ τ'' N σ l
    have hx : OneXmOn cx N σ S := fun w hw i =>
      (min_le_left _ _).trans (one_add_mul_mFun_edge hD hl hτ''le hw i)
    have hSt := hSWe N hN₅ σ l hD hl
    have hSSt := hSSe N hN₆ σ l hD hl
    have hEnt := (hGe N hN₃ M Sig S hmG hSd hx hSt).1
    have hImp := hIe N hN₄ M σ (gaussX M N) S hmG.diagModel_specOf hSd hx hSt hSSt
    exact key S hSd hx hEnt hImp (fun w hw => ⟨hw.2, Or.inr ⟨l, hl, hw.1⟩⟩) ⟨he, hzg⟩

/-- `N^{1/3} ≥ 2` for `N ≥ 8`. -/
private lemma gap_two_le {n : ℝ} (hn : 8 ≤ n) : 2 ≤ n ^ (1 / 3 : ℝ) := by
  have h8 : (8 : ℝ) = 2 ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc (2 : ℝ) = (2 ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ n ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) (h8 ▸ hn) (by norm_num)

/-- `2/N ≤ N^{−2/3+ε}` for `N ≥ 8`. -/
private lemma gap_hNbig {n ε : ℝ} (hn : 8 ≤ n) (hε : 0 < ε) : 2 / n ≤ n ^ (-2 / 3 + ε) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : n ^ (-2 / 3 : ℝ) ≤ n ^ (-2 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine le_trans ?_ h1
  have h2 := gap_two_le hn
  have h3 : n ^ (-2 / 3 : ℝ) * n = n ^ (1 / 3 : ℝ) := by
    rw [mul_comm, ← Real.rpow_one_add' hn0.le (by norm_num)]; norm_num
  rw [div_le_iff₀ hn0, h3]
  exact h2

/-- `η = N^{−1/2−ε/4} κ^{1/4} ≥ N^{−1+τ₀}` once `κ ≥ N^{−2/3+ε}/2`, `N ≥ 8` and `τ₀ ≤ 1/4`. -/
private lemma gap_eta_low {n ε τ₀ κ : ℝ} (hn : 8 ≤ n) (hτ₀ : τ₀ ≤ 1 / 4)
    (hκ : n ^ (-2 / 3 + ε) / 2 ≤ κ) :
    n ^ (-1 + τ₀) ≤ n ^ (-1 / 2 - ε / 4) * κ ^ (1 / 4 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  set a := n ^ (-2 / 3 + ε) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn0 _
  have h1 : (a / 2) ^ (1 / 4 : ℝ) ≤ κ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hκ (by norm_num)
  have h2 : n ^ (-1 / 2 - ε / 4) * (a / 2) ^ (1 / 4 : ℝ) =
      n ^ (-2 / 3 : ℝ) / 2 ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow ha0.le (by norm_num), ha, ← Real.rpow_mul hn0.le, mul_div_assoc',
      ← Real.rpow_add hn0]
    congr 2
    ring
  have h3 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ n ^ (1 / 12 : ℝ) := by
    have := Real.rpow_le_rpow (by norm_num) (gap_two_le hn) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_mul hn0.le, show (1 / 3 : ℝ) * (1 / 4) = 1 / 12 by norm_num] at this
  have h4 : n ^ (-1 + τ₀) ≤ n ^ (-3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h5 : n ^ (-3 / 4 : ℝ) ≤ n ^ (-2 / 3 : ℝ) / 2 ^ (1 / 4 : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    calc n ^ (-3 / 4 : ℝ) * 2 ^ (1 / 4 : ℝ) ≤ n ^ (-3 / 4 : ℝ) * n ^ (1 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = n ^ (-2 / 3 : ℝ) := by rw [← Real.rpow_add hn0]; norm_num
  calc n ^ (-1 + τ₀) ≤ n ^ (-2 / 3 : ℝ) / 2 ^ (1 / 4 : ℝ) := h4.trans h5
    _ = n ^ (-1 / 2 - ε / 4) * (a / 2) ^ (1 / 4 : ℝ) := h2.symm
    _ ≤ n ^ (-1 / 2 - ε / 4) * κ ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `η = N^{−1/2−ε/4} κ^{1/4} ≤ τ₀⁻¹` for `0 ≤ κ ≤ C_κ(τ₀)`, `N ≥ 1`, `τ₀ ≤ 1/4`. -/
private lemma gap_eta_up {n ε τ₀ κ : ℝ} (hn1 : 1 ≤ n) (hε : 0 < ε) (hτ₀ : 0 < τ₀)
    (hτ₀4 : τ₀ ≤ 1 / 4) (hκ0 : 0 ≤ κ) (hκ : κ ≤ kappaMax τ₀) :
    n ^ (-1 / 2 - ε / 4) * κ ^ (1 / 4 : ℝ) ≤ τ₀⁻¹ := by
  set t := τ₀⁻¹ with ht
  have ht4 : 4 ≤ t := by
    rw [ht, le_inv_comm₀ (by norm_num) hτ₀]; linarith
  have hK : kappaMax τ₀ ≤ t ^ 4 := by
    unfold kappaMax; rw [← ht]
    have h2 : 16 ≤ t ^ 2 := by nlinarith
    have h3 : 16 * t ^ 2 ≤ t ^ 4 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg t)
      nlinarith
    nlinarith
  have h1 : n ^ (-1 / 2 - ε / 4) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have h2 : κ ^ (1 / 4 : ℝ) ≤ t := by
    calc κ ^ (1 / 4 : ℝ) ≤ (t ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hκ0 (hκ.trans hK) (by norm_num)
      _ = t := by
          rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by linarith) (by norm_num)
  calc n ^ (-1 / 2 - ε / 4) * κ ^ (1 / 4 : ℝ) ≤ 1 * t :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = t := one_mul t

/-- A point `E ∉ supp ϱ` within `r < E` of `supp ϱ` lies within `r` of an edge `a_l`. -/
private lemma gap_near_edge {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E y r : ℝ} (hE : E ∉ (varrho N σ).support)
    (hy : y ∈ (varrho N σ).support) (hEy : |E - y| < r) (hr : r < E) :
    ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ |E - edgeVal N σ l| < r := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hEy
  have hy0 : 0 < y := by linarith
  have hE0 : 0 < E := by linarith
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ hσ hN hS hy0).1 hy
  have hEk : E ∉ Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) := fun hm =>
    hE ((mem_support_varrho_iff N σ hσ hN hS hE0).2 ⟨k, hk1, hk2, hm⟩)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hEk
  rcases hEk with hlo | hhi
  · refine ⟨2 * k, by omega, by omega, abs_lt.2 ⟨by linarith [hyk.1], by linarith [hyk.1]⟩⟩
  · refine ⟨2 * k - 1, by omega, by omega, abs_lt.2 ⟨by linarith [hyk.2], by linarith [hyk.2]⟩⟩

/-- The core of Lemma 10.1 at fixed `N`: w.h.p., an eigenvalue of `Q` in `W ⊆ [τ_W, ∞)` at
distance `≥ N^{−2/3+ε}` from `supp ϱ` is within `w` of `supp ϱ` and comes with an edge `a_l`
within `τ/4` of `W` that is not regular at `τ/2`. -/
private lemma gap_core (τ : ℝ) (C : ℕ → ℝ) (ε D τW w : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε2 : ε < 2 / 3) (hτW : 0 < τW) (hw : 0 < w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (W : Set ℝ),
      IsModel τ C M N Sig X → W ⊆ Set.Ici τW →
      HighProbAt N D {ω | ∀ j, specOf (QN Sig (X ω)) j ∈ W →
        (N : ℝ) ^ (-2 / 3 + ε) ≤
          Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support →
        Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support < w ∧
          ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N (specOf Sig) ∧
            Metric.infDist (edgeVal N (specOf Sig) l) W ≤ τ / 4 ∧
            ¬ RegularEdge (τ / 2) N (specOf Sig) l} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X W hm _ => absurd hm.tau_le_one hτ1⟩
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  set C0 := max C₀ 0 with hC0
  have hC00 : 0 ≤ C0 := le_max_right _ _
  have hA : 0 < τ⁻¹ * C0 + 1 := by positivity
  set τ₀ := min (min (τW / 2) (τ / 4)) (min (1 / 4) ((τ⁻¹ * C0 + 1)⁻¹)) with hτ₀
  have hτ₀0 : 0 < τ₀ := by positivity
  have hτ₀W : τ₀ ≤ τW / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hτ₀τ : τ₀ ≤ τ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hτ₀4 : τ₀ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₀C : τ⁻¹ * C0 + 1 ≤ τ₀⁻¹ := by
    have : τ₀ ≤ (τ⁻¹ * C0 + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
    exact (le_inv_comm₀ hτ₀0 hA).1 this
  have hTp := gap_edgeTau'_pos hτ₀0
  set τ'' := min (min (edgeTau' τ₀) (τ / 8)) (min (τ₀ / 2) (w / 2)) with hτ''
  have hτ''0 : 0 < τ'' := by positivity
  have hτ''e : τ'' ≤ edgeTau' τ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hτ''τ : τ'' ≤ τ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hτ''2 : τ'' ≤ τ₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ''w : τ'' ≤ w / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁, hNorm⟩ := hC₀ C (D + 1)
  obtain ⟨N₂, hLaw⟩ := gap_law τ₀ τ'' C ε D hτ₀0 hτ₀4 hτ''0 hτ''e hε hε2
  obtain ⟨N₃, hEx⟩ := gap_exclusion ε (gapCup τ₀ τ'') hε hε2 (gapCup_nonneg _ _)
  refine ⟨max (max (max N₁ N₂) (max N₃ ⌈8 / τ⌉₊)) (max (max ⌈2 / w⌉₊ ⌈τ₀⁻¹ + 3⌉₊) 8),
    fun N hN Ω _ _ M Sig X W hm hW => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN₁, hN₂⟩, hN₃, hN₄⟩, ⟨hN₅, hN₆⟩, hN8⟩ := hN
  have hn8 : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by omega
  have hNτ : 1 / (N : ℝ) ≤ τ / 8 := by
    have h1 : 8 / τ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN₄)
    rw [div_le_iff₀ hτ] at h1
    rw [div_le_iff₀ hn0]; linarith
  have hNw : 1 / (N : ℝ) ≤ w / 2 := by
    have h1 : 2 / w ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN₅)
    rw [div_le_iff₀ hw] at h1
    rw [div_le_iff₀ hn0]; linarith
  have hNτ₀ : τ₀⁻¹ + 3 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN₆)
  have hNτ₀' : 1 / (N : ℝ) ≤ τ₀ := by
    rw [div_le_iff₀ hn0]
    have h1 : τ₀ * (τ₀⁻¹ + 3) ≤ τ₀ * N := mul_le_mul_of_nonneg_left hNτ₀ hτ₀0.le
    rw [mul_add, mul_inv_cancel₀ hτ₀0.ne'] at h1
    linarith
  have hNbig := gap_hNbig hn8 hε
  set σ := specOf Sig with hσ
  have hm₀ : IsModel τ₀ C M N Sig X := hm.mono hτ₀0 (by linarith)
  have hdm := hm₀.diagModel_specOf
  have hDA : DensityAssumptions τ₀ N σ := hdm.densityAssumptions hτ₀0
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      have := hm.ratio_ge
      rw [h0, Nat.cast_zero, zero_div] at this
      linarith
    · exact h0
  have hS : (posVals σ).Nonempty := by
    refine ⟨σ ⟨0, hM⟩, ?_⟩
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨⟨0, hM⟩, rfl⟩, hdm.pos _⟩
  -- the grid `E_k = k/N`, `η(E) = N^{−1/2−ε/4} κ(E)^{1/4}`, and the events
  set η : ℝ → ℝ := fun E => (N : ℝ) ^ (-1 / 2 - ε / 4) * kappa N σ E ^ (1 / 4 : ℝ) with hη
  set zk : ℕ → ℂ := fun k => ⟨(k : ℝ) / N, η ((k : ℝ) / N)⟩ with hzk
  set L : ℕ := ⌈τ₀⁻¹ * N⌉₊ + 1 with hL
  set G := (Finset.range L).filter (fun k => zk k ∈ gapT τ₀ τ'' ε N σ) with hG
  set Bad : ℕ → Set Ω := fun k => {ω | (N : ℝ) ^ (ε / 8) * gapPhi N σ (zk k) <
    ‖mN Sig (X ω) (zk k) - mFun N σ (zk k)‖} with hBad
  set NormE : Set Ω := {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} with hNormE
  have hK : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rwa [div_le_iff₀ hn0] at this
  have hPN : ℙ NormEᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := hNorm N hN₁ M X hm.entries hK
  have hPB : ∀ k ∈ G, ℙ (Bad k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := fun k hk =>
    hLaw N hN₂ M Sig X hm₀ (zk k) (Finset.mem_filter.1 hk).2
  have hcard : (G.card : ℝ) ≤ τ₀⁻¹ * N + 2 := by
    have h1 : G.card ≤ L := (Finset.card_filter_le _ _).trans (Finset.card_range L).le
    have h2 : (L : ℝ) ≤ τ₀⁻¹ * N + 2 := by
      rw [hL]; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ τ₀⁻¹ * (N : ℝ) by positivity)
      linarith
    exact (Nat.cast_le.2 h1).trans h2
  unfold HighProbAt
  calc ℙ _ ≤ ℙ (NormEᶜ ∪ ⋃ k ∈ G, Bad k) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        refine hω ?_
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_not,
          not_exists] at hcon
        obtain ⟨hωN, hωG⟩ := hcon
        intro j hjW hdist
        set lam := specOf (QN Sig (X ω)) j with hlam
        have hlamW : τW ≤ lam := hW hjW
        have hlamU : lam ≤ τ⁻¹ * C0 :=
          (gap_eig_le hτ hm.sigma (X ω) j).trans (mul_le_mul_of_nonneg_left
            ((show ‖(X ω)ᵀ * X ω‖ ≤ C₀ from hωN).trans (le_max_left _ _)) (inv_pos.2 hτ).le)
        have hlam0 : 0 ≤ lam * N := mul_nonneg (by linarith) hn0.le
        set k := ⌊lam * N⌋₊ with hk
        have hkc : (k : ℝ) = ((⌊lam * N⌋ : ℤ) : ℝ) := natCast_floor_eq_intCast_floor hlam0
        have hfl1 : (k : ℝ) ≤ lam * N := Nat.floor_le hlam0
        have hfl2 : lam * N < k + 1 := Nat.lt_floor_add_one _
        set E' : ℝ := (k : ℝ) / N with hE'
        have hE'le : E' ≤ lam := by rw [hE', div_le_iff₀ hn0]; exact hfl1
        have hE'ge : lam - 1 / N < E' := by
          rw [hE', lt_div_iff₀ hn0, sub_mul, one_div, inv_mul_cancel₀ hn0.ne']; linarith
        obtain ⟨hEs, hκ, hlE⟩ := gap_grid hDA hε hε2 hNbig hdist
        rw [← hkc] at hEs hκ hlE
        have hE'τ₀ : τ₀ ≤ E' := by linarith
        have hE'up : E' ≤ τ₀⁻¹ := by linarith
        have hE'abs : |E'| ≤ τ₀⁻¹ := abs_le.2 ⟨by linarith [inv_pos.2 hτ₀0], hE'up⟩
        have hκpos : 0 < kappa N σ E' :=
          lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hn0 (-2 / 3 + ε); positivity) hκ
        have hκU := kappa_le hDA hE'abs
        set z' := zk k with hz'
        have hηpos : 0 < η E' := by
          have := Real.rpow_pos_of_pos hκpos (1 / 4 : ℝ)
          have := Real.rpow_pos_of_pos hn0 (-1 / 2 - ε / 4)
          positivity
        have hspec : z' ∈ specDomain τ₀ N := by
          refine ⟨hηpos, ?_, hE'abs, gap_eta_low hn8 hτ₀4 hκ,
            gap_eta_up hn1 hε hτ₀0 hτ₀4 hκpos.le hκU⟩
          exact hE'τ₀.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z'))
        have hgd : z' ∈ gapDomain τ₀ ε N σ := ⟨hspec, hEs, hκ, le_rfl⟩
        have hcontra : z' ∈ gapT τ₀ τ'' ε N σ → False := by
          intro hT
          have hkG : k ∈ G := by
            refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hT⟩
            have h1 : lam * N ≤ τ₀⁻¹ * N := mul_le_mul_of_nonneg_right (by linarith) hn0.le
            have : k ≤ ⌈τ₀⁻¹ * N⌉₊ := (Nat.floor_mono h1).trans (Nat.floor_le_ceil _)
            omega
          have hle : ‖mN Sig (X ω) z' - mFun N σ z'‖ ≤ (N : ℝ) ^ (ε / 8) * gapPhi N σ z' :=
            not_lt.1 (hωG k hkG)
          have hIm := gap_im_le hDA hτ''0 hτ''e hT
          have hex := hEx N hN₃ σ z' hκ rfl hIm
          have hpos : 0 < z'.im := hηpos
          have hlow := im_empStieltjes_ge (specOf (QN Sig (X ω))) hpos j hlE
          rw [← mN_eq_empStieltjes hm.sigma.posDef (X ω) hpos] at hlow
          have hdiff : (mN Sig (X ω) z').im ≤
              (mFun N σ z').im + ‖mN Sig (X ω) z' - mFun N σ z'‖ := by
            have := Complex.im_le_norm (mN Sig (X ω) z' - mFun N σ z')
            rw [Complex.sub_im] at this
            linarith
          linarith
        have hsne : (varrho N σ).support.Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, Metric.infDist_empty] at hdist
          have := Real.rpow_pos_of_pos hn0 (-2 / 3 + ε)
          linarith
        by_cases hout : τ'' ≤ Metric.infDist E' (varrho N σ).support
        · exact (hcontra ⟨hgd, Or.inl ⟨hspec, hout⟩⟩).elim
        · obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hsne).1 (not_le.1 hout)
          rw [Real.dist_eq] at hdy
          obtain ⟨l, hl1, hl2, hEl⟩ := gap_near_edge hDA.nonneg hNpos hS hEs hy hdy
            (by linarith)
          have hlE' : |lam - E'| < 1 / N := abs_lt.2 ⟨by linarith, by linarith⟩
          have hwd : Metric.infDist lam (varrho N σ).support < w := by
            calc Metric.infDist lam (varrho N σ).support ≤ dist lam y :=
                  Metric.infDist_le_dist_of_mem hy
              _ ≤ |lam - E'| + |E' - y| := by rw [Real.dist_eq]; exact abs_sub_le _ _ _
              _ < w := by linarith
          have hWd : Metric.infDist (edgeVal N σ l) W ≤ τ / 4 := by
            calc Metric.infDist (edgeVal N σ l) W ≤ dist (edgeVal N σ l) lam :=
                  Metric.infDist_le_dist_of_mem hjW
              _ ≤ |edgeVal N σ l - E'| + |E' - lam| := by
                  rw [Real.dist_eq]; exact abs_sub_le _ _ _
              _ ≤ τ / 4 := by
                  rw [abs_sub_comm (edgeVal N σ l), abs_sub_comm E' lam]; linarith
          by_cases hreg : RegularEdge (τ / 2) N σ l
          · obtain ⟨h1, h2⟩ := abs_lt.1 hEl
            exact (hcontra ⟨hgd, Or.inr ⟨l, regularEdge_mono hreg (by linarith), hspec,
              ⟨by linarith, by linarith⟩⟩⟩).elim
          · exact ⟨hwd, l, hl1, hl2, hWd, hreg⟩
    _ ≤ ℙ NormEᶜ + ℙ (⋃ k ∈ G, Bad k) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ∑ k ∈ G, ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
        add_le_add hPN ((measure_biUnion_finset_le G Bad).trans (Finset.sum_le_sum hPB))
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set x := (N : ℝ) ^ (-D) with hx
        have hx0 : 0 < x := Real.rpow_pos_of_pos hn0 _
        have e1 : (N : ℝ) ^ (-(D + 1)) = x / N := by
          rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hn0, Real.rpow_neg_one]; ring
        have e2 : (N : ℝ) ^ (-(D + 2)) = x / N ^ 2 := by
          rw [show -(D + 2) = -D + -2 by ring, Real.rpow_add hn0, Real.rpow_neg hn0.le (2 : ℝ),
            Real.rpow_two]; ring
        have hq : (N : ℝ) + (τ₀⁻¹ * N + 2) ≤ (N : ℝ) ^ 2 := by nlinarith
        rw [e1, e2]
        calc x / N + G.card * (x / N ^ 2) ≤ x / N + (τ₀⁻¹ * N + 2) * (x / N ^ 2) := by
              gcongr
          _ = x * (N + (τ₀⁻¹ * N + 2)) / N ^ 2 := by field_simp
          _ ≤ x * N ^ 2 / N ^ 2 := by gcongr
          _ = x := by field_simp

/-- Lemma 10.1 (`lem:gap`) at fixed `N`, localized: in a window `W ⊆ [τ_W, ∞)` whose nearby
edges are regular at `τ/2`, every eigenvalue of `Q` lies within `N^{−2/3+ε}` of `supp ϱ`. -/
theorem gap_window (τ : ℝ) (C : ℕ → ℝ) (ε D τW : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε2 : ε < 2 / 3)
    (hτW : 0 < τW) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (W : Set ℝ),
      IsModel τ C M N Sig X → W ⊆ Set.Ici τW →
      (∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) →
        Metric.infDist (edgeVal N (specOf Sig) l) W ≤ τ / 4 →
          RegularEdge (τ / 2) N (specOf Sig) l) →
      HighProbAt N D {ω | ∀ j, specOf (QN Sig (X ω)) j ∈ W →
        Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support <
          (N : ℝ) ^ (-2 / 3 + ε)} := by
  obtain ⟨N₀, h⟩ := gap_core τ C ε D τW 1 hτ hε hε2 hτW one_pos
  refine ⟨N₀, fun N hN Ω _ _ M Sig X W hm hW hreg => ?_⟩
  have hc := h N hN M Sig X W hm hW
  unfold HighProbAt at hc ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 fun ω hω j hj => ?_)) hc
  by_contra hlt
  obtain ⟨-, l, hl1, hl2, hlW, hnreg⟩ := hω j hj (not_lt.1 hlt)
  exact hnreg (hreg l hl1 hl2 hlW)

/-- Lemma 10.1 under the edge hypothesis of Theorem 3.12 (every edge with `a_k ≥ τ/2` regular at `τ/2`), on the window `edgeWin τ`
(which contains `[3τ/4, ∞)`). -/
theorem gap_edgeWin (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε2 : ε < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      HighProbAt N D {ω | ∀ j, specOf (QN Sig (X ω)) j ∈ edgeWin τ N (specOf Sig) →
        Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support <
          (N : ℝ) ^ (-2 / 3 + ε)} := by
  obtain ⟨N₀, h⟩ := gap_window τ C ε D (3 * τ / 8) hτ hε hε2 (by positivity)
  refine ⟨N₀, fun N hN Ω _ _ M Sig X hm hedge => h N hN M Sig X _ hm ?_ ?_⟩
  · rintro E (hE | ⟨k, -, -, hk, hEk⟩)
    · exact le_trans (by linarith) (Set.mem_Ici.1 hE)
    · exact Set.mem_Ici.2 (by linarith [(abs_le.1 hEk).1])
  · intro l hl1 hl2 hlW
    refine hedge l hl1 hl2 ?_
    by_contra hlt
    rw [not_le] at hlt
    set δ := min (τ / 16) (τ / 2 - edgeVal N (specOf Sig) l) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
    have hne : (edgeWin τ N (specOf Sig)).Nonempty := ⟨3 * τ / 4, Or.inl (Set.mem_Ici.2 le_rfl)⟩
    obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hne).1 (show
      Metric.infDist (edgeVal N (specOf Sig) l) (edgeWin τ N (specOf Sig)) < τ / 4 + δ by
        linarith)
    rw [Real.dist_eq] at hdy
    have h1 := (abs_lt.1 hdy).1
    have h2 := (abs_lt.1 hdy).2
    rcases hy with hy | ⟨k, hk1, hk2, hk, hyk⟩
    · have : δ ≤ τ / 2 - edgeVal N (specOf Sig) l := min_le_right _ _
      linarith [Set.mem_Ici.1 hy]
    · have hδ16 : δ ≤ τ / 16 := min_le_left _ _
      obtain ⟨h3, h4⟩ := abs_le.1 hyk
      by_cases hlk : l = k
      · rw [hlk] at hlt; linarith
      · have h5 := (hedge k hk1 hk2 hk).2.2.2.1 l hl1 hl2 hlk
        have h6 : |edgeVal N (specOf Sig) k - edgeVal N (specOf Sig) l| ≤ 7 * τ / 16 :=
          abs_le.2 ⟨by linarith, by linarith⟩
        linarith

/-- Lemma 10.1 away from the spectrum, with no regularity: every eigenvalue `≥ τ_W` lies within
`w` of `supp ϱ`. -/
theorem gap_outside (τ : ℝ) (C : ℕ → ℝ) (w τW D : ℝ) (hτ : 0 < τ) (hw : 0 < w) (hτW : 0 < τW) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      HighProbAt N D {ω | ∀ j, τW ≤ specOf (QN Sig (X ω)) j →
        Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support < w} := by
  obtain ⟨N₀, h⟩ := gap_core τ C (1 / 3) D τW w hτ (by norm_num) (by norm_num) hτW hw
  refine ⟨max (max N₀ 1) ⌈(w⁻¹) ^ 3⌉₊, fun N hN Ω _ _ M Sig X hm => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN₀, hN1⟩, hNw⟩ := hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : (N : ℝ) ^ (-2 / 3 + 1 / 3 : ℝ) ≤ w := by
    have h1 : (w⁻¹) ^ 3 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNw)
    have h2 : w⁻¹ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
      calc w⁻¹ = ((w⁻¹) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
              Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
        _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [show (-2 / 3 + 1 / 3 : ℝ) = -(1 / 3) by norm_num, Real.rpow_neg hn0.le]
    rw [inv_le_comm₀ (by positivity) hw]
    exact h2
  have hc := h N hN₀ M Sig X (Set.Ici τW) hm le_rfl
  unfold HighProbAt at hc ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 fun ω hω j hj => ?_)) hc
  by_contra hge
  exact hge (hω j hj (hpow.trans (not_lt.1 hge))).1

/-! ### Instances

Marchenko–Pastur: Gaussian `X` (`M = n`, `N = 2n`, `φ = 1/2`), `Σ = I_n`, `τ = 1/5`; the model
hypothesis is discharged for every `n ≥ 1`. -/

end Anisotropic
