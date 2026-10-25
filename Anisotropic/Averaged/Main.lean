import Anisotropic.Averaged.Chain
import Anisotropic.Averaged.ClaimFour
import Anisotropic.Averaged.Defs
import Anisotropic.Averaged.HatAvg
import Anisotropic.Comparison.Ensemble
import Anisotropic.Comparison.Gronwall
import Anisotropic.Comparison.Interpolation
import Anisotropic.Comparison.Ladder
import Anisotropic.Comparison.MainII
import Anisotropic.Comparison.PrelimBounds
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.Domains
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.Gaussian.Lemma62
import Anisotropic.Gaussian.Main
import Anisotropic.Probability.NormBound.GaussianLower

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Proposition 9.1 and Theorem 3.21 -/

/-! ## Auxiliary facts on `F̃` and on the interpolating laws -/

private theorem avgMain_continuous_ofCoord :
    Continuous (ofCoord : (Fin M × Fin N → ℝ) → Matrix (Fin M) (Fin N) ℝ) :=
  continuous_pi fun i => continuous_pi fun μ => continuous_apply (i, μ)

/-- `X^{θ, t}_{(α)}`: the coordinate `α` of `x` replaced by `t`. -/
private theorem avgMain_ofCoord_update (x : Fin M × Fin N → ℝ) (α : Fin M × Fin N) (t : ℝ) :
    ofCoord (Function.update x α t) = Xupd (ofCoord x) α.1 α.2 t := by
  funext j ν
  simp only [ofCoord, Xupd, Function.update_apply, Prod.ext_iff]

private theorem avgMain_measurable_Ft_pow (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (p : ℕ) :
    Measurable fun x : Fin M × Fin N → ℝ => Ft Sig (ofCoord x) z ^ p :=
  ((((measurable_mN Sig z).sub_const _).norm).comp
    avgMain_continuous_ofCoord.measurable).pow_const p

/-- `|m_N(z)| ≤ η⁻¹`. -/
private theorem avgMain_norm_mN_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (hN : 1 ≤ N) :
    ‖mN Sig A z‖ ≤ z.im⁻¹ := by
  have := isProbabilityMeasure_empMeasure (specOf (Aᵀ * Sig * A)) (by omega : 0 < N)
  rw [mN_eq_resolventTransform hSig A hz, resolventTransform_apply]
  have hb : ∀ x : ℝ, ‖resolvent z x‖ ≤ z.im⁻¹ := by
    intro x
    rw [show resolvent z x = ((x : ℂ) - z)⁻¹ by simp [resolvent, Ring.inverse_eq_inv'],
      norm_inv]
    refine inv_anti₀ hz ?_
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact le_trans (le_abs_self _) h
  have h := norm_integral_le_of_norm_le_const
    (μ := empMeasure (specOf (Aᵀ * Sig * A))) (ae_of_all _ hb)
  simpa using h

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ`. -/
private theorem avgMain_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

/-- The deterministic bound `F̃ ≤ η⁻¹ + C_m ≤ N + C_m` on `S`. -/
private theorem avgMain_Ft_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) : Ft Sig A z ≤ N + mBoundConst τ := by
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : z.im⁻¹ ≤ N := by
    have hlow : (N : ℝ)⁻¹ ≤ z.im := by
      have h2 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith [hset.pos])
      rw [Real.rpow_neg_one] at h2
      exact h2.trans hzD.2.2.2.1
    calc z.im⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = N := inv_inv _
  have hm := (gen_prop_m_specDomain (avgMain_density hset hN) hzD).2.1
  unfold Ft
  calc ‖mN Sig A z - mFun N (specOf Sig) z‖
      ≤ ‖mN Sig A z‖ + ‖mFun N (specOf Sig) z‖ := norm_sub_le _ _
    _ ≤ N + mBoundConst τ :=
        add_le_add ((avgMain_norm_mN_le hset.sigma.posDef A hη hN).trans h1) hm

private theorem avgMain_Ft_nonneg (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) : 0 ≤ Ft Sig A z :=
  norm_nonneg _

/-- `F̃^p ∘ ofCoord` is integrable under every product of probability laws, for `z ∈ S`. -/
private theorem avgMain_integrable_Ft_pi {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) (p : ℕ)
    (ν : Fin M × Fin N → Measure ℝ) [∀ β, IsProbabilityMeasure (ν β)] :
    Integrable (fun x => Ft Sig (ofCoord x) z ^ p) (Measure.pi ν) := by
  refine Integrable.of_bound (avgMain_measurable_Ft_pow Sig z p).aestronglyMeasurable
    (((N : ℝ) + mBoundConst τ) ^ p) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (avgMain_Ft_nonneg _ _ _) _)]
  exact pow_le_pow_left₀ (avgMain_Ft_nonneg _ _ _) (avgMain_Ft_le hset hN hz _) p

/-- `F̃(X)^p` is integrable for a matrix with measurable entries, for `z ∈ S`. -/
private theorem avgMain_integrable_Ft {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) (p : ℕ)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : ∀ i μ, Measurable fun ω => X ω i μ) :
    Integrable fun ω => Ft Sig (X ω) z ^ p := by
  have hg : Measurable fun ω (β : Fin M × Fin N) => X ω β.1 β.2 :=
    measurable_pi_iff.2 fun β => hX β.1 β.2
  refine Integrable.of_bound ((avgMain_measurable_Ft_pow Sig z p).comp hg).aestronglyMeasurable
    (((N : ℝ) + mBoundConst τ) ^ p) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (avgMain_Ft_nonneg _ _ _) _)]
  exact pow_le_pow_left₀ (avgMain_Ft_nonneg _ _ _) (avgMain_Ft_le hset hN hz _) p

/-- `N⁻¹ ≤ C_m Ψ²` on `S` (Lemma 4.10). -/
private theorem avgMain_Psi_sq_ge {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (mBoundConst τ * N)⁻¹ ≤ Psi N (specOf Sig) z ^ 2 := by
  have hzD := hset.domain.1 hz
  obtain ⟨-, -, hm3⟩ := gen_prop_m_specDomain (avgMain_density hset hN) hzD
  have hC := mBoundConst_pos hset.pos
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  set x := Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hsq : x ^ 2 = (mFun N (specOf Sig) z).im / (N * z.im) := Real.sq_sqrt (by positivity)
  have hle : x ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  have h1 : (mBoundConst τ * N)⁻¹ ≤ (mFun N (specOf Sig) z).im / (N * z.im) := by
    rw [le_div_iff₀ hpos]
    calc (mBoundConst τ * N)⁻¹ * (N * z.im) = (mBoundConst τ)⁻¹ * z.im := by
          field_simp
      _ ≤ (mFun N (specOf Sig) z).im := hm3
  calc (mBoundConst τ * N)⁻¹ ≤ x ^ 2 := by rw [hsq]; exact h1
    _ ≤ Psi N (specOf Sig) z ^ 2 := pow_le_pow_left₀ hx0 hle 2

/-- `Ψ > 0` for `N ≥ 1`, `η > 0`. -/
private theorem avgMain_Psi_pos {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hη : 0 < z.im) :
    0 < Psi N σ z := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Psi
  have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

private theorem avgMain_gaussLaw_prob (N : ℕ) : IsProbabilityMeasure (gaussLaw N) := by
  unfold gaussLaw
  infer_instance

private theorem avgMain_entryLaw_prob {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {K : ℕ} {Y : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hY : EntryAssumption C Y) (β : Fin K × Fin N) : IsProbabilityMeasure (entryLaw Y β) :=
  ⟨by simp [entryLaw, Measure.map_apply (hY.measurable β.1 β.2) MeasurableSet.univ]⟩

/-- The Gaussian law `N(0, 1/N)` is the entry law of `X^Gauss`. -/
private theorem avgMain_gaussLaw_eq (hN : 1 ≤ N) :
    gaussLaw N = entryLaw (gaussX 1 N) ((0 : Fin 1), (⟨0, hN⟩ : Fin N)) :=
  ((gaussX_isGaussianEnsemble 1 N).law 0 ⟨0, hN⟩).symm

private theorem avgMain_rpow_neg_half (hN : 1 ≤ N) (n : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) = ((Real.sqrt N)⁻¹) ^ n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNp.le, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  congr 1
  ring

private theorem avgMain_integral_pullback {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    {f : Ω' → Ω} (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {h : Ω → ℝ}
    (hh : Measurable h) : ∫ ω', h (f ω') = ∫ ω, h ω := by
  rw [← integral_map hf.aemeasurable (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

private theorem avgMain_integrable_pullback {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    {f : Ω' → Ω} (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {h : Ω → ℝ}
    (hh : Measurable h) (hi : Integrable h) : Integrable fun ω' => h (f ω') := by
  rw [← hmap] at hi
  exact (integrable_map_measure hh.aestronglyMeasurable hf.aemeasurable).1 hi

/-- The entry assumptions pass to `X ∘ f` for a measure-preserving `f`. -/
private theorem avgMain_entry_transfer {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {f : Ω' → Ω}
    (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {C : ℕ → ℝ} {K : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) :
    EntryAssumption C fun ω' => X (f ω') := by
  have key : ∀ g : ℝ → ℝ, Continuous g → ∀ i μ,
      ∫ ω', g (X (f ω') i μ) = ∫ ω, g (X ω i μ) := fun g hg i μ =>
    avgMain_integral_pullback hf hmap (hg.measurable.comp (hX.measurable i μ))
  have hmeasX : ∀ β : Fin K × Fin N, Measurable fun ω => X ω β.1 β.2 :=
    fun β => hX.measurable β.1 β.2
  refine ⟨fun i μ => (hX.measurable i μ).comp hf, ?_, fun i μ => ?_, fun i μ => ?_,
    fun q i μ => ?_, fun q i μ => ?_⟩
  · have hm' : ∀ β : Fin K × Fin N, AEMeasurable (fun ω' => X (f ω') β.1 β.2) ℙ :=
      fun β => ((hmeasX β).comp hf).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map hm']
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasX β).aemeasurable)).1 hX.indep
    have hg : Measurable fun ω (β : Fin K × Fin N) => X ω β.1 β.2 := measurable_pi_iff.2 hmeasX
    have e1 : (ℙ : Measure Ω').map (fun ω' (β : Fin K × Fin N) => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω (β : Fin K × Fin N) => X ω β.1 β.2) := by
      rw [← hmap, Measure.map_map hg hf]; rfl
    have e2 : ∀ β : Fin K × Fin N, (ℙ : Measure Ω').map (fun ω' => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω => X ω β.1 β.2) := fun β => by
      rw [← hmap, Measure.map_map (hmeasX β) hf]; rfl
    rw [e1, h]
    simp_rw [e2]
  · exact (key (fun t => t) continuous_id i μ).trans (hX.mean i μ)
  · exact (key (fun t => t ^ 2) (by fun_prop) i μ).trans (hX.var i μ)
  · exact avgMain_integrable_pullback hf hmap
      ((by fun_prop : Continuous fun t : ℝ => |Real.sqrt N * t| ^ q).measurable.comp
        (hX.measurable i μ)) (hX.integrable_moment q i μ)
  · exact (key (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) i μ).trans_le (hX.moment q i μ)

/-- (moment_matching) for `F̃^p` along the entry `α` of `X^θ`, with `X^θ_α` replaced by
`y ∼ law(Y_β)` independent of `X^θ`, and `|E y^n| ≤ N^{−n/2} C'_n`. -/
private theorem avgMain_key (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεap : 100 * p * εa ≤ 1) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting τ c M N Sig S → AnisoAllAt N (momMax C) Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ S, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (K : ℕ) (ΩY : Type) [MeasureSpace ΩY]
          [IsProbabilityMeasure (ℙ : Measure ΩY)] (Y : ΩY → Matrix (Fin K) (Fin N) ℝ)
          (β : Fin K × Fin N), EntryAssumption (momMax C) Y → ∀ α : Fin M × Fin N,
          ‖((∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                (entryLaw X) α (entryLaw Y β)) : ℝ) : ℂ)
              - ∫ x, (fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 0
                  + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 2)
                  ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ ≤
            2 * (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ (2 * p) +
              ∑ n ∈ Finset.Icc 3 (4 * p),
                ‖∫ x, fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) n
                    ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
                  ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) := by
  obtain ⟨N₁, h₁⟩ := avg_moment_matching τ c (momMax C) p εa Da hτ hτ1 hc hp hp2 hεa hεaτ
    hεap hDa
  refine ⟨max N₁ 1, ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X hX z hz θ hθ K ΩY _ _ Y β hY α
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have : IsProbabilityMeasure (gaussLaw N) := avgMain_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) β) :=
    fun _ => avgMain_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (entryLaw X β) := avgMain_entryLaw_prob hX
  have : IsProbabilityMeasure (entryLaw Y β) := avgMain_entryLaw_prob hY β
  have hmixP : ∀ β : Fin M × Fin N,
      IsProbabilityMeasure (mixMeasure θ (gaussLaw N) (entryLaw X β)) :=
    fun β => isProbabilityMeasure_mixMeasure _ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X))) := hIP
  have : IsProbabilityMeasure (ℙ : Measure (PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X) (entryLaw Y β))) := by
    change IsProbabilityMeasure ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod
      (entryLaw Y β))
    infer_instance
  -- the interpolated ensemble and the pair `(X^θ, y)`
  have hX₀ : EntryAssumption (momMax C)
      (Ω := InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord :=
    (entryAssumption_interp hX hN1 hθ.1 hθ.2).mono fun q => by
      unfold momMax; exact max_le le_rfl (le_max_right _ _)
  have hfst : Measurable fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β) => (Prod.fst ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
        (entryLaw X)) := measurable_fst
  have hmapfst : (ℙ : Measure (PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β))).map (fun ω => (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
        (fun _ => gaussLaw N) (entryLaw X))) =
      (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X))) := by
    change ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)).map Prod.fst =
      interpLaw θ (fun _ => gaussLaw N) (entryLaw X)
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hX' := avgMain_entry_transfer hfst hmapfst hX₀
  have hind : IndepFun (fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
      (entryLaw Y β) => ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
        (fun _ => gaussLaw N) (entryLaw X))) (fun ω => Prod.snd ω) := by
    have h : IndepFun (Prod.fst : (Fin M × Fin N → ℝ) × ℝ → _) Prod.snd
        ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
        measurable_snd.aemeasurable]
      simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
        measure_univ, one_smul]
    exact h.comp avgMain_continuous_ofCoord.measurable measurable_id
  -- integrals of functions of `y`
  have hy : ∀ g : ℝ → ℝ, Continuous g →
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        g (Prod.snd ω) = ∫ ω, g (Y ω β.1 β.2) := by
    intro g hg
    change ∫ q, g q.2 ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) = _
    rw [integral_fun_snd, probReal_univ, one_smul]
    exact integral_map (hY.measurable β.1 β.2).aemeasurable hg.aestronglyMeasurable
  have hyi : ∀ g : ℝ → ℝ, Continuous g → Integrable (fun ω => g (Y ω β.1 β.2)) →
      Integrable fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
        (entryLaw Y β) => g (Prod.snd ω) := by
    intro g hg hi
    change Integrable (fun q => g q.2)
      ((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β))
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (hY.measurable β.1 β.2).aemeasurable).2 hi).comp_snd _
  have hy1 := (hy (fun t => t) continuous_id).trans (hY.mean β.1 β.2)
  have hy2 := (hy (fun t => t ^ 2) (by fun_prop)).trans (hY.var β.1 β.2)
  have hym : ∀ q : ℕ, Integrable (fun ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X) (entryLaw Y β) => |Real.sqrt N * Prod.snd ω| ^ q) ∧
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        |Real.sqrt N * Prod.snd ω| ^ q ≤ momMax C q := fun q =>
    ⟨hyi (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) (hY.integrable_moment q β.1 β.2),
      (hy (fun t => |Real.sqrt N * t| ^ q) (by fun_prop)).trans_le (hY.moment q β.1 β.2)⟩
  have hmm := h₁ N hNN₁ M Sig S hset hA _ _ _ hX' hind measurable_snd hy1 hy2 hym z hz α.1 α.2
  -- the three identifications
  have hFm : Measurable fun x : Fin M × Fin N → ℝ => Ft Sig (ofCoord x) z ^ p :=
    avgMain_measurable_Ft_pow Sig z p
  have : ∀ β' : Fin M × Fin N, IsProbabilityMeasure (Function.update
      (fun β => mixMeasure θ (gaussLaw N) (entryLaw X β)) α (entryLaw Y β) β') := fun β' => by
    by_cases h : β' = α
    · subst h; simpa using avgMain_entryLaw_prob hY β
    · simpa [Function.update_of_ne h] using hmixP β'
  have hFi : Integrable (fun x : Fin M × Fin N → ℝ => Ft Sig (ofCoord x) z ^ p)
      (interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (entryLaw Y β)) :=
    avgMain_integrable_Ft_pi hset hN1 hz p _
  have hE : (((∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
        (entryLaw X) α (entryLaw Y β)) : ℝ) : ℂ)) =
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        (Ft Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
          (entryLaw X))) α.1 α.2 (Prod.snd ω)) z : ℂ) ^ p := by
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_interpLawAt_eq α (entryLaw Y β) hFm hFi]
    change _ = ∫ q, _ ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β))
    simp only [avgMain_ofCoord_update]
  have hfst_int : ∀ g : (Fin M × Fin N → ℝ) → ℂ,
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        g (Prod.fst ω) = ∫ x, g x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    intro g
    change ∫ q, g q.1 ∂((interpLaw θ (fun _ => gaussLaw N) (entryLaw X)).prod (entryLaw Y β)) = _
    rw [integral_fun_fst, probReal_univ, one_smul]
  have hA' : ∫ x, (fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 0
        + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 2)
        ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) =
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        (fCoeff p (avgCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z α.1 α.2) 0
        + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace
          (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z α.1 α.2) 2) :=
    (hfst_int (fun x => fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 0
      + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 2)).symm
  have hIn : ∀ n : ℕ,
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        fCoeff p (avgCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z α.1 α.2) n =
      ∫ x, fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) n
        ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := fun n =>
    hfst_int (fun x => fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) n)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hYn : ∀ n : ℕ,
      ‖∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        ((Prod.snd ω : ℝ) : ℂ) ^ n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n := by
    intro n
    have e : ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
        (entryLaw Y β), ((Prod.snd ω : ℝ) : ℂ) ^ n =
        ((∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Prod.snd ω : ℝ) ^ n : ℝ) : ℂ) := by
      simp_rw [← Complex.ofReal_pow]
      exact integral_complex_ofReal
    rw [e, Complex.norm_real, Real.norm_eq_abs, avgMain_rpow_neg_half hN1]
    calc |∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Prod.snd ω : ℝ) ^ n|
        ≤ ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), |(Prod.snd ω : ℝ) ^ n| := abs_integral_le_integral_abs
      _ = ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)
          (entryLaw Y β), (Real.sqrt N)⁻¹ ^ n * |Real.sqrt N * Prod.snd ω| ^ n := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only
          rw [abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne',
            one_pow, one_mul, abs_pow]
      _ = (Real.sqrt N)⁻¹ ^ n * ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
          (entryLaw X) (entryLaw Y β), |Real.sqrt N * Prod.snd ω| ^ n := integral_const_mul _ _
      _ ≤ (Real.sqrt N)⁻¹ ^ n * momMax C n :=
          mul_le_mul_of_nonneg_left (hym n).2 (by positivity)
  rw [hE, hA']
  set Sn := ∑ n ∈ Finset.Icc 3 (4 * p),
      (∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        fCoeff p (avgCoeff Sig (Xupd (ofCoord (Prod.fst ω : InterpSpace (Fin M × Fin N) θ
          (fun _ => gaussLaw N) (entryLaw X))) α.1 α.2 0) z α.1 α.2) n) *
      ∫ ω : PairSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X) (entryLaw Y β),
        ((Prod.snd ω : ℝ) : ℂ) ^ n with hSn
  calc _ = ‖(_ - _ - Sn) + Sn‖ := by rw [sub_add_cancel]
    _ ≤ ‖_ - _ - Sn‖ + ‖Sn‖ := norm_add_le _ _
    _ ≤ _ := by
        refine add_le_add hmm ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, hIn n]
        exact mul_le_mul_of_nonneg_left (hYn n) (norm_nonneg _)

/-! ## Lemmas 7.10–7.11, Lemma 7.5 and Proposition 9.1 for `F̃` -/


/-- Theorem 3.21 (i) for every model at once: the entrywise law for `(X^Gauss, D(Σ))` at
`(ε₁, D₁)` gives the anisotropic law at `(ε, D)` for every `X` with moment function `C`. -/
theorem anisoAll_of_gauss (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), τ ≤ (M : ℝ) / N → (M : ℝ) / N ≤ τ⁻¹ → SigmaAssumption τ Sig →
      SpectralDomain τ N S → OneXmOn c N (specOf Sig) S →
      EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
      AnisoAllAt N C Sig S ε D := by
  obtain ⟨ε₂, D₂, hε₂, N₁, h₁⟩ := prop_comparison_two τ c C ε D hτ hτ1 hc hε
  obtain ⟨N₂, h₂⟩ := gauss_aniso τ c ε₂ D₂ gaussMoment hτ hc hε₂
  refine ⟨ε₂ / 4, lawD1 ε₂ D₂, by positivity, max (max N₁ N₂) 1,
    fun N hN M Sig S hr1 hr2 hsig hS hx hg => ?_⟩
  intro Ω _ _ X hX
  have hN₁ : N ≥ N₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N ≥ N₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) := isModel_gaussX hN1 hr1 hr2 hsig
  exact h₁ N hN₁ M Sig X S ⟨hr1, hr2, hX, hsig⟩ hS hx
    (h₂ N hN₂ M Sig (gaussX M N) S (gaussX_isGaussianEnsemble M N) hgm hS hx hg)

/-- Lemmas 7.10–7.11 for `F̃^p` (the `n = 3` term included). -/
theorem avg_comparison (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεap : 100 * p * εa ≤ 1) (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N (momMax C) Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax C) X →
        ∀ z ∈ S, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          |∑ α : Fin M × Fin N,
              ((∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (entryLaw X α)))
                - ∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLawAt θ (fun _ => gaussLaw N)
                  (entryLaw X) α (gaussLaw N)))| ≤
            Cstar * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p +
              ∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) := by
  obtain ⟨N₁, h₁⟩ := avgMain_key τ c C p εa Da hτ hτ1 hc hp hp2 hεa hεaτ hεap hDa
  obtain ⟨K₂, hK₂, N₂, h₂⟩ := avg_zero_to_theta τ c (momMax C) p εa Da hτ hτ1 hc hp hp2 hεa
    hεaτ hεap hDa
  obtain ⟨K₃, hK₃, N₃, h₃⟩ := avg_claim3 τ c (momMax C) p δ εa Da hτ hτ1 hc hp hp2 hδ hεa
    hεaτ hεaδ hDa
  obtain ⟨K₄, hK₄, N₄, h₄⟩ := avg_claim_ge4 τ c (momMax C) p δ εa Da hτ hτ1 hc hp hp2 hδ hεa
    hεaτ hεaδ hDa
  have hmom0 : ∀ n, 0 ≤ momMax C n := fun n =>
    le_trans (by unfold gaussMoment; exact integral_nonneg fun x => by positivity)
      (le_max_right _ _)
  set SC : ℝ := ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n with hSC
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg fun n _ => hmom0 n
  set C1 : ℝ := 2 * τ⁻¹ + SC * K₂ * (K₃ + K₄ + 1) with hC1
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨2 * C1, by positivity, max (max (max N₁ N₂) (max N₃ N₄)) 1, ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X hX z hz θ hθ
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNN₃ : N₃ ≤ N := by omega
  have hNN₄ : N₄ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) β) :=
    fun _ => avgMain_gaussLaw_prob N
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (entryLaw X β) := avgMain_entryLaw_prob hX
  have : ∀ β : Fin M × Fin N, IsProbabilityMeasure (mixMeasure θ (gaussLaw N) (entryLaw X β)) :=
    fun β => isProbabilityMeasure_mixMeasure _ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N)
      (entryLaw X))) := hIP
  have hX₀ : EntryAssumption (momMax C)
      (Ω := InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord :=
    (entryAssumption_interp hX hN1 hθ.1 hθ.2).mono fun q => by
      unfold momMax; exact max_le le_rfl (le_max_right _ _)
  have hΨ0 : 0 ≤ Psi N (specOf Sig) z := (avgMain_Psi_pos hN1 (hset.domain.1 hz).1).le
  set a : ℝ := ((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p with ha
  set E : ℝ := ∫ x, Ft Sig (ofCoord x) z ^ p ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))
    with hE
  have ha0 : 0 ≤ a := by positivity
  have hE0 : 0 ≤ E := integral_nonneg fun x => pow_nonneg (avgMain_Ft_nonneg _ _ _) p
  have hΨa : Psi N (specOf Sig) z ^ (2 * p) ≤ a := by
    rw [ha, mul_pow, pow_mul]
    have h1 : (1 : ℝ) ≤ ((N : ℝ) ^ δ) ^ p := one_le_pow₀ (Real.one_le_rpow hN1r hδ.le)
    have h2 : 0 ≤ (Psi N (specOf Sig) z ^ 2) ^ p := by positivity
    nlinarith
  -- (avg_pf_claim) at `X^θ`, `n ∈ [3, 4p]`
  have hB : ∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
      ∑ i, ∑ μ, ‖∫ ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X),
        fCoeff p (avgCoeff Sig (ofCoord ω) z i μ) n‖ ≤ (K₃ + K₄) * (a + E) := by
    intro n hn
    have hmono : ∀ K : ℝ, 0 ≤ K → K ≤ K₃ + K₄ → K * (a + E) ≤ (K₃ + K₄) * (a + E) :=
      fun K _ hK => mul_le_mul_of_nonneg_right hK (by positivity)
    rcases (show n = 3 ∨ n ∈ Finset.Icc 4 (4 * p) by
      simp only [Finset.mem_Icc] at hn ⊢; omega) with rfl | hn4
    · have h := h₃ N hNN₃ M Sig S hset hA
        (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord hX₀ z hz
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
      exact h.trans (hmono K₃ hK₃ (by linarith))
    · exact (h₄ N hNN₄ M Sig S hset hA
        (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord hX₀ z hz n
        hn4).trans
        (hmono K₄ hK₄ (by linarith))
  have hZ := h₂ N hNN₂ M Sig S hset hA
    (InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord hX₀ z hz
    ((K₃ + K₄) * (a + E)) (by positivity) hB
  -- (moment_matching) along every entry, for `u = 1` and `u = 0`
  have hG : EntryAssumption (momMax C) (gaussX 1 N) :=
    ((gaussX_isGaussianEnsemble 1 N).entryAssumption hN1).mono fun q => le_max_right _ _
  set A : Fin M × Fin N → ℂ := fun α =>
    ∫ x, (fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 0
      + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) 2)
      ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) with hAdef
  set R : Fin M × Fin N → ℝ := fun α =>
    2 * (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ (2 * p) +
      ∑ n ∈ Finset.Icc 3 (4 * p),
        ‖∫ x, fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) n
            ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
          ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) with hRdef
  set I1 : Fin M × Fin N → ℝ := fun α => ∫ x, Ft Sig (ofCoord x) z ^ p
    ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (entryLaw X α)) with hI1
  set I0 : Fin M × Fin N → ℝ := fun α => ∫ x, Ft Sig (ofCoord x) z ^ p
    ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (gaussLaw N)) with hI0
  have hk1 : ∀ α, ‖((I1 α : ℝ) : ℂ) - A α‖ ≤ R α := fun α =>
    h₁ N hNN₁ M Sig S hset hA Ω X hX z hz θ hθ M Ω X α hX α
  have hk0 : ∀ α, ‖((I0 α : ℝ) : ℂ) - A α‖ ≤ R α := by
    intro α
    have h := h₁ N hNN₁ M Sig S hset hA Ω X hX z hz θ hθ 1 (GaussSpace 1 N) (gaussX 1 N)
      ((0 : Fin 1), (⟨0, hN1⟩ : Fin N)) hG α
    rw [← avgMain_gaussLaw_eq hN1] at h
    exact h
  -- the sum over `α`
  have hsplit : ∑ α : Fin M × Fin N, ∑ n ∈ Finset.Icc 3 (4 * p),
      ‖∫ x, fCoeff p (avgCoeff Sig (Xupd (ofCoord x) α.1 α.2 0) z α.1 α.2) n
          ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖ *
        ((N : ℝ) ^ (-(n : ℝ) / 2) * momMax C n) =
      ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
        ∑ i, ∑ μ, ‖∫ ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X),
          fCoeff p (avgCoeff Sig (Xupd (ofCoord ω) i μ 0) z i μ) n‖) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    change _ = momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∫ x, fCoeff p (avgCoeff Sig (Xupd (ofCoord x) i μ 0) z i μ) n
        ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))‖)
    ring
  have hMN : (M : ℝ) * N * (N : ℝ) ^ (-2 : ℝ) ≤ τ⁻¹ := by
    have e : (M : ℝ) * N * (N : ℝ) ^ (-2 : ℝ) = (M : ℝ) / N := by
      rw [Real.rpow_neg hNp.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [e]
    exact hset.ratio_le
  have hR : ∑ α, R α ≤ C1 * (a + E) := by
    calc ∑ α, R α = (M : ℝ) * N * (2 * (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ (2 * p)) +
          ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n * ((N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω : InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X),
              fCoeff p (avgCoeff Sig (Xupd (ofCoord ω) i μ 0) z i μ) n‖) := by
          simp only [hRdef]
          rw [Finset.sum_add_distrib, hsplit, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 2 * τ⁻¹ * a + ∑ n ∈ Finset.Icc 3 (4 * p), momMax C n *
            (K₂ * ((K₃ + K₄) * (a + E) + a)) := by
          refine add_le_add ?_ (Finset.sum_le_sum fun n hn =>
            mul_le_mul_of_nonneg_left ((hZ n hn).trans ?_) (hmom0 n))
          · have h1 := mul_le_mul_of_nonneg_right hMN
              (by positivity : (0 : ℝ) ≤ 2 * Psi N (specOf Sig) z ^ (2 * p))
            have h2 := mul_le_mul_of_nonneg_left hΨa (by positivity : (0 : ℝ) ≤ 2 * τ⁻¹)
            nlinarith
          · exact mul_le_mul_of_nonneg_left (by linarith) hK₂
      _ = 2 * τ⁻¹ * a + SC * K₂ * ((K₃ + K₄) * (a + E) + a) := by
          rw [hSC, Finset.sum_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ C1 * (a + E) := by
          rw [hC1]
          have h1 : 0 ≤ SC * K₂ := by positivity
          have h2 : 0 ≤ 2 * τ⁻¹ * E := by positivity
          have h3 : 0 ≤ SC * K₂ * E := by positivity
          nlinarith
  -- `u = 1` minus `u = 0`
  have hdiff : |∑ α, (I1 α - I0 α)| ≤ ∑ α, R α + ∑ α, R α := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sum]
    simp only [Complex.ofReal_sub]
    calc ‖∑ α, ((I1 α : ℂ) - (I0 α : ℂ))‖
        = ‖∑ α, ((((I1 α : ℝ) : ℂ) - A α) - (((I0 α : ℝ) : ℂ) - A α))‖ := by
          congr 1
          exact Finset.sum_congr rfl fun α _ => by ring
      _ ≤ ∑ α, ‖(((I1 α : ℝ) : ℂ) - A α) - (((I0 α : ℝ) : ℂ) - A α)‖ := norm_sum_le _ _
      _ ≤ ∑ α, (R α + R α) :=
          Finset.sum_le_sum fun α _ => (norm_sub_le _ _).trans (add_le_add (hk1 α) (hk0 α))
      _ = ∑ α, R α + ∑ α, R α := Finset.sum_add_distrib
  calc |∑ α, (I1 α - I0 α)| ≤ ∑ α, R α + ∑ α, R α := hdiff
    _ ≤ 2 * C1 * (a + E) := by linarith

/-- Lemma 7.5 for `F̃^p`: Grönwall from the Gaussian start `E F̃^p(X^Gauss) ≤ 2(N^{ε₁} Φ)^p`. -/
theorem avg_moment_bound (τ c cΦ : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hcΦ : 0 < cΦ) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ)
    (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ) (hεap : 100 * p * εa ≤ 1) (hεaδ : 20 * p * εa ≤ δ)
    (hDa : dPrevTwo τ p ≤ Da) :
    ∃ Kp : ℝ, 0 < Kp ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (Φ : ℂ → ℝ) (ε₁ D₁ : ℝ), CompSetting τ c M N Sig S →
      AnisoAllAt N (momMax C) Sig S εa Da → 0 ≤ ε₁ → 2 * (p : ℝ) + 1 ≤ D₁ →
      AveragedPhiLawAt N ε₁ D₁ Sig (gaussX M N) S Φ →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, cΦ * Psi N (specOf Sig) z ^ 2 ≤ Φ z →
          Integrable (fun ω => Ft Sig (X ω) z ^ p) ∧
            ∫ ω, Ft Sig (X ω) z ^ p ≤ Kp * ((N : ℝ) ^ (δ + ε₁) * Φ z) ^ p := by
  obtain ⟨Cs, hCs, N₁, h₁⟩ := avg_comparison τ c C p δ εa Da hτ hτ1 hc hp hp2 hδ hεa hεaτ
    hεap hεaδ hDa
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := mBoundConst_pos hτ
  have hexp : 1 ≤ Real.exp Cs := Real.one_le_exp hCs
  refine ⟨(2 * Real.exp Cs - 1) * (cΦ⁻¹ ^ p + 2), ?_,
    max (max N₁ ⌈(2 * Km / cΦ) ^ p⌉₊) (max ⌈Km⌉₊ 1), ?_⟩
  · have : 0 < cΦ⁻¹ ^ p + 2 := by positivity
    have : 0 < 2 * Real.exp Cs - 1 := by linarith
    positivity
  intro N hN M Sig S Φ ε₁ D₁ hset hA hε₁ hD₁ hgauss Ω _ _ X hX z hz hΦz
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNN₁ : N₁ ≤ N := by omega
  have hNr : ⌈(2 * Km / cΦ) ^ p⌉₊ ≤ N := by omega
  have hNK : ⌈Km⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hKmN : Km ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hrN : (2 * Km / cΦ) ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNr)
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hΨ : 0 < Psi N (specOf Sig) z := avgMain_Psi_pos hN1 hη
  have hΦ0 : 0 < Φ z := lt_of_lt_of_le (by positivity) hΦz
  refine ⟨avgMain_integrable_Ft hset hN1 hz p hX.measurable, ?_⟩
  have hXm : EntryAssumption (momMax C) X := hX.mono fun q => le_max_left _ _
  have : ∀ α : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) α) :=
    fun _ => avgMain_gaussLaw_prob N
  have : ∀ α, IsProbabilityMeasure (entryLaw X α) := avgMain_entryLaw_prob hX
  -- `g(θ) = E F̃^p(X^θ)` and its derivative (Remark 7.18)
  set F : (Fin M × Fin N → ℝ) → ℝ := fun x => Ft Sig (ofCoord x) z ^ p with hFdef
  have hFm : Measurable F := avgMain_measurable_Ft_pow Sig z p
  have hint : ∀ u, Integrable F (vertexLaw (fun _ => gaussLaw N) (entryLaw X) u) := by
    intro u
    have : ∀ α, IsProbabilityMeasure
        (if u α then entryLaw X α else (fun _ => gaussLaw N) α) := by
      intro α
      split <;> infer_instance
    exact avgMain_integrable_Ft_pi hset hN1 hz p _
  set g : ℝ → ℝ := interpPoly (fun _ => gaussLaw N) (entryLaw X) F with hg
  set g' : ℝ → ℝ := fun θ => ∑ α : Fin M × Fin N,
      ((∫ x, F x ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (entryLaw X α)))
        - ∫ x, F x ∂(interpLawAt θ (fun _ => gaussLaw N) (entryLaw X) α (gaussLaw N)))
    with hg'
  have hgeq : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      g θ = ∫ x, F x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) := fun θ hθ =>
    (integral_interpLaw_eq_interpPoly hθ.1 hθ.2 hFm hint).symm
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' θ) θ := fun θ hθ =>
    hasDerivAt_interpPoly hθ.1 hθ.2 hFm hint
  have hcont : ContinuousOn g (Set.Icc 0 1) := fun θ hθ =>
    (hderiv θ hθ).continuousAt.continuousWithinAt
  -- the affine bound on `g'` (Lemmas 7.10–7.11)
  set b : ℝ := ((N : ℝ) ^ ε₁ * Φ z) ^ p with hb
  set a₀ : ℝ := ((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p with ha₀
  have hb0 : 0 ≤ b := by positivity
  have ha₀0 : 0 ≤ a₀ := by positivity
  have hbound : ∀ θ ∈ Set.Ico (0 : ℝ) 1, g' θ ≤ Cs * ((a₀ + 2 * b) + g θ) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hθ
    have hc := h₁ N hNN₁ M Sig S hset hA Ω X hXm z hz θ hθ'
    rw [hgeq θ hθ']
    calc g' θ ≤ |g' θ| := le_abs_self _
      _ ≤ Cs * (a₀ + ∫ x, F x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) := hc
      _ ≤ Cs * ((a₀ + 2 * b) + ∫ x, F x ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) := by
          gcongr
          linarith
  -- the Gaussian start `E F̃^p(X^Gauss) ≤ 2 (N^{ε₁} Φ)^p`
  have hlaw0 : interpLaw 0 (fun _ => gaussLaw N) (entryLaw X) =
      Measure.pi fun _ : Fin M × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    unfold interpLaw
    congr 1
    funext α
    simp [mixMeasure, unitClamp, gaussLaw]
  have hg0 : g 0 = ∫ ω, Ft Sig (gaussX M N ω) z ^ p := by
    rw [hgeq 0 ⟨le_rfl, zero_le_one⟩, hlaw0]
    rfl
  set t : ℝ := (N : ℝ) ^ ε₁ * Φ z with ht
  have ht0 : 0 ≤ t := by positivity
  set Bd : ℝ := (N : ℝ) + Km with hBdDef
  set E0 : Set (GaussSpace M N) := {ω | t < Ft Sig (gaussX M N ω) z} with hE0
  have hGm : Measurable fun ω : GaussSpace M N => Ft Sig (gaussX M N ω) z :=
    ((measurable_mN Sig z).sub_const _).norm.comp
      (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ =>
        (gaussX_isGaussianEnsemble M N).measurable i μ)
  have hE0m : MeasurableSet E0 := measurableSet_lt measurable_const hGm
  have hP : (ℙ : Measure (GaussSpace M N)).real E0 ≤ (N : ℝ) ^ (-D₁) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hgauss z hz)
  have hpt : ∀ ω : GaussSpace M N, Ft Sig (gaussX M N ω) z ^ p ≤
      t ^ p + Bd ^ p * E0.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ E0
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have h1 : Ft Sig (gaussX M N ω) z ^ p ≤ Bd ^ p :=
        pow_le_pow_left₀ (avgMain_Ft_nonneg _ _ _) (avgMain_Ft_le hset hN1 hz _) p
      have h2 : 0 ≤ t ^ p := by positivity
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have h1 : Ft Sig (gaussX M N ω) z ≤ t := not_lt.1 hω
      exact pow_le_pow_left₀ (avgMain_Ft_nonneg _ _ _) h1 p
  have hstart1 : ∫ ω, Ft Sig (gaussX M N ω) z ^ p ≤ t ^ p + Bd ^ p * (N : ℝ) ^ (-D₁) := by
    have hi1 : Integrable fun ω : GaussSpace M N => Ft Sig (gaussX M N ω) z ^ p :=
      avgMain_integrable_Ft hset hN1 hz p (gaussX_isGaussianEnsemble M N).measurable
    have hind : Integrable (E0.indicator (1 : GaussSpace M N → ℝ)) :=
      (integrable_const (1 : ℝ)).indicator hE0m
    have hi2 : Integrable fun ω : GaussSpace M N => t ^ p + Bd ^ p * E0.indicator 1 ω :=
      (integrable_const _).add (hind.const_mul _)
    calc ∫ ω, Ft Sig (gaussX M N ω) z ^ p ≤ ∫ ω, (t ^ p + Bd ^ p * E0.indicator 1 ω) :=
          integral_mono hi1 hi2 hpt
      _ = t ^ p + Bd ^ p * (ℙ : Measure (GaussSpace M N)).real E0 := by
          rw [integral_add (integrable_const _) (hind.const_mul _), integral_const,
            integral_const_mul, integral_indicator_one hE0m]
          simp
      _ ≤ t ^ p + Bd ^ p * (N : ℝ) ^ (-D₁) := by gcongr
  have hBd : Bd ≤ 2 * N := by rw [hBdDef]; linarith
  have hD : (N : ℝ) ^ (-D₁) ≤ ((N : ℝ)⁻¹) ^ (2 * p + 1) := by
    have h1 : (N : ℝ) ^ (-D₁) ≤ (N : ℝ) ^ (-(((2 * p + 1 : ℕ) : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
    have e : (N : ℝ) ^ (-(((2 * p + 1 : ℕ) : ℕ) : ℝ)) = ((N : ℝ)⁻¹) ^ (2 * p + 1) := by
      rw [Real.rpow_neg hNp.le, Real.rpow_natCast, inv_pow]
    exact h1.trans e.le
  have htl : cΦ * (Km * N)⁻¹ ≤ t := by
    have h1 : cΦ * (Km * N)⁻¹ ≤ Φ z :=
      le_trans (mul_le_mul_of_nonneg_left (avgMain_Psi_sq_ge hset hN1 hz) hcΦ.le) hΦz
    have h2 : Φ z ≤ t := by
      rw [ht]
      exact le_mul_of_one_le_left hΦ0.le (Real.one_le_rpow hN1r hε₁)
    linarith
  have hNN : (N : ℝ) ^ p * ((N : ℝ)⁻¹) ^ p = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNp.ne', one_pow]
  have hsmall : Bd ^ p * (N : ℝ) ^ (-D₁) ≤ t ^ p := by
    have e1 : (2 * (N : ℝ)) ^ p * ((N : ℝ)⁻¹) ^ (2 * p + 1) =
        2 ^ p * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ p := by
      rw [mul_pow, pow_succ, two_mul, pow_add]
      linear_combination (2 ^ p * ((N : ℝ)⁻¹) ^ p * (N : ℝ)⁻¹) * hNN
    have e2 : (cΦ * (Km * N)⁻¹) ^ p = (cΦ / Km) ^ p * ((N : ℝ)⁻¹) ^ p := by
      rw [← mul_pow]
      congr 1
      field_simp
    have e3 : 2 ^ p * (N : ℝ)⁻¹ ≤ (cΦ / Km) ^ p := by
      rw [mul_inv_le_iff₀ hNp]
      calc (2 : ℝ) ^ p = (cΦ / Km) ^ p * (2 * Km / cΦ) ^ p := by
            rw [← mul_pow]
            congr 1
            field_simp
        _ ≤ (cΦ / Km) ^ p * N := by gcongr
    calc Bd ^ p * (N : ℝ) ^ (-D₁) ≤ (2 * (N : ℝ)) ^ p * ((N : ℝ)⁻¹) ^ (2 * p + 1) := by
          have hBd0 : 0 ≤ Bd := by rw [hBdDef]; positivity
          gcongr
      _ = 2 ^ p * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ p := e1
      _ ≤ (cΦ / Km) ^ p * ((N : ℝ)⁻¹) ^ p := by gcongr
      _ = (cΦ * (Km * N)⁻¹) ^ p := e2.symm
      _ ≤ t ^ p := pow_le_pow_left₀ (by positivity) htl p
  have h0 : g 0 ≤ a₀ + 2 * b := by
    rw [hg0]
    have : t ^ p = b := rfl
    linarith
  -- Grönwall
  have hgr := gronwall_affine (Φ := g) (Φ' := g') hCs (by positivity) hcont
    (fun θ hθ => hderiv θ (Set.Ico_subset_Icc_self hθ)) hbound h0
  -- `g(1) = E F̃^p(X)`: the entries of `X` are independent
  have h1 : ∫ ω, Ft Sig (X ω) z ^ p = g 1 := by
    rw [hgeq 1 ⟨zero_le_one, le_rfl⟩]
    have hg1 : Measurable fun ω (β : Fin M × Fin N) => X ω β.1 β.2 :=
      measurable_pi_iff.2 fun β => hX.measurable β.1 β.2
    have hlaw1 : interpLaw 1 (fun _ => gaussLaw N) (entryLaw X) =
        (ℙ : Measure Ω).map (fun ω (β : Fin M × Fin N) => X ω β.1 β.2) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map
        (fun β : Fin M × Fin N => (hX.measurable β.1 β.2).aemeasurable)).1 hX.indep]
      unfold interpLaw
      congr 1
      funext α
      simp [mixMeasure, unitClamp, entryLaw]
    rw [hlaw1, integral_map hg1.aemeasurable hFm.aestronglyMeasurable]
    rfl
  -- the final constant
  set T : ℝ := ((N : ℝ) ^ (δ + ε₁) * Φ z) ^ p with hT
  have hNδ : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (δ + ε₁) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hNε : (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (δ + ε₁) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have ha₀T : a₀ ≤ cΦ⁻¹ ^ p * T := by
    have hΨΦ : Psi N (specOf Sig) z ^ 2 ≤ cΦ⁻¹ * Φ z := by
      rw [le_inv_mul_iff₀ hcΦ]
      exact hΦz
    have h2 : (N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2 ≤ cΦ⁻¹ * ((N : ℝ) ^ (δ + ε₁) * Φ z) := by
      calc (N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2 ≤ (N : ℝ) ^ (δ + ε₁) * (cΦ⁻¹ * Φ z) :=
            mul_le_mul hNδ hΨΦ (by positivity) (by positivity)
        _ = cΦ⁻¹ * ((N : ℝ) ^ (δ + ε₁) * Φ z) := by ring
    rw [ha₀, hT, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 p
  have hbT : b ≤ T := by
    rw [hb, hT]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hNε hΦ0.le) p
  have hK1 : 0 ≤ 2 * Real.exp Cs - 1 := by linarith
  rw [h1]
  calc g 1 ≤ (2 * Real.exp Cs - 1) * (a₀ + 2 * b) := hgr
    _ ≤ (2 * Real.exp Cs - 1) * ((cΦ⁻¹ ^ p + 2) * T) := by
        gcongr
        nlinarith
    _ = (2 * Real.exp Cs - 1) * (cΦ⁻¹ ^ p + 2) * T := by ring

/-- Proposition 9.1 (`prop:gen_avg`) at fixed `N`: the entrywise law and the averaged law with
`Φ` for `(X^Gauss, D(Σ))` at `(ε₁, D₁)` give the averaged law with `Φ` for `(X, Σ)` at `(ε, D)`. -/
theorem prop_gen_avg (τ c cΦ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hcΦ : 0 < cΦ) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ),
      IsModel τ C M N Sig X → SpectralDomain τ N S → OneXmOn c N (specOf Sig) S →
      PhiCond τ cΦ N (specOf Sig) S Φ →
      EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
      AveragedPhiLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S Φ →
      AveragedPhiLawAt N ε D Sig X S Φ := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨1, 0, one_pos, 0, fun N _ Ω _ _ M Sig X S Φ hm _ _ _ _ _ =>
      absurd hm.tau_le_one hτ1⟩
  -- the moment `p`, the exponents `δ`, `εa` and the level `Da`
  set k : ℕ := max 1 ⌈(D + 1) / ε⌉₊ with hk
  set p : ℕ := 2 * k with hpdef
  have hp : Even p := ⟨k, by rw [hpdef]; ring⟩
  have hk1 : 1 ≤ k := le_max_left _ _
  have hp2 : 2 ≤ p := by omega
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hkD : D + 1 ≤ ε * k := by
    have h1 : (D + 1) / ε ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(D + 1) / ε⌉₊)
    rw [div_le_iff₀ hε] at h1
    linarith
  have hpk : (p : ℝ) = 2 * k := by rw [hpdef]; push_cast; ring
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set εa : ℝ := min (min (τ / 16) (1 / (100 * p))) (ε / (80 * p)) with hεadef
  have hεa : 0 < εa := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hεa1 : εa ≤ τ / 16 := (min_le_left _ _).trans (min_le_left _ _)
  have hεa2 : εa ≤ 1 / (100 * p) := (min_le_left _ _).trans (min_le_right _ _)
  have hεa3 : εa ≤ ε / (80 * p) := min_le_right _ _
  have hεaτ : 16 * εa ≤ τ := by linarith
  have hεap : 100 * p * εa ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hεa2 (by positivity : (0 : ℝ) ≤ 100 * p)
    rwa [mul_one_div_cancel (by positivity)] at this
  have hεaδ : 20 * p * εa ≤ δ := by
    have := mul_le_mul_of_nonneg_left hεa3 (by positivity : (0 : ℝ) ≤ 20 * p)
    calc 20 * p * εa ≤ 20 * p * (ε / (80 * p)) := this
      _ = δ := by rw [hδdef]; field_simp; ring
  -- the a priori input and the moment bound
  obtain ⟨ε₂, D₂, hε₂, N₁, hAll⟩ := anisoAll_of_gauss τ c (momMax C) εa (dPrevTwo τ p) hτ hτ1
    hc hεa
  obtain ⟨Kp, hKp, N₂, hmb⟩ := avg_moment_bound τ c cΦ C p δ εa (dPrevTwo τ p) hτ hτ1 hc hcΦ
    hp hp2 hδ hεa hεaτ hεap hεaδ le_rfl
  refine ⟨min ε₂ (ε / 4), max D₂ (2 * p + 1), lt_min hε₂ (by positivity),
    max (max N₁ N₂) (max ⌈Kp⌉₊ 1), ?_⟩
  intro N hN Ω _ _ M Sig X S Φ hm hS hx hΦ hge hga
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNK : ⌈Kp⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hKpN : Kp ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hset : CompSetting τ c M N Sig S :=
    ⟨hτ, hτ1, hc, hm.ratio_ge, hm.ratio_le, hm.sigma, hS, hx⟩
  have hge₂ : EntrywiseLawAt N ε₂ D₂ (diagonal (specOf Sig)) (gaussX M N) S := fun z hz s t =>
    DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => (avgMain_Psi_pos hN1 (hS.1 hz).1).le) (min_le_left _ _) (le_max_left _ _)
      (hge z hz s t)
  have hA := hAll N hNN₁ M Sig S hm.ratio_ge hm.ratio_le hm.sigma hS hx hge₂
  have hgSig : AveragedPhiLawAt N (min ε₂ (ε / 4)) (max D₂ (2 * p + 1)) Sig (gaussX M N) S Φ :=
    gauss_averaged' hm.sigma.posDef.isHermitian (gaussX_isGaussianEnsemble M N) hga
  intro z hz
  have hΦz := (hΦ z hz).1
  have hΦ0 : 0 < Φ z := lt_of_lt_of_le
    (mul_pos hcΦ (pow_pos (avgMain_Psi_pos hN1 (hS.1 hz).1) 2)) hΦz
  set ε₁ : ℝ := min ε₂ (ε / 4) with hε₁def
  have hε₁0 : 0 ≤ ε₁ := le_min hε₂.le (by positivity)
  have hε₁4 : ε₁ ≤ ε / 4 := min_le_right _ _
  obtain ⟨hint, hmom⟩ := hmb N hNN₂ M Sig S Φ ε₁ (max D₂ (2 * p + 1)) hset hA hε₁0
    (le_max_right _ _) hgSig Ω X hm.entries z hz hΦz
  -- Markov at the power `p`
  change DomAt N ε D (fun ω => Ft Sig (X ω) z) (fun _ => Φ z)
  refine DomAt.of_moment (ε := δ + ε₁ + 1 / p) p hN1 ?_ (fun ω => avgMain_Ft_nonneg _ _ _)
    hΦ0 hint ?_
  · have e : (ε - (δ + ε₁ + 1 / p)) * p = ε * p - δ * p - ε₁ * p - 1 := by
      field_simp
      ring
    have h1 : ε₁ * p ≤ ε / 4 * p := mul_le_mul_of_nonneg_right hε₁4 hp0.le
    rw [e, hδdef]
    rw [hpk] at h1 ⊢
    linarith
  · have hNp1 : ((N : ℝ) ^ (1 / (p : ℝ))) ^ p = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, one_div, inv_mul_cancel₀ hp0.ne',
        Real.rpow_one]
    have e : ((N : ℝ) ^ (δ + ε₁ + 1 / p) * Φ z) ^ p =
        N * ((N : ℝ) ^ (δ + ε₁) * Φ z) ^ p := by
      rw [Real.rpow_add hNp, mul_pow, mul_pow, mul_pow, hNp1]
      ring
    rw [e]
    refine hmom.trans (mul_le_mul_of_nonneg_right hKpN (by positivity))

/-- Theorem 3.21 (i) (`thm:gen_iso`) at fixed `N`: the entrywise law for `(X^Gauss, D(Σ))` at
`(ε₁, D₁)` gives the anisotropic law for `(X, Σ)` at `(ε, D)`. -/
theorem gen_iso_aniso (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S → OneXmOn c N (specOf Sig) S →
      EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
      AnisotropicLawAt N ε D Sig X S := by
  by_cases hτ1 : τ ≤ 1
  · obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := anisoAll_of_gauss τ c C ε D hτ hτ1 hc hε
    exact ⟨ε₁, D₁, hε₁, N₀, fun N hN Ω _ _ M Sig X S hm hS hx hg =>
      h N hN M Sig S hm.ratio_ge hm.ratio_le hm.sigma hS hx hg Ω X hm.entries⟩
  · exact ⟨1, 0, one_pos, 0, fun N _ Ω _ _ M Sig X S hm _ _ _ =>
      absurd hm.tau_le_one hτ1⟩

/-- Theorem 3.21 (ii) (`thm:gen_iso`) at fixed `N`: the entrywise and averaged laws for
`(X^Gauss, D(Σ))` at `(ε₁, D₁)` give the averaged law for `(X, Σ)` at `(ε, D)`. -/
theorem gen_iso_avg (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S → OneXmOn c N (specOf Sig) S →
      EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
      AveragedLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
      AveragedLawAt N ε D Sig X S := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := prop_gen_avg τ c (phiConst τ) C ε D hτ hc (phiConst_pos hτ) hε
  refine ⟨ε₁, D₁, hε₁, max N₀ 1, fun N hN Ω _ _ M Sig X S hm hS hx hge hga => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  exact h N (le_of_max_le_left hN) M Sig X S (fun z => 1 / (N * z.im)) hm hS hx
    (phiCond_inv hda hN1 hS.1) hge hga

/-- Proposition 9.1 instantiated (conditional: the `∃ N₀` threshold exceeds the small
instances, so the model hypotheses stay binders). -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ),
    IsModel (1 / 10) gaussMoment M N Sig (gaussX M N) → SpectralDomain (1 / 10) N S →
    OneXmOn (1 / 2) N (specOf Sig) S → PhiCond (1 / 10) (phiConst (1 / 10)) N (specOf Sig) S Φ →
    EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
    AveragedPhiLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S Φ →
    AveragedPhiLawAt N 1 1 Sig (gaussX M N) S Φ := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := prop_gen_avg (1 / 10) (1 / 2) (phiConst (1 / 10)) gaussMoment 1 1
    (by norm_num) (by norm_num) (phiConst_pos (by norm_num)) (by norm_num)
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN M Sig S Φ hm hS hx hΦ hg ha =>
    h N hN M Sig (gaussX M N) S Φ hm hS hx hΦ hg ha⟩

/-- `anisoAll_of_gauss` instantiated at `τ = 1/10`, `c = 1/2`, `C = gaussMoment`, `ε = D = 1`
(conditional: the `∃ N₀` threshold exceeds the small instances, so the model hypotheses stay
binders). -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), (1 / 10 : ℝ) ≤ (M : ℝ) / N →
    (M : ℝ) / N ≤ (1 / 10 : ℝ)⁻¹ → SigmaAssumption (1 / 10) Sig →
    SpectralDomain (1 / 10) N S → OneXmOn (1 / 2) N (specOf Sig) S →
    EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
    AnisoAllAt N gaussMoment Sig S 1 1 :=
  anisoAll_of_gauss (1 / 10) (1 / 2) gaussMoment 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `avg_comparison` instantiated at `τ = 1/10`, `c = 1/2`, `C = gaussMoment`, `p = 2`, `δ = 1`,
`εa = 1/400`, `Da = dPrevTwo (1/10) 2` (conditional: the `∃ N₀` threshold exceeds the small
instances, so the model hypotheses stay binders). -/
example : ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), CompSetting (1 / 10) (1 / 2) M N Sig S →
    AnisoAllAt N (momMax gaussMoment) Sig S (1 / 400) (dPrevTwo (1 / 10) 2) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (momMax gaussMoment) X →
      ∀ z ∈ S, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        |∑ α : Fin M × Fin N,
            ((∫ x, Ft Sig (ofCoord x) z ^ 2 ∂(interpLawAt θ (fun _ => gaussLaw N)
                (entryLaw X) α (entryLaw X α)))
              - ∫ x, Ft Sig (ofCoord x) z ^ 2 ∂(interpLawAt θ (fun _ => gaussLaw N)
                (entryLaw X) α (gaussLaw N)))| ≤
          Cstar * (((N : ℝ) ^ (1 : ℝ) * Psi N (specOf Sig) z ^ 2) ^ 2 +
            ∫ x, Ft Sig (ofCoord x) z ^ 2 ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X))) :=
  avg_comparison (1 / 10) (1 / 2) gaussMoment 2 1 (1 / 400) (dPrevTwo (1 / 10) 2) (by norm_num)
    (by norm_num) (by norm_num) even_two le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl

/-- `avg_moment_bound` instantiated at `τ = 1/10`, `c = 1/2`, `c_Φ = phiConst (1/10)`,
`C = gaussMoment`, `p = 2`, `δ = 1`, `εa = 1/400`, `Da = dPrevTwo (1/10) 2` (conditional: the
`∃ N₀` threshold exceeds the small instances, so the model hypotheses stay binders). -/
example : ∃ Kp : ℝ, 0 < Kp ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ) (ε₁ D₁ : ℝ),
    CompSetting (1 / 10) (1 / 2) M N Sig S →
    AnisoAllAt N (momMax gaussMoment) Sig S (1 / 400) (dPrevTwo (1 / 10) 2) → 0 ≤ ε₁ →
    2 * ((2 : ℕ) : ℝ) + 1 ≤ D₁ → AveragedPhiLawAt N ε₁ D₁ Sig (gaussX M N) S Φ →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption gaussMoment X →
      ∀ z ∈ S, phiConst (1 / 10) * Psi N (specOf Sig) z ^ 2 ≤ Φ z →
        Integrable (fun ω => Ft Sig (X ω) z ^ 2) ∧
          ∫ ω, Ft Sig (X ω) z ^ 2 ≤ Kp * ((N : ℝ) ^ (1 + ε₁) * Φ z) ^ 2 :=
  avg_moment_bound (1 / 10) (1 / 2) (phiConst (1 / 10)) gaussMoment 2 1 (1 / 400)
    (dPrevTwo (1 / 10) 2) (by norm_num) (by norm_num) (by norm_num) (phiConst_pos (by norm_num))
    even_two le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- Theorem 3.21 (i) instantiated at `τ = 1/10`, `c = 1/2`, `C = gaussMoment`, `ε = D = 1`
(conditional: the `∃ N₀` threshold exceeds the small instances, so the model hypotheses stay
binders). -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    IsModel (1 / 10) gaussMoment M N Sig X → SpectralDomain (1 / 10) N S →
    OneXmOn (1 / 2) N (specOf Sig) S →
    EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
    AnisotropicLawAt N 1 1 Sig X S :=
  gen_iso_aniso (1 / 10) (1 / 2) gaussMoment 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- Theorem 3.21 (ii) instantiated at `τ = 1/10`, `c = 1/2`, `C = gaussMoment`, `ε = D = 1`
(conditional: the `∃ N₀` threshold exceeds the small instances, so the model hypotheses stay
binders). -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
    IsModel (1 / 10) gaussMoment M N Sig X → SpectralDomain (1 / 10) N S →
    OneXmOn (1 / 2) N (specOf Sig) S →
    EntrywiseLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
    AveragedLawAt N ε₁ D₁ (diagonal (specOf Sig)) (gaussX M N) S →
    AveragedLawAt N 1 1 Sig X S :=
  gen_iso_avg (1 / 10) (1 / 2) gaussMoment 1 1 (by norm_num) (by norm_num) (by norm_num)

end Anisotropic
