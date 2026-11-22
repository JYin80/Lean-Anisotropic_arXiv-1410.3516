module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.Stability.EdgeTaylor
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Instances.MarchenkoPasturTwo
public import Anisotropic.Qdot.Classical
public import Anisotropic.Qdot.Defs
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.EdgeLow
public import Anisotropic.Rigidity.Gap
public import Anisotropic.Rigidity.GaussCount
public import Anisotropic.Rigidity.Main

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 11.3, window-local: the edge and bulk pieces under (T_diag) -/

/-! ## The measure `ϱ`, the classical count `n` and the edges -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma rl_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
  refine ⟨hN, Nat.pos_of_ne_zero hM, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
    have : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at this
    simp at this
  have hgap := h.Sigma_gap
  have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul, hall]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
    simp [Set.indicator_of_mem h0]
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [happ, hM', ENNReal.toReal_one] at hgap
  linarith

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma rl_anti {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, -, hS⟩ := rl_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (by omega) (by omega)).trans (ih (by omega))

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` for `1 ≤ k ≤ 2p`. -/
private lemma rl_edge_mem {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ 2 * numBands N σ) :
    0 ≤ edgeVal N σ k ∧ edgeVal N σ k ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
  obtain ⟨hN, -, hS⟩ := rl_facts h
  exact edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hk hkp

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rl_varrho_apply (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma rl_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) =
      varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- `n` is nonincreasing. -/
private lemma rl_nClass_anti {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) : nClass N σ y ≤ nClass N σ x := by
  have := rl_nClass_sub hσ hN hxy
  have h0 : 0 ≤ (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal := by positivity
  linarith

/-- `n ≥ 0`. -/
private lemma rl_nClass_nonneg (σ : Fin M → ℝ) (x : ℝ) : 0 ≤ nClass N σ x := by
  unfold nClass; positivity

/-- If `ρ ≥ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≥ N c₀ (y − x)`. -/
private lemma rl_nClass_sub_ge {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, c₀ ≤ rhoDens N σ u) :
    N * c₀ * (y - x) ≤ nClass N σ x - nClass N σ y := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rl_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hge : ENNReal.ofReal (c₀ * (y - x)) ≤ varrho N σ (Set.Ico x y) := by
    rw [rl_varrho_apply σ measurableSet_Ico hsub]
    calc ENNReal.ofReal (c₀ * (y - x))
        = ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
      _ ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
  have h1 : c₀ * (y - x) ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * c₀ * (y - x) = N * (c₀ * (y - x)) := by ring
    _ ≤ N * (varrho N σ (Set.Ico x y)).toReal := mul_le_mul_of_nonneg_left h1 hN0

/-- If `ρ ≤ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≤ N c₀ (y − x)`. -/
private lemma rl_nClass_sub_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, rhoDens N σ u ≤ c₀) :
    nClass N σ x - nClass N σ y ≤ N * c₀ * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rl_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hle : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (c₀ * (y - x)) := by
    rw [rl_varrho_apply σ measurableSet_Ico hsub]
    calc ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u)
        ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
      _ = ENNReal.ofReal (c₀ * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ c₀ * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal ≤ N * (c₀ * (y - x)) :=
        mul_le_mul_of_nonneg_left h1 hN0
    _ = N * c₀ * (y - x) := by ring

/-- `d_k ≤ M ∧ N` for `1 ≤ k ≤ p`, and `d_p = M ∧ N`. -/
private lemma rl_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    cumCount N σ k ≤ min M N ∧ cumCount N σ (numBands N σ) = min M N := by
  obtain ⟨hN, hM, hS⟩ := rl_facts hda
  have hp := (card_innerCrit N σ hda.nonneg hN hS).2
  have hsum := (Ni_sum N σ hσ hN hM).2
  have hnn : ∀ l ∈ Finset.Icc 1 (numBands N σ), l ∉ Finset.Icc 1 k →
      0 ≤ bandCount N σ l := fun l _ _ => by unfold bandCount; positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => bandCount N σ l)
    (Finset.Icc_subset_Icc le_rfl hkp) hnn
  obtain ⟨hc1, -, -⟩ := cumCount_spec hda hk hkp
  obtain ⟨hcp, -, -⟩ := cumCount_spec hda hp le_rfl
  rw [hsum] at hle hcp
  rw [← hc1] at hle
  constructor
  · have : (cumCount N σ k : ℝ) ≤ ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hle
    exact_mod_cast this
  · have : (cumCount N σ (numBands N σ) : ℝ) = ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hcp
    exact_mod_cast this

/-- `d_0 = 0`. -/
private lemma rl_cum_zero (N : ℕ) (σ : Fin M → ℝ) : cumCount N σ 0 = 0 := by
  simp [cumCount]

/-- `n(x) ≤ d_k` for `a_{2k} < x`, `1 ≤ k ≤ p`. -/
private lemma rl_n_le_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx : edgeVal N σ (2 * k) < x) :
    nClass N σ x ≤ cumCount N σ k := by
  obtain ⟨hN, -, hS⟩ := rl_facts hda
  have hσ := hda.nonneg
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hna := (nClass_edgeVal hda hk hkp).1
  have hcr : (cumCount N σ k : ℝ) = cumCount N σ (k - 1) + bandCount N σ k := by
    rw [← hcs]; push_cast; rw [hbn]
  rcases le_or_gt (edgeVal N σ (2 * k - 1)) x with h1 | h1
  · have := rl_nClass_anti hσ hN h1
    have h0 : 0 ≤ bandCount N σ k := by unfold bandCount; positivity
    linarith
  · have := isProbabilityMeasure_varrho N σ hσ hN
    have hs := rl_nClass_sub hσ hN h1.le
    have hmono : (varrho N σ (Set.Ico x (edgeVal N σ (2 * k - 1)))).toReal ≤
        (varrho N σ (Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono fun t ht => ⟨le_trans hx.le ht.1, ht.2.le⟩)
    have hb : bandCount N σ k =
        N * (varrho N σ (Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)))).toReal := rfl
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left hmono hN0
    linarith

/-- (def:gamma_alpha): `n(x) ≥ j − 1/2` at `x > 0` gives `x ≤ γ_j`. -/
private lemma rl_le_gamma {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {j : ℕ}
    (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x) (hn : (j : ℝ) - 1 / 2 ≤ nClass N σ x) :
    x ≤ gammaLoc N σ j := by
  obtain ⟨hN, -, hS⟩ := rl_facts h
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbdd : BddAbove {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N σ E} := by
    refine ⟨edgeVal N σ 1, fun E hE => ?_⟩
    by_contra hlt
    push Not at hlt
    have hsub : Set.Ici E ⊆ (Set.Icc 0 (edgeVal N σ 1))ᶜ := fun t ht hmem =>
      absurd (le_trans (Set.mem_Ici.mp ht) hmem.2) (not_le.mpr hlt)
    have h0 : varrho N σ (Set.Ici E) = 0 :=
      measure_mono_null hsub (varrho_compl_Icc_edgeVal N σ h.nonneg hN hS)
    have : nClass N σ E = 0 := by simp [nClass, h0]
    linarith [hE.2]
  exact le_csSup hbdd ⟨hx, hn⟩

/-- `A ⊆ B` and `A` holds with high probability: so does `B`. -/
private lemma rl_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : HighProbAt N D A) (hAB : A ⊆ B) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 hAB)).trans h

/-- Two events of probability `≥ 1 − N^{−D−1}` intersect in an event of probability
`≥ 1 − N^{−D}`, for `N ≥ 2`. -/
private lemma rl_hp_inter {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (hN : 2 ≤ N) (hA : HighProbAt N (D + 1) A) (hB : HighProbAt N (D + 1) B) :
    HighProbAt N D (A ∩ B) := by
  unfold HighProbAt at *
  rw [Set.compl_inter]
  refine (measure_union_le _ _).trans ((add_le_add hA hB).trans ?_)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hpos, Real.rpow_neg_one]
  rw [e]
  have h0 : 0 ≤ (N : ℝ) ^ (-D) := by positivity
  have h1 : (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN'
  nlinarith

/-- The eigenvalues `σ` of `Σ` are positive under Assumption 2.1. -/
private lemma rl_sigma_pos {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) : ∀ i, 0 < specOf Sig i := fun i => by
  rw [specOf_eq hm.sigma.posDef.isHermitian]
  exact hm.sigma.posDef.eigenvalues_pos i

/-- `C N^a ≤ N^b` for `a < b` and `N` large. -/
private lemma rl_ev (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((h1.eventually_ge_atTop C).and (Filter.eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h2, h3⟩ := hN₀ N hN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN]; ring_nf

/-- `(N − 1 : ℕ) = N − 1` in `ℝ` for `N ≥ 2`. -/
private lemma rl_cast_pred (hN : 2 ≤ N) : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; simp

/-- (phi_bounded), (bound_Sigma), (Sigma_gap) at `N − 1` with `τ/2`, from those at `N` with `τ`. -/
private lemma rl_da_pred {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hN : 2 ≤ N) :
    DensityAssumptions (τ / 2) (N - 1) σ := by
  have hτ := h.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := rl_cast_pred hN
  have hφl := h.phi_lower
  have hφu := h.phi_upper
  unfold phiRatio at hφl hφu
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  refine ⟨by positivity, h.nonneg, ?_, ?_, ?_, ?_⟩
  · unfold phiRatio
    rw [hc, le_div_iff₀ hN1]
    rw [le_div_iff₀ (by linarith)] at hφl
    nlinarith
  · unfold phiRatio
    rw [hc, div_le_iff₀ hN1]
    rw [div_le_iff₀ (by linarith)] at hφu
    have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [this]
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith
  · intro i
    have := h.bound_Sigma i
    have : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  · have := (h.mono (show 0 < τ / 2 by positivity) (by linarith)).Sigma_gap
    linarith

/-! ## Scaling and interlacing of sorted eigenvalues -/

section SpecSub

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- The orthogonal matrix whose columns are the eigenvectors of `A`. -/
private def rlU (hA : A.IsHermitian) : Matrix (Fin K) (Fin K) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)

/-- The coordinates of `w` in the eigenbasis of `A`. -/
private def rlC (hA : A.IsHermitian) (w : Fin K → ℝ) : Fin K → ℝ :=
  star (rlU hA) *ᵥ w

private lemma rlU_star_mul (hA : A.IsHermitian) : star (rlU hA) * rlU hA = 1 :=
  Unitary.coe_star_mul_self _

private lemma rlU_mul_star (hA : A.IsHermitian) : rlU hA * star (rlU hA) = 1 :=
  Unitary.coe_mul_star_self _

private lemma rlU_mulVec_rlC (hA : A.IsHermitian) (w : Fin K → ℝ) : rlU hA *ᵥ rlC hA w = w := by
  unfold rlC
  rw [mulVec_mulVec, rlU_mul_star, one_mulVec]

private lemma rlU_orth_dot (hA : A.IsHermitian) (x y : Fin K → ℝ) :
    (rlU hA *ᵥ x) ⬝ᵥ (rlU hA *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, mulVec_mulVec]
  have : (rlU hA)ᵀ * rlU hA = 1 := by
    have h := rlU_star_mul hA
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [this, one_mulVec]

private lemma rlU_decomp (hA : A.IsHermitian) :
    A = rlU hA * diagonal hA.eigenvalues * star (rlU hA) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [rlU] using this

private lemma rl_dot_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ w = ∑ j, (rlC hA w j) ^ 2 := by
  conv_lhs => rw [← rlU_mulVec_rlC hA w]
  rw [rlU_orth_dot]
  simp [dotProduct, sq]

private lemma rl_quad_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ (A *ᵥ w) = ∑ j, hA.eigenvalues j * (rlC hA w j) ^ 2 := by
  have h1 : A *ᵥ w = rlU hA *ᵥ (diagonal hA.eigenvalues *ᵥ rlC hA w) := by
    conv_lhs => rw [rlU_decomp hA]
    unfold rlC
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1]
  nth_rewrite 1 [← rlU_mulVec_rlC hA w]
  rw [rlU_orth_dot]
  simp only [dotProduct, mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The linear map recording the eigencoordinates of `w` indexed by `s`. -/
private def rlMap (hA : A.IsHermitian) (s : Finset (Fin K)) : (Fin K → ℝ) →ₗ[ℝ] (s → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : s → Fin K)) ∘ₗ Matrix.mulVecLin (star (rlU hA))

private lemma rl_mem_ker_rlMap (hA : A.IsHermitian) (s : Finset (Fin K)) (w : Fin K → ℝ) :
    w ∈ LinearMap.ker (rlMap hA s) ↔ ∀ j ∈ s, rlC hA w j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 j.2

private lemma rl_le_finrank_ker (hA : A.IsHermitian) (s : Finset (Fin K)) :
    K ≤ Module.finrank ℝ (LinearMap.ker (rlMap hA s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (rlMap hA s)
  have h1 : Module.finrank ℝ (LinearMap.range (rlMap hA s)) ≤ s.card := by
    calc Module.finrank ℝ (LinearMap.range (rlMap hA s)) ≤ Module.finrank ℝ (s → ℝ) :=
          Submodule.finrank_le _
      _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℝ (Fin K → ℝ) = K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

private lemma rl_eigCount_add_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E + (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j).card = K := by
  have : eigCount A E = (Finset.univ.filter fun j => E ≤ hA.eigenvalues j).card := by
    unfold eigCount
    rw [specOf_eq hA]
  rw [this, Finset.card_filter_add_card_filter_not]
  simp

/-- A spectral subspace: dimension at least `n_A(E)`, and `⟨w, A w⟩ ≥ E |w|²` on it. -/
private lemma rl_spectral_subspace (hA : A.IsHermitian) (E : ℝ) :
    ∃ W : Submodule ℝ (Fin K → ℝ), eigCount A E ≤ Module.finrank ℝ W ∧
      ∀ w ∈ W, E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w) := by
  set s := Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j with hs
  have hz : ∀ w ∈ LinearMap.ker (rlMap hA s), ∀ j, hA.eigenvalues j < E → rlC hA w j = 0 := by
    intro w hw j hj
    exact (rl_mem_ker_rlMap hA s w).mp hw j (by simpa [hs] using hj)
  refine ⟨LinearMap.ker (rlMap hA s), ?_, ?_⟩
  · have h1 := rl_le_finrank_ker hA s
    have h2 : eigCount A E + s.card = K := rl_eigCount_add_card hA E
    omega
  · intro w hw
    rw [rl_quad_eq_sum hA, rl_dot_eq_sum hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : hA.eigenvalues j < E
    · rw [hz w hw j hj]; simp
    · exact mul_le_mul_of_nonneg_right (not_lt.mp hj) (sq_nonneg _)

/-- `n_A(E) ≤ n_{cA}(cE)` for `c > 0`. -/
private lemma rl_eigCount_le_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount A E ≤ eigCount (c • A) (c * E) := by
  obtain ⟨W, hW1, hW2⟩ := rl_spectral_subspace hA E
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine hW1.trans (eigCount_ge_of_subspace hcA W fun w hw => ?_)
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hW2 w hw) hc.le

/-- `n_{cA}(cE) = n_A(E)` for `c > 0`. -/
private lemma rl_eigCount_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount (c • A) (c * E) = eigCount A E := by
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine le_antisymm ?_ (rl_eigCount_le_smul hA hc E)
  have := rl_eigCount_le_smul hcA (inv_pos.mpr hc) (c * E)
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
    one_mul] at this

/-- `λ_j(cA) = c λ_j(A)` for `c > 0`, `1 ≤ j ≤ K`. -/
private lemma rl_sortedEig_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 1 ≤ j)
    (hjK : j ≤ K) : sortedEig (c • A) j = c * sortedEig A j := by
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  have key : ∀ x, x ≤ sortedEig (c • A) j ↔ x ≤ c * sortedEig A j := by
    intro x
    rw [sortedEig_ge_iff hcA hj hjK, show x = c * (x / c) by field_simp, rl_eigCount_smul hA hc,
      ← sortedEig_ge_iff hA hj hjK, mul_le_mul_iff_of_pos_left hc]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

end SpecSub

/-- `λ̇_{k,i} = (N/(N−1)) λ_j(π̄ B π̄)`, `j = Ṅ_1 + ⋯ + Ṅ_{k−1} + i`. -/
private lemma rl_lamDot_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) {l i : ℕ}
    (hj : 1 ≤ cumCount (N - 1) (specOf Sig) (l - 1) + i)
    (hjN : cumCount (N - 1) (specOf Sig) (l - 1) + i ≤ N) :
    lamDotBand Sig Xm l i = (N : ℝ) / (N - 1) *
      sortedEig (QN Sig (Xdot Xm)) (cumCount (N - 1) (specOf Sig) (l - 1) + i) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) / (N - 1) := div_pos (by linarith) (by linarith)
  unfold lamDotBand QdotN
  exact rl_sortedEig_smul (XSX_isHermitian hSig (Xdot Xm)) hc hj hjN

/-- Cauchy interlacing for `π̄ B π̄`: `λ_{j+1}(B) ≤ λ_j(π̄ B π̄)`. -/
private lemma rl_interlace_lo {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {j : ℕ} (hj : 1 ≤ j) (hjN : j + 1 ≤ N) :
    sortedEig (QN Sig Xm) (j + 1) ≤ sortedEig (QN Sig (Xdot Xm)) j := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  set x := sortedEig (QN Sig Xm) (j + 1)
  have h1 := (sortedEig_ge_iff hB (by omega) hjN x).1 le_rfl
  have h2 := eigCount_le_compress_add_one hSig Xm x
  exact (sortedEig_ge_iff hB' hj (by omega) x).2 (by omega)

/-- Cauchy interlacing for `π̄ B π̄`: `λ_j(π̄ B π̄) ≤ λ_j(B)` when `λ_j(π̄ B π̄) > 0`. -/
private lemma rl_interlace_hi {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpos : 0 < sortedEig (QN Sig (Xdot Xm)) j) :
    sortedEig (QN Sig (Xdot Xm)) j ≤ sortedEig (QN Sig Xm) j := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  set x := sortedEig (QN Sig (Xdot Xm)) j
  have h1 := (sortedEig_ge_iff hB' hj hjN x).1 le_rfl
  have h2 := eigCount_compress_le hSig Xm hpos
  exact (sortedEig_ge_iff hB hj hjN x).2 (h1.trans h2)

/-- If `0 < L ≤ λ_j(π̄ B π̄)` and `λ_j(B) ≤ U`, then
`L ≤ (N/(N−1)) λ_j(π̄ B π̄) ≤ U + U/(N − 1)`. -/
private lemma rl_dot_bounds {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) {L U : ℝ}
    (hL : 0 < L) (hLj : L ≤ sortedEig (QN Sig (Xdot Xm)) j) (hU : sortedEig (QN Sig Xm) j ≤ U) :
    L ≤ (N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j ∧
      (N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j ≤ U + U / (N - 1) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < sortedEig (QN Sig (Xdot Xm)) j := lt_of_lt_of_le hL hLj
  have hle := rl_interlace_hi hSig Xm hj hjN hpos
  set x := sortedEig (QN Sig (Xdot Xm)) j
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have e : (N : ℝ) / (N - 1) = 1 + 1 / (N - 1) := by field_simp; ring
  have hU0 : 0 ≤ U := by linarith
  rw [e]
  constructor
  · have : 0 ≤ 1 / ((N : ℝ) - 1) * x := by positivity
    nlinarith
  · have h1 : 1 / ((N : ℝ) - 1) * x ≤ 1 / ((N : ℝ) - 1) * U :=
      mul_le_mul_of_nonneg_left (hle.trans hU) (by positivity)
    have e2 : U / ((N : ℝ) - 1) = 1 / ((N : ℝ) - 1) * U := by ring
    nlinarith

/-! ## The bulk piece -/

/-- `U/(N − 1) ≤ 2U/N` for `U ≥ 0`, `N ≥ 2`. -/
private lemma rl_div_pred {U : ℝ} (hU : 0 ≤ U) (hN : 2 ≤ N) :
    U / ((N : ℝ) - 1) ≤ 2 * U * (N : ℝ)⁻¹ := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_iff₀ (by linarith)]
  have e : 2 * U * (N : ℝ)⁻¹ * ((N : ℝ) - 1) = U * (2 - 2 / N) := by
    field_simp
  rw [e]
  have : 2 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  nlinarith

set_option maxHeartbeats 1000000 in
-- many linear-arithmetic steps over a large context
/-- The bulk step at one index, on the rigidity event of Theorem 3.15 (iii) at `N`. -/
private lemma rl_bulk_det {τ τ' c₀ ε ε₁ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hda : DensityAssumptions τ N (specOf Sig))
    (hσ : ∀ j, 0 < specOf Sig j) (hSig : Sig.IsHermitian) (hN2 : 2 ≤ N) (hk1 : 1 ≤ k)
    (hkp : k ≤ numBands N (specOf Sig)) (hτ' : 0 < τ') (hc0 : 0 < c₀) (hε₁0 : 0 < ε₁)
    (hρ : ∀ E ∈ Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ' / 2)
      (edgeVal N (specOf Sig) (2 * k - 1) - τ' / 2), c₀ ≤ rhoDens N (specOf Sig) E)
    (hsub : ∀ E, min τ τ' ≤ E →
      |nClass (N - 1) (specOf Sig) E - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε₁)
    (hω : ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k →
      gammaBand N (specOf Sig) k i ∈ Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ' / 2)
        (edgeVal N (specOf Sig) (2 * k - 1) - τ' / 2) →
      |lamBand Sig Xm k i - gammaBand N (specOf Sig) k i| ≤ (N : ℝ) ^ ε₁ * (N : ℝ)⁻¹)
    (f3 : (2 / c₀ + 1 + 2 * (2 * τ⁻¹ * (1 + τ⁻¹))) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε)
    (f4 : 4 / (c₀ * τ') * (N : ℝ) ^ ε₁ ≤ N) (f5 : 4 / τ' * (N : ℝ) ^ ε₁ ≤ N)
    {l i : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ numBands (N - 1) (specOf Sig)) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat (N - 1) (specOf Sig) l)
    (hE : gammaBand (N - 1) (specOf Sig) l i ∈
      Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ') (edgeVal N (specOf Sig) (2 * k - 1) - τ')) :
    |lamDotBand Sig Xm l i - gammaBand (N - 1) (specOf Sig) l i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
  have hτ := hda.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  set K := 2 / c₀ + 1 + 2 * Ca with hK
  set σ := specOf Sig with hσdef
  have hdaN1 := rl_da_pred hda hN2
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  -- the index `j` at `N − 1`
  obtain ⟨-, -, hcs'⟩ := cumCount_spec hdaN1 hl1 hlp
  have hcl := (rl_cum hdaN1 hσ hl1 hlp).1
  have hj1 : 1 ≤ cumCount (N - 1) σ (l - 1) + i := by omega
  have hjM : cumCount (N - 1) σ (l - 1) + i ≤ min M (N - 1) := by omega
  obtain ⟨-, hnE⟩ := nClass_gammaLoc hdaN1 hσ hj1 hjM
  have hEdef : gammaBand (N - 1) σ l i = gammaLoc (N - 1) σ (cumCount (N - 1) σ (l - 1) + i) :=
    rfl
  rw [hEdef] at hE ⊢
  rw [rl_lamDot_eq hSig Xm hN2 hj1 (by omega : cumCount (N - 1) σ (l - 1) + i ≤ N)]
  set j := cumCount (N - 1) σ (l - 1) + i with hj
  set E := gammaLoc (N - 1) σ j with hEd
  set a₂ := edgeVal N σ (2 * k) with ha₂
  set a₁ := edgeVal N σ (2 * k - 1) with ha₁
  have ha₂0 := (rl_edge_mem hda (k := 2 * k) (by omega) (by omega)).1
  have ha₁C := (rl_edge_mem hda (k := 2 * k - 1) (by omega) (by omega)).2
  rw [← ha₁, ← hCa] at ha₁C
  rw [← ha₂] at ha₂0
  have hEτ : min τ τ' ≤ E := le_trans (min_le_right _ _) (by linarith [hE.1])
  have hsub := hsub E hEτ
  rw [abs_le] at hsub
  -- the window of half-width `r`
  set s := (N : ℝ) ^ ε₁ with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) hε₁0.le
  set r := (s + 1) / (c₀ * N) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hNcr : (N : ℝ) * c₀ * r = s + 1 := by rw [hr]; field_simp
  have hrτ : r ≤ τ' / 2 := by
    rw [hr, div_le_iff₀ (by positivity)]
    have e : 4 / (c₀ * τ') * s * (c₀ * τ' / 8) = s / 2 := by field_simp; ring
    have := mul_le_mul_of_nonneg_right f4 (by positivity : (0 : ℝ) ≤ c₀ * τ' / 8)
    rw [e] at this
    linarith
  have hsN : s * (N : ℝ)⁻¹ ≤ τ' / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
    have e : 4 / τ' * s * (τ' / 4) = s := by field_simp
    have := mul_le_mul_of_nonneg_right f5 (by positivity : (0 : ℝ) ≤ τ' / 4)
    rw [e] at this
    linarith
  have hwin : ∀ x, E - r ≤ x → x ≤ E + r →
      x ∈ Set.Icc (a₂ + τ' / 2) (a₁ - τ' / 2) :=
    fun x h1 h2 => ⟨by linarith [hE.1], by linarith [hE.2]⟩
  have hm1 := rl_nClass_sub_ge hda.nonneg hN0 (x := E - r) (y := E) (c₀ := c₀)
    (by linarith [hE.1]) (by linarith) hc0.le
    (fun u hu => hρ u (hwin u hu.1 (by linarith [hu.2])))
  have hm2 := rl_nClass_sub_ge hda.nonneg hN0 (x := E) (y := E + r) (c₀ := c₀)
    (by linarith [hE.1]) (by linarith) hc0.le
    (fun u hu => hρ u (hwin u (by linarith [hu.1]) (by linarith [hu.2])))
  rw [show E - (E - r) = r by ring, hNcr] at hm1
  rw [show E + r - E = r by ring, hNcr] at hm2
  have hjr : (j : ℝ) - 1 / 2 = nClass (N - 1) σ E := hnE.symm
  have hlo : (j : ℝ) + 1 / 2 ≤ nClass N σ (E - r) := by linarith
  have hhi : nClass N σ (E + r) ≤ (j : ℝ) - 3 / 2 := by linarith
  -- `j` and `j + 1` lie in the band `k` at `N`
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk1 hkp
  have hna := (nClass_edgeVal hda hk1 hkp).1
  have hcm := (rl_cum hda hσ hk1 hkp).1
  have hc1 : (cumCount N σ (k - 1) : ℝ) ≤ (j : ℝ) - 3 / 2 := by
    rw [← hna]
    exact le_trans (rl_nClass_anti hda.nonneg hN0 (by linarith [hE.2])) hhi
  have hc2 : (j : ℝ) + 1 / 2 ≤ cumCount N σ k :=
    hlo.trans (rl_n_le_cum hda hk1 hkp (by linarith [hE.1]))
  have hc1' : cumCount N σ (k - 1) + 1 ≤ j := by
    have : (cumCount N σ (k - 1) : ℝ) + 1 ≤ j := by linarith
    exact_mod_cast this
  have hc2' : j + 1 ≤ cumCount N σ k := by
    have : (j : ℝ) + 1 ≤ cumCount N σ k := by
      have h := hc2
      have : ((j + 1 : ℕ) : ℝ) < (cumCount N σ k : ℝ) + 1 := by push_cast; linarith
      have := Nat.lt_succ_iff.mp (by exact_mod_cast this)
      exact_mod_cast this
    exact_mod_cast this
  have hjMN : j + 1 ≤ min M N := hc2'.trans hcm
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 (by omega)
  obtain ⟨-, hnγ'⟩ := nClass_gammaLoc hda hσ (by omega : 1 ≤ j + 1) hjMN
  push_cast at hnγ'
  -- the classical locations `γ_j`, `γ_{j+1}` at `N` near `E`
  have hγ1 : gammaLoc N σ j ≤ E + r := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (le_of_lt (not_le.mp hc))
    linarith
  have hγ2 : E - r ≤ gammaLoc N σ j :=
    rl_le_gamma hda hj1 (by linarith [hE.1]) (by linarith)
  have hγ3 : gammaLoc N σ (j + 1) ≤ E + r := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (le_of_lt (not_le.mp hc))
    linarith
  have hγ4 : E - r ≤ gammaLoc N σ (j + 1) :=
    rl_le_gamma hda (by omega) (by linarith [hE.1]) (by push_cast; linarith)
  -- rigidity at `N` for `j` and `j + 1`
  set i₁ := j - cumCount N σ (k - 1) with hi₁
  have hi₁j : cumCount N σ (k - 1) + i₁ = j := by omega
  have hi₁j' : cumCount N σ (k - 1) + (i₁ + 1) = j + 1 := by omega
  have hr1 := hω i₁ (by omega) (by omega)
    (by rw [gammaBand, hi₁j]; exact hwin _ hγ2 hγ1)
  have hr2 := hω (i₁ + 1) (by omega) (by omega)
    (by rw [gammaBand, hi₁j']; exact hwin _ hγ4 hγ3)
  rw [lamBand, gammaBand, hi₁j] at hr1
  rw [lamBand, gammaBand, hi₁j'] at hr2
  rw [abs_le] at hr1 hr2
  -- interlacing and the factor `N/(N − 1)`
  set L := sortedEig (QN Sig Xm) (j + 1) with hL
  set U := sortedEig (QN Sig Xm) j with hU
  have hL0 : 0 < L := by linarith [hE.1]
  have hLj := rl_interlace_lo hSig Xm hj1 (hc2'.trans (hcm.trans (min_le_right _ _)))
  obtain ⟨hb1, hb2⟩ := rl_dot_bounds hSig Xm hN2 hj1 (by omega) hL0 hLj le_rfl
  have hU0 : 0 ≤ U := by linarith [hE.1, hr1.1]
  have hUle : U ≤ Ca := by linarith [hE.2, hr1.2]
  have hdiv := rl_div_pred hU0 hN2
  have hfin : (s + 1) / c₀ + s + 2 * Ca ≤ (N : ℝ) ^ ε := by
    refine le_trans ?_ f3
    rw [hK]
    have h1 : (s + 1) / c₀ ≤ 2 / c₀ * s := by
      rw [div_le_iff₀ hc0]; field_simp; linarith
    have h2 : 2 * Ca ≤ 2 * Ca * s := by nlinarith
    linarith
  have hNi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  have hfin' : r + s * (N : ℝ)⁻¹ + 2 * Ca * (N : ℝ)⁻¹ ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
    have e : r = (s + 1) / c₀ * (N : ℝ)⁻¹ := by rw [hr]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_right hfin hNi.le
    linarith
  have h2U : 2 * U * (N : ℝ)⁻¹ ≤ 2 * Ca * (N : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hNi.le
  have hCN : 0 ≤ 2 * Ca * (N : ℝ)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Rigidity of `λ̇` in the bulk of a regular component `k`, under (T_diag). -/
theorem rigidity_dot_bulk (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularBulk c N (specOf Sig) k →
      (RegularEdge τ N (specOf Sig) (2 * k) ∨ RegularEdge τ N (specOf Sig) (2 * k - 1)) →
      HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf Sig) l →
        gammaBand (N - 1) (specOf Sig) l i ∈
          Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ') (edgeVal N (specOf Sig) (2 * k - 1) - τ') →
        |lamDotBand Sig (X ω) l i - gammaBand (N - 1) (specOf Sig) l i| ≤
          (N : ℝ) ^ ε * (N : ℝ)⁻¹} := by
  by_cases hc0 : 0 < c (τ' / 2)
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k _ hb _ => absurd ((hb.2.2 (τ' / 2) (by linarith)).1) hc0⟩
  set c₀ := c (τ' / 2) with hc₀
  set ε₁ := min ε 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by have := lt_min hε one_pos; rw [hε₁]; linarith
  have hε₁ε : ε₁ < ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  have hε₁1 : ε₁ < 1 := by have := min_le_right ε 1; rw [hε₁]; linarith
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  set K := 2 / c₀ + 1 + 2 * Ca with hK
  obtain ⟨N₁, h₁⟩ := rigidity_bulk τ (τ' / 2) c C ε₁ D hτ (by linarith) hε₁0
  obtain ⟨N₂, h₂⟩ := nClass_pred_sub (min τ τ') ε₁ (lt_min hτ hτ') hε₁0
  obtain ⟨N₃, h₃⟩ := rl_ev K hε₁ε
  obtain ⟨N₄, h₄⟩ := rl_ev (4 / (c₀ * τ')) (a := ε₁) (b := 1) hε₁1
  obtain ⟨N₅, h₅⟩ := rl_ev (4 / τ') (a := ε₁) (b := 1) hε₁1
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 2)),
    fun N hN Ω _ _ M Sig X k hm hb hedge => ?_⟩
  have hN1 : N₁ ≤ N := le_of_max_le_left (le_of_max_le_left hN)
  have hN2' : N₂ ≤ N := le_of_max_le_right (le_of_max_le_left hN)
  have f3 := h₃ N (le_of_max_le_left (le_of_max_le_left (le_of_max_le_right hN)))
  have f4 := h₄ N (le_of_max_le_right (le_of_max_le_left (le_of_max_le_right hN)))
  have f5 := h₅ N (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hN)))
  have hN2 : 2 ≤ N := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hN))
  rw [Real.rpow_one] at f4 f5
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := rl_sigma_pos hm
  have hSig := hm.sigma.posDef.isHermitian
  have hda0 : DensityAssumptions (min τ τ') N (specOf Sig) :=
    hda.mono (lt_min hτ hτ') (min_le_left _ _)
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  obtain ⟨hk1, hkp, hbk⟩ := hb
  have hρ := (hbk (τ' / 2) (by linarith)).2
  refine rl_hp_mono (h₁ N hN1 M Sig X k hm ⟨hk1, hkp, hbk⟩ hedge) fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro l hl1 hlp i hi hiN hE
  exact rl_bulk_det hda hσ hSig hN2 hk1 hkp hτ' hc0 hε₁0 hρ
    (fun E hE => h₂ N hN2' M (specOf Sig) hda0 E hE) hω f3 f4 f5 hl1 hlp hi hiN hE

/-! ## The square-root inversion near an edge (real arithmetic) -/

/-- `max(1, 2c₂)`. -/
private def rlM (c₂ : ℝ) : ℝ := max 1 (2 * c₂)

/-- The spacing constant `L = 4 max(1, 2c₂)/c₁`. -/
private def rlL (c₁ c₂ : ℝ) : ℝ := 4 * rlM c₂ / c₁

/-- The threshold `K = 2 L max(1, 2c₂)²` between the edge and the spacing regimes. -/
private def rlK (c₁ c₂ : ℝ) : ℝ := 2 * rlL c₁ c₂ * rlM c₂ ^ 2

/-- If the density on `[v₁, v₂] ⊆ [0, t]` is at least `c₁√v₁` times the step, the mass between
the edge and distance `v` is at least `N c₁ √v v / 4`. -/
private lemma rl_mass_low {N c₁ t v : ℝ} {Φ : ℝ → ℝ} (hN : 0 < N) (hc₁ : 0 < c₁)
    (hΦ0 : Φ 0 = 0)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hv : 0 < v) (hvt : v ≤ t) : N * c₁ * √v * v / 4 ≤ Φ v := by
  have ha := hlo (v / 2) v (by positivity) (by linarith) hvt
  have hb := hlo 0 (v / 2) le_rfl (by positivity) (by linarith)
  rw [hΦ0, Real.sqrt_zero, mul_zero, zero_mul] at hb
  have hsq : √v / 2 ≤ √(v / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h := Real.sq_sqrt hv.le
    have e : (√v / 2) ^ 2 = (√v) ^ 2 / 4 := by ring
    rw [e, h]
    linarith
  have hc : N * c₁ * (√v / 2) * (v - v / 2) ≤ N * c₁ * √(v / 2) * (v - v / 2) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have he : N * c₁ * (√v / 2) * (v - v / 2) = N * c₁ * √v * v / 4 := by ring
  linarith

/-- `x ≤ E β` follows from `8 x³ i N² ≤ E³` when `β³ i N² = 1`. -/
private lemma rl_cube {x E β N : ℝ} {i : ℕ} (hβ : 0 < β) (hE : 0 ≤ E)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (h : 8 * x ^ 3 * i * N ^ 2 ≤ E ^ 3) : 2 * x ≤ E * β := by
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  calc (2 * x) ^ 3 = 8 * x ^ 3 * (β ^ 3 * i * N ^ 2) := by rw [hβi]; ring
    _ = β ^ 3 * (8 * x ^ 3 * i * N ^ 2) := by ring
    _ ≤ β ^ 3 * E ^ 3 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (E * β) ^ 3 := by ring

/-- The edge regime `i < K s` of the inversion: `|μ − u| ≤ E β`. -/
private lemma rl_core_small {N s y E β c₁ K t u μ : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hc₁ : 0 < c₁) (hK : 0 < K) (hβ : 0 < β)
    (hE : 0 ≤ E) (hβi : β ^ 3 * i * N ^ 2 = 1)
    (hu : 0 < u) (hut : u ≤ t) (hYt : y ^ 2 ≤ t)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, 0 ≤ v → v ≤ t → (i : ℝ) + 1 ≤ m v → μ ≤ v) (hexcl : -y ^ 2 ≤ μ)
    (hreg : (i : ℝ) < K * s)
    (hA2 : (K + 1) * s + 1 ≤ N * c₁ * y ^ 3 / 4)
    (hA3 : 128 * K ^ 3 * s ^ 3 ≤ c₁ ^ 2 * E ^ 3)
    (hA4 : 8 * K * s * y ^ 6 * N ^ 2 ≤ E ^ 3) :
    |μ - u| ≤ E * β := by
  have hY := rl_mass_low hN hc₁ hΦ0 hlo (v := y ^ 2) (by positivity) hYt
  rw [Real.sqrt_sq hy.le] at hY
  have hmY : (i : ℝ) + 1 ≤ m (y ^ 2) := by
    have := (abs_le.1 (hcount (y ^ 2) (by positivity) hYt)).1
    have e : N * c₁ * y * y ^ 2 / 4 = N * c₁ * y ^ 3 / 4 := by ring
    linarith
  have hμY : μ ≤ y ^ 2 := h1 _ (by positivity) hYt hmY
  set r := √u with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hu
  have hru : r ^ 2 = u := Real.sq_sqrt hu.le
  have hur : N * c₁ * r * u / 4 ≤ i - 1 / 2 := by
    rw [← hΦu]; exact rl_mass_low hN hc₁ hΦ0 hlo hu hut
  have hA : N * c₁ * r ^ 3 ≤ 4 * K * s := by
    have e : N * c₁ * r * u = N * c₁ * r ^ 3 := by rw [← hru]; ring
    linarith
  have hu3 : 8 * u ^ 3 * i * N ^ 2 ≤ E ^ 3 := by
    have hC : 8 * u ^ 3 * i * N ^ 2 * c₁ ^ 2 ≤ E ^ 3 * c₁ ^ 2 := by
      have e : 8 * u ^ 3 * i * N ^ 2 * c₁ ^ 2 = 8 * (N * c₁ * r ^ 3) ^ 2 * i := by
        rw [← hru]; ring
      rw [e]
      calc 8 * (N * c₁ * r ^ 3) ^ 2 * i ≤ 8 * (4 * K * s) ^ 2 * (K * s) := by
            have := hreg.le
            gcongr
        _ = 128 * K ^ 3 * s ^ 3 := by ring
        _ ≤ c₁ ^ 2 * E ^ 3 := hA3
        _ = E ^ 3 * c₁ ^ 2 := by ring
    exact le_of_mul_le_mul_right hC (by positivity)
  have hY3 : 8 * (y ^ 2) ^ 3 * i * N ^ 2 ≤ E ^ 3 := by
    calc 8 * (y ^ 2) ^ 3 * i * N ^ 2 ≤ 8 * (y ^ 2) ^ 3 * (K * s) * N ^ 2 := by
          have := hreg.le
          gcongr
      _ = 8 * K * s * y ^ 6 * N ^ 2 := by ring
      _ ≤ E ^ 3 := hA4
  have h3 := rl_cube hβ hE hβi hu3
  have h4 := rl_cube hβ hE hβi hY3
  have hy2 : 0 ≤ y ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The spacing regime `i ≥ K s` of the inversion: `|μ − u| ≤ L s β ≤ E β`. -/
private lemma rl_core_big {N s β c₁ c₂ M L t u μ E : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 1 ≤ s) (hc₁ : 0 < c₁) (hβ : 0 < β) (hM1 : 1 ≤ M) (hM2 : 2 * c₂ ≤ M)
    (hL : L * c₁ = 4 * M) (hL0 : 0 < L)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (hi : (1 : ℝ) ≤ i)
    (hu : 0 < u) (hut : u ≤ t / 2)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hhi : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → Φ v₂ - Φ v₁ ≤ N * c₂ * √v₂ * (v₂ - v₁))
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, 0 ≤ v → v ≤ t → (i : ℝ) + 1 ≤ m v → μ ≤ v)
    (h2 : ∀ v, 0 ≤ v → v ≤ t → μ < v → (i : ℝ) ≤ m v)
    (hreg : 2 * L * M ^ 2 * s ≤ i) (hA5 : L * s ≤ E) :
    |μ - u| ≤ E * β := by
  have hM0 : 0 < M := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  set r := √u with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hu
  have hru : r ^ 2 = u := Real.sq_sqrt hu.le
  set w := 1 / (N * β) with hw
  have hw0 : 0 < w := by positivity
  have hNβw : N * β * w = 1 := by rw [hw]; field_simp
  have hiw : (i : ℝ) = N * w ^ 3 := by
    have e1 : (i : ℝ) = 1 / (β ^ 3 * N ^ 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [e1, hw]
    field_simp
  have hhu := hhi 0 u le_rfl hu.le (by linarith)
  rw [hΦ0, hΦu, ← hr, sub_zero, sub_zero] at hhu
  have hw3 : w ^ 3 ≤ M * r ^ 3 := by
    have h5 : N * w ^ 3 ≤ N * (2 * c₂ * r ^ 3) := by
      rw [← hiw]
      have e : N * c₂ * r * u = N * (c₂ * r ^ 3) := by rw [← hru]; ring
      have : N * (2 * c₂ * r ^ 3) = 2 * (N * (c₂ * r ^ 3)) := by ring
      linarith
    have h6 : w ^ 3 ≤ 2 * c₂ * r ^ 3 := le_of_mul_le_mul_left h5 hN
    have h7 : 2 * c₂ * r ^ 3 ≤ M * r ^ 3 := mul_le_mul_of_nonneg_right hM2 (by positivity)
    linarith
  have hwr : w ≤ M * r := by
    by_contra hc
    have hc' : M * r < w := lt_of_not_ge hc
    have h5 : (M * r) ^ 3 < w ^ 3 := pow_lt_pow_left₀ hc' (by positivity) (by norm_num)
    have hM3 : M ≤ M ^ 3 := by
      have : 1 ≤ M ^ 2 := one_le_pow₀ hM1
      calc M = M * 1 := by ring
        _ ≤ M * M ^ 2 := mul_le_mul_of_nonneg_left this hM0.le
        _ = M ^ 3 := by ring
    have h6 : M * r ^ 3 ≤ (M * r) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hM3 (by positivity : (0 : ℝ) ≤ r ^ 3)
      calc M * r ^ 3 ≤ M ^ 3 * r ^ 3 := this
        _ = (M * r) ^ 3 := by ring
    linarith
  set δ := L * s * β with hδ
  have hδ0 : 0 < δ := by positivity
  have hδu : 2 * δ ≤ u := by
    have h5 : 2 * L * M ^ 2 * s * β ≤ w ^ 2 := by
      have h6 : 2 * L * M ^ 2 * s * β ≤ i * β := mul_le_mul_of_nonneg_right hreg hβ.le
      have e : (i : ℝ) * β = w ^ 2 := by
        rw [hiw]
        have : N * w ^ 3 * β = w ^ 2 * (N * β * w) := by ring
        rw [this, hNβw, mul_one]
      linarith
    have h6 : w ^ 2 ≤ M ^ 2 * u := by
      rw [← hru]
      have := pow_le_pow_left₀ hw0.le hwr 2
      calc w ^ 2 ≤ (M * r) ^ 2 := this
        _ = M ^ 2 * r ^ 2 := by ring
    have h7 : M ^ 2 * (2 * δ) ≤ M ^ 2 * u := by
      have : M ^ 2 * (2 * δ) = 2 * L * M ^ 2 * s * β := by rw [hδ]; ring
      linarith
    exact le_of_mul_le_mul_left h7 (by positivity)
  have hbig : 4 * s ≤ N * c₁ * r * δ := by
    have h5 : 1 ≤ M * (N * β * r) := by
      have : N * β * w ≤ N * β * (M * r) := mul_le_mul_of_nonneg_left hwr (by positivity)
      have e : N * β * (M * r) = M * (N * β * r) := by ring
      linarith
    have e : N * c₁ * r * δ = (L * c₁) * s * (N * β * r) := by rw [hδ]; ring
    rw [e, hL]
    have : 4 * s * 1 ≤ 4 * s * (M * (N * β * r)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    calc 4 * s = 4 * s * 1 := by ring
      _ ≤ 4 * s * (M * (N * β * r)) := this
      _ = 4 * M * s * (N * β * r) := by ring
  have hup : u - δ ≤ μ := by
    by_contra hc
    have hc' : μ < u - δ := lt_of_not_ge hc
    have hv0 : 0 ≤ u - δ := by linarith
    have hm := h2 _ hv0 (by linarith) hc'
    have hmass' := hlo (u - δ) u hv0 (by linarith) (by linarith)
    have hsq : r / 2 ≤ √(u - δ) := by
      rw [Real.le_sqrt (by positivity) hv0]
      have e : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
      rw [e, hru]
      linarith
    have hc2 := (abs_le.1 (hcount (u - δ) hv0 (by linarith))).2
    have h5 : N * c₁ * (r / 2) * δ ≤ N * c₁ * √(u - δ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ0.le
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : u - (u - δ) = δ := by ring
    rw [e] at hmass'
    have e2 : N * c₁ * (r / 2) * δ = (N * c₁ * r * δ) / 2 := by ring
    linarith
  have hlow : μ ≤ u + δ := by
    apply h1 _ (by linarith) (by linarith)
    have hmass' := hlo u (u + δ) hu.le (by linarith) (by linarith)
    rw [← hr] at hmass'
    have e : u + δ - u = δ := by ring
    rw [e] at hmass'
    have hc2 := (abs_le.1 (hcount (u + δ) (by linarith) (by linarith))).1
    linarith
  have hδE : δ ≤ E * β := by
    rw [hδ]; exact mul_le_mul_of_nonneg_right hA5 hβ.le
  rw [abs_le]
  constructor <;> linarith

/-- The inversion near a square-root edge, in the distance `v` from the edge: `Φ(v)` is the
classical mass between the edge and distance `v` (density between `c₁√v` and `c₂√v`), `m(v)`
a comparison count, `u` the distance of `γ` (with `Φ(u) = i − 1/2`), `μ` that of the compared
point. If `|m − Φ| ≤ s` on `[0, t]` and `μ ≥ −y²`, then `|μ − u| ≤ E β`, where
`β³ i N² = 1`. -/
private lemma rl_edge_core {N s y E β c₁ c₂ t u μ : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 1 ≤ s) (hy : 0 < y) (hc₁ : 0 < c₁) (hβ : 0 < β)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (hi : 1 ≤ i)
    (hu : 0 < u) (hut : u ≤ t / 2) (hYt : y ^ 2 ≤ t)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hhi : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → Φ v₂ - Φ v₁ ≤ N * c₂ * √v₂ * (v₂ - v₁))
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, 0 ≤ v → v ≤ t → (i : ℝ) + 1 ≤ m v → μ ≤ v)
    (h2 : ∀ v, 0 ≤ v → v ≤ t → μ < v → (i : ℝ) ≤ m v)
    (hexcl : -y ^ 2 ≤ μ)
    (hA2 : (rlK c₁ c₂ + 1) * s + 1 ≤ N * c₁ * y ^ 3 / 4)
    (hA3 : 128 * rlK c₁ c₂ ^ 3 * s ^ 3 ≤ c₁ ^ 2 * E ^ 3)
    (hA4 : 8 * rlK c₁ c₂ * s * y ^ 6 * N ^ 2 ≤ E ^ 3)
    (hA5 : rlL c₁ c₂ * s ≤ E) :
    |μ - u| ≤ E * β := by
  have hM1 : 1 ≤ rlM c₂ := le_max_left _ _
  have hM2 : 2 * c₂ ≤ rlM c₂ := le_max_right _ _
  have hM0 : 0 < rlM c₂ := by linarith
  have hL : rlL c₁ c₂ * c₁ = 4 * rlM c₂ := by unfold rlL; field_simp
  have hL0 : 0 < rlL c₁ c₂ := by unfold rlL; positivity
  have hK0 : 0 < rlK c₁ c₂ := by unfold rlK; positivity
  have hE0 : 0 ≤ E := le_trans (by positivity) hA5
  have hi0 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  by_cases hreg : (i : ℝ) < rlK c₁ c₂ * s
  · exact rl_core_small hN (by linarith) hy hc₁ hK0 hβ hE0 hβi hu (by linarith) hYt hΦ0 hΦu hlo
      hcount h1 hexcl hreg hA2 hA3 hA4
  · exact rl_core_big hN hs hc₁ hβ hM1 hM2 hL hL0 hβi hi0 hu hut hΦ0 hΦu hlo hhi hcount h1 h2
      (le_of_not_gt hreg) hA5

/-- `(x^a)^n = x^{a n}`. -/
private lemma rl_rpow_pow {x : ℝ} (hx : 0 < x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]

/-- The exponent rows of the edge inversion at `s = N^{ε₁}`, `y = N^{−1/3+ε₁/2}`, `E = N^ε`,
for `N` large. -/
private lemma rl_num {c₁ c₂ t ε ε₁ : ℝ} (hc₁ : 0 < c₁) (ht : 0 < t) (hε₁ : 0 < ε₁)
    (hε₁ε : 2 * ε₁ ≤ ε) (hε₁2 : ε₁ < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ (N : ℝ) ^ ε₁ ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 = (N : ℝ) ^ (-2 / 3 + ε₁) ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 ≤ t ∧
      (rlK c₁ c₂ + 1) * (N : ℝ) ^ ε₁ + 1 ≤
        N * c₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 / 4 ∧
      128 * rlK c₁ c₂ ^ 3 * ((N : ℝ) ^ ε₁) ^ 3 ≤ c₁ ^ 2 * ((N : ℝ) ^ ε) ^ 3 ∧
      8 * rlK c₁ c₂ * (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2 ≤
        ((N : ℝ) ^ ε) ^ 3 ∧
      rlL c₁ c₂ * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε := by
  have hK0 : 0 ≤ rlK c₁ c₂ := by
    unfold rlK rlL; have : 1 ≤ rlM c₂ := le_max_left _ _
    have : 0 < rlM c₂ := by linarith
    positivity
  obtain ⟨N₁, e1⟩ := rl_ev (1 / t) (a := -2 / 3 + ε₁) (b := 0) (by linarith)
  obtain ⟨N₂, e2⟩ := rl_ev (4 * (rlK c₁ c₂ + 2) / c₁) (a := ε₁) (b := 3 * ε₁ / 2) (by linarith)
  obtain ⟨N₃, e3⟩ := rl_ev (128 * rlK c₁ c₂ ^ 3 / c₁ ^ 2) (a := 3 * ε₁) (b := 3 * ε)
    (by linarith)
  obtain ⟨N₄, e4⟩ := rl_ev (8 * rlK c₁ c₂) (a := 4 * ε₁) (b := 3 * ε) (by linarith)
  obtain ⟨N₅, e5⟩ := rl_ev (rlL c₁ c₂) (a := ε₁) (b := ε) (by linarith)
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hN))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have f1 := e1 N (le_of_max_le_left (le_of_max_le_left hN))
  have f2 := e2 N (le_of_max_le_right (le_of_max_le_left hN))
  have f3 := e3 N (le_of_max_le_left (le_of_max_le_left (le_of_max_le_right hN)))
  have f4 := e4 N (le_of_max_le_right (le_of_max_le_left (le_of_max_le_right hN)))
  have f5 := e5 N (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hN)))
  have hs1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1r hε₁.le
  have hy2 : ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 = (N : ℝ) ^ (-2 / 3 + ε₁) := by
    rw [rl_rpow_pow hNr]; congr 1; push_cast; ring
  have hy3 : (N : ℝ) * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 = (N : ℝ) ^ (3 * ε₁ / 2) := by
    rw [rl_rpow_pow hNr]
    conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNr]; congr 1; push_cast; ring
  have hy6 : (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2 =
      (N : ℝ) ^ (4 * ε₁) := by
    rw [rl_rpow_pow hNr, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hNr,
      ← Real.rpow_add hNr]
    congr 1; push_cast; ring
  have hs3 : ((N : ℝ) ^ ε₁) ^ 3 = (N : ℝ) ^ (3 * ε₁) := by
    rw [rl_rpow_pow hNr]; congr 1; push_cast; ring
  have hE3 : ((N : ℝ) ^ ε) ^ 3 = (N : ℝ) ^ (3 * ε) := by
    rw [rl_rpow_pow hNr]; congr 1; push_cast; ring
  refine ⟨hs1, hy2, ?_, ?_, ?_, ?_, f5⟩
  · rw [hy2]
    rw [Real.rpow_zero] at f1
    have := mul_le_mul_of_nonneg_left f1 ht.le
    rw [← mul_assoc, mul_one_div_cancel ht.ne', one_mul, mul_one] at this
    exact this
  · have h5 : N * c₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 / 4 =
        c₁ / 4 * (N : ℝ) ^ (3 * ε₁ / 2) := by rw [← hy3]; ring
    rw [h5]
    have h6 : c₁ / 4 * (4 * (rlK c₁ c₂ + 2) / c₁ * (N : ℝ) ^ ε₁) =
        (rlK c₁ c₂ + 2) * (N : ℝ) ^ ε₁ := by field_simp
    have h7 := mul_le_mul_of_nonneg_left f2 (by positivity : (0 : ℝ) ≤ c₁ / 4)
    rw [h6] at h7
    nlinarith
  · rw [hs3, hE3]
    have h7 := mul_le_mul_of_nonneg_left f3 (by positivity : (0 : ℝ) ≤ c₁ ^ 2)
    have h6 : c₁ ^ 2 * (128 * rlK c₁ c₂ ^ 3 / c₁ ^ 2 * (N : ℝ) ^ (3 * ε₁)) =
        128 * rlK c₁ c₂ ^ 3 * (N : ℝ) ^ (3 * ε₁) := by field_simp
    rw [h6] at h7
    exact h7
  · have e : 8 * rlK c₁ c₂ * (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 *
        (N : ℝ) ^ 2 = 8 * rlK c₁ c₂ * ((N : ℝ) ^ ε₁ *
          ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2) := by ring
    rw [e, hy6, hE3]
    exact f4

/-- `N^ε i₀^{−1/3} N^{−2/3} ≤ N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}` when
`1 ≤ i ∧ (N_k + 1 − i) ≤ i₀`. -/
private lemma rl_rig_le {Nk i i₀ : ℕ} {ε : ℝ} (h1 : 1 ≤ min i (Nk + 1 - i))
    (h2 : min i (Nk + 1 - i) ≤ i₀) :
    (N : ℝ) ^ ε * (i₀ : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hm : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have := Real.rpow_le_rpow_of_nonpos hm
    (by exact_mod_cast h2 : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ (i₀ : ℝ))
    (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) h3

/-- `rigBound N N_k i ε ≤ N^ε (c x)^{−1/3} N^{−2/3}` when `0 < c x ≤ i ∧ (N_k + 1 − i)`. -/
private lemma rl_rig_ge {Nk i : ℕ} {ε c x : ℝ} (hcx : 0 < c * x)
    (h : c * x ≤ ((min i (Nk + 1 - i) : ℕ) : ℝ)) :
    rigBound N Nk i ε ≤ (N : ℝ) ^ ε * (c * x) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  unfold rigBound
  have := Real.rpow_le_rpow_of_nonpos hcx h (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) h3

/-- `β = i^{−1/3} N^{−2/3}` satisfies `β > 0` and `β³ i N² = 1`. -/
private lemma rl_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ)) ∧
      (a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ))) ^ 3 * a * b ^ 2 = 1 := by
  refine ⟨by positivity, ?_⟩
  have e1 : (a ^ (-(1 / 3 : ℝ))) ^ 3 = a⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
    exact Real.rpow_neg_one a
  have e2 : (b ^ (-(2 / 3 : ℝ))) ^ 3 = (b ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num
  rw [mul_pow, e1, e2]
  field_simp

/-! ## The density and the support near a regular edge -/

/-- The lower constant `1/(π √C₂(τ))` of the square-root density. -/
private def rlC1 (τ : ℝ) : ℝ := 1 / (Real.pi * √(edgeC2 τ))

/-- The upper constant `2/(π √c₂(τ))` of the square-root density. -/
private def rlC2 (τ : ℝ) : ℝ := 2 / (Real.pi * √(edgec2 τ))

private lemma rl_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeC2 τ ∧ 0 < edgec2 τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  refine ⟨by unfold edgeC2 edgeCx; positivity, by unfold edgec2 edgeCx; positivity⟩

private lemma rl_C1_pos {τ : ℝ} (hτ : 0 < τ) : 0 < rlC1 τ := by
  have := (rl_C_pos hτ).1; unfold rlC1; positivity

private lemma rl_C2_pos {τ : ℝ} (hτ : 0 < τ) : 0 < rlC2 τ := by
  have := (rl_C_pos hτ).2; unfold rlC2; positivity

/-- `c₁ √d ≤ ρ ≤ c₂ √d` on the band side of a regular edge, `d` the distance to the edge
(proof of Lemma A.4). -/
private lemma rl_rho_edge {τ : ℝ} {σ : Fin M → ℝ} {l : ℕ} (hda : DensityAssumptions τ N σ)
    (hl : RegularEdge τ N σ l) {x : ℝ} (hx : |x - edgeVal N σ l| ≤ edgeTau0 τ)
    (hside : (-1 : ℝ) ^ (l + 1) * (x - edgeVal N σ l) ≤ 0) :
    rlC1 τ * √|x - edgeVal N σ l| ≤ rhoDens N σ x ∧
      rhoDens N σ x ≤ rlC2 τ * √|x - edgeVal N σ l| := by
  obtain ⟨h1, h2⟩ := (rhoDens_edge hda hl hx).1 hside
  obtain ⟨hC2, hc2⟩ := rl_C_pos hda.pos
  rw [Real.sqrt_div' _ hC2.le] at h1
  rw [Real.sqrt_div' _ hc2.le] at h2
  have hπ := Real.pi_pos
  have hsC := Real.sqrt_pos.2 hC2
  have hsc := Real.sqrt_pos.2 hc2
  set d := √|x - edgeVal N σ l|
  constructor
  · have e : rlC1 τ * d = d / √(edgeC2 τ) / Real.pi := by unfold rlC1; field_simp
    rw [e, div_le_iff₀ hπ]
    linarith
  · have e : rlC2 τ * d = 2 * (d / √(edgec2 τ)) / Real.pi := by unfold rlC2; field_simp
    rw [e, le_div_iff₀ hπ]
    linarith

/-- The mass bounds below an upper edge `a`: if `c √(a − x) ≤ ρ(x)` on `[a − t, a]`, then
`n(a − v₂) − n(a − v₁) ≥ N c √v₁ (v₂ − v₁)` for `0 ≤ v₁ ≤ v₂ ≤ t`. -/
private lemma rl_lo_up {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (hat : t < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a - t ≤ x → x ≤ a → c * √(a - x) ≤ rhoDens N σ x) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c * √v₁ * (v₂ - v₁) ≤
      (nClass N σ (a - v₂) - nClass N σ a) - (nClass N σ (a - v₁) - nClass N σ a) := by
  intro v₁ v₂ h0 h12 h2t
  have := rl_nClass_sub_ge (N := N) hσ hN (x := a - v₂) (y := a - v₁) (c₀ := c * √v₁)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.2])) hc)
        (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
  have e : a - v₁ - (a - v₂) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The upper mass bound below an upper edge `a` (density `≤ c √(a − x)`). -/
private lemma rl_hi_up {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (hat : t < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a - t ≤ x → x ≤ a → rhoDens N σ x ≤ c * √(a - x)) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t →
      (nClass N σ (a - v₂) - nClass N σ a) - (nClass N σ (a - v₁) - nClass N σ a) ≤
        N * c * √v₂ * (v₂ - v₁) := by
  intro v₁ v₂ h0 h12 h2t
  have := rl_nClass_sub_le (N := N) hσ hN (x := a - v₂) (y := a - v₁) (c₀ := c * √v₂)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.1])) hc)
  have e : a - v₁ - (a - v₂) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The mass bounds above a lower edge `a` (density `≥ c √(x − a)` on `[a, a + t]`). -/
private lemma rl_lo_dn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a ≤ x → x ≤ a + t → c * √(x - a) ≤ rhoDens N σ x) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c * √v₁ * (v₂ - v₁) ≤
      (nClass N σ a - nClass N σ (a + v₂)) - (nClass N σ a - nClass N σ (a + v₁)) := by
  intro v₁ v₂ h0 h12 h2t
  have := rl_nClass_sub_ge (N := N) hσ hN (x := a + v₁) (y := a + v₂) (c₀ := c * √v₁)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.1])) hc)
        (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
  have e : a + v₂ - (a + v₁) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The upper mass bound above a lower edge `a` (density `≤ c √(x − a)`). -/
private lemma rl_hi_dn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a ≤ x → x ≤ a + t → rhoDens N σ x ≤ c * √(x - a)) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t →
      (nClass N σ a - nClass N σ (a + v₂)) - (nClass N σ a - nClass N σ (a + v₁)) ≤
        N * c * √v₂ * (v₂ - v₁) := by
  intro v₁ v₂ h0 h12 h2t
  have := rl_nClass_sub_le (N := N) hσ hN (x := a + v₁) (y := a + v₂) (c₀ := c * √v₂)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.2])) hc)
  have e : a + v₂ - (a + v₁) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma rl_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  rw [heq]
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  nlinarith

/-- `0 < τ'(τ)`, `τ₀(τ) = 4 τ'(τ)` and `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma rl_tau_facts {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgeTau' τ ∧ edgeTau0 τ = 4 * edgeTau' τ ∧ edgeTau' τ ≤ τ / 2 := by
  refine ⟨edgeTau'_pos hτ, by unfold edgeTau'; ring, rl_edgeTau'_le hτ hτ1⟩

/-- A positive point of `supp ϱ` lies in a band `[a_{2k}, a_{2k−1}]`, `1 ≤ k ≤ p`. -/
private lemma rl_supp {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) (hy0 : 0 < y) :
    ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ edgeVal N σ (2 * k) ≤ y ∧ y ≤ edgeVal N σ (2 * k - 1) := by
  obtain ⟨hN, -, hS⟩ := rl_facts h
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ h.nonneg hN hS hy0).1 hy
  exact ⟨k, hk1, hk2, hyk.1, hyk.2⟩

/-- A point of a band `[a_{2k}, a_{2k−1}]` with `0 < y` lies in `supp ϱ`. -/
private lemma rl_mem_supp {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {y : ℝ} (hy0 : 0 < y)
    (hy1 : edgeVal N σ (2 * k) ≤ y) (hy2 : y ≤ edgeVal N σ (2 * k - 1)) :
    y ∈ (varrho N σ).support := by
  obtain ⟨hN, -, hS⟩ := rl_facts h
  exact (mem_support_varrho_iff N σ h.nonneg hN hS hy0).2 ⟨k, hk, hkp, hy1, hy2⟩

/-- A point `x ≥ r` at distance `≥ r` from every band is at distance `≥ r` from `supp ϱ`. -/
private lemma rl_dist {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {x r : ℝ}
    (hr : 0 ≤ r) (hx : r ≤ x) (hne : (varrho N σ).support.Nonempty)
    (h : ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x) :
    r ≤ Metric.infDist x (varrho N σ).support := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [Real.dist_eq]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨l, hl1, hl2, hyl1, hyl2⟩ := rl_supp hda hy hy0
  rcases h l hl1 hl2 with h' | h'
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- `τ₀(τ) ≤ τ/16` for `τ ∈ (0, 1]`. -/
private lemma rl_tau0_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau0 τ ≤ τ / 16 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  unfold edgeTau0
  nlinarith

/-- `a_{2k−2} ≥ a_{2k−1} + τ` when the edge `2k − 1` is regular at `τ`, `k ≥ 2`. -/
private lemma rl_sep_up {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 2 ≤ k) (hreg : RegularEdge τ N σ (2 * k - 1)) :
    edgeVal N σ (2 * k - 1) + τ ≤ edgeVal N σ (2 * k - 2) := by
  have hkp := hreg.2.1
  have h1 := hreg.2.2.2.1 (2 * k - 2) (by omega) (by omega) (by omega)
  have h2 := rl_anti hda (i := 2 * k - 2) (j := 2 * k - 1) (by omega) (by omega) hkp
  rw [abs_of_nonpos (by linarith)] at h1
  linarith

/-- `a_{2k+1} + τ ≤ a_{2k}` when the edge `2k` is regular at `τ`, `k < p`. -/
private lemma rl_sep_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) (hreg : RegularEdge τ N σ (2 * k)) :
    edgeVal N σ (2 * k + 1) + τ ≤ edgeVal N σ (2 * k) := by
  have h1 := hreg.2.2.2.1 (2 * k + 1) (by omega) (by omega) (by omega)
  have h2 := rl_anti hda (i := 2 * k) (j := 2 * k + 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonneg (by linarith)] at h1
  linarith

/-- `a_{2k} + τ ≤ a_{2k−1}` when one of the two edges of the band `k` is regular at `τ`. -/
private lemma rl_band_wide {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (hreg : RegularEdge τ N σ (2 * k) ∨ RegularEdge τ N σ (2 * k - 1)) :
    edgeVal N σ (2 * k) + τ ≤ edgeVal N σ (2 * k - 1) := by
  have h2 := rl_anti hda (i := 2 * k - 1) (j := 2 * k) (by omega) (by omega) (by omega)
  rcases hreg with h | h
  · have h1 := h.2.2.2.1 (2 * k - 1) (by omega) (by omega) (by omega)
    rw [abs_of_nonpos (by linarith)] at h1
    linarith
  · have h1 := h.2.2.2.1 (2 * k) (by omega) (by omega) (by omega)
    rw [abs_of_nonneg (by linarith)] at h1
    linarith

/-- `x_{2k} < 0` for a band `k < p`, and for `k = p` when `R = #{σ_i > 0}/N < 1`. -/
private lemma rl_xCrit_neg {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hcase : k < numBands N σ ∨ massRatio N σ < 1) :
    xCrit N σ (2 * k) < 0 := by
  obtain ⟨hN, -, hS⟩ := rl_facts hda
  have hσ := hda.nonneg
  have hp := card_innerCrit N σ hσ hN hS
  by_cases hkl : k < numBands N σ
  · have hne : 2 * k ≠ 2 * numBands N σ := by omega
    unfold xCrit
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
    have hlen : ((innerCrit N σ).sort (· ≤ ·)).reverse.length = Multiset.card (innerCrit N σ) := by
      rw [List.length_reverse, Multiset.length_sort]
    have hidx : 2 * k - 1 < ((innerCrit N σ).sort (· ≤ ·)).reverse.length := by
      rw [hlen]; omega
    rw [List.getD_eq_getElem _ _ hidx]
    have hmem := List.getElem_mem hidx
    rw [List.mem_reverse, Multiset.mem_sort] at hmem
    exact (Multiset.mem_filter.1 hmem).2.1
  · have hk' : k = numBands N σ := by omega
    have hmr : massRatio N σ < 1 := hcase.resolve_left hkl
    unfold xCrit
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 2 * k = 2 * numBands N σ by omega))]
    obtain ⟨-, hF⟩ := yEdge_spec N σ hσ hN hS
    rw [inv_lt_zero]
    by_contra hy
    push Not at hy
    have hle : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (yEdge N σ + s) ^ 2 ≤
        ∑ s ∈ posVals σ, weight N σ s := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hs0 : 0 < s := (Finset.mem_filter.1 hs).2
      have hw : 0 ≤ weight N σ s := by unfold weight; positivity
      have h1 : s ^ 2 ≤ (yEdge N σ + s) ^ 2 := by nlinarith
      rw [mul_div_assoc]
      calc weight N σ s * (s ^ 2 / (yEdge N σ + s) ^ 2) ≤ weight N σ s * 1 :=
            mul_le_mul_of_nonneg_left (div_le_one_of_le₀ h1 (sq_nonneg _)) hw
        _ = weight N σ s := mul_one _
    have hsw := sum_weight N σ
    unfold FChart1 at hF
    linarith

/-- The band of `N − 1` containing a point `E` near an edge `a` of `N`: if the edge `l'` of
`N − 1` lies within `r'` of `a`, is regular at `τ₁`, and `|E − a| ≤ r`, `r + r' < τ₁`, then an
odd `l'` is the upper edge `2l − 1` and an even `l'` the lower edge `2l` of that band `l`. -/
private lemma rl_partner {τ₁ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ K σ)
    {l l' : ℕ} (hl : 1 ≤ l) (hlp : l ≤ numBands K σ) (hreg : RegularEdge τ₁ K σ l')
    {E a r r' : ℝ} (hE1 : edgeVal K σ (2 * l) < E) (hE2 : E < edgeVal K σ (2 * l - 1))
    (hEa : |E - a| ≤ r) (hpa : |edgeVal K σ l' - a| ≤ r') (hsmall : r + r' < τ₁) :
    (l' % 2 = 1 → l' = 2 * l - 1) ∧ (l' % 2 = 0 → l' = 2 * l) := by
  obtain ⟨hl1, hl2, -, hsep, -⟩ := hreg
  have hd : |E - edgeVal K σ l'| < τ₁ := by
    have := abs_sub_le E a (edgeVal K σ l')
    rw [abs_sub_comm a] at this
    linarith
  rw [abs_lt] at hd
  constructor
  · intro hodd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := rl_anti hda (i := l') (j := 2 * l - 1) hl1 hlt.le (by omega)
      have h2 := hsep (2 * l - 1) (by omega) (by omega) (by omega)
      rw [abs_of_nonneg (by linarith)] at h2
      linarith
    · have h1 := rl_anti hda (i := 2 * l) (j := l') (by omega) (by omega) hl2
      have h2 := hsep (2 * l) (by omega) (by omega) (by omega)
      rw [abs_of_nonpos (by linarith)] at h2
      linarith
  · intro heven
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := rl_anti hda (i := l') (j := 2 * l - 1) hl1 (by omega) (by omega)
      have h2 := hsep (2 * l - 1) (by omega) (by omega) (by omega)
      rw [abs_of_nonneg (by linarith)] at h2
      linarith
    · have h1 := rl_anti hda (i := 2 * l) (j := l') (by omega) hgt.le hl2
      have h2 := hsep (2 * l) (by omega) (by omega) (by omega)
      rw [abs_of_nonpos (by linarith)] at h2
      linarith

/-- In the gap above the band `k` (between `a_{2k−1}` and `a_{2k−2}`, or above `a_1`):
`n(x) = d_{k−1}`. -/
private lemma rl_n_gap_up {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx1 : edgeVal N σ (2 * k - 1) ≤ x)
    (hx2 : 2 ≤ k → x ≤ edgeVal N σ (2 * k - 2)) : nClass N σ x = cumCount N σ (k - 1) := by
  obtain ⟨hN, -, hS⟩ := rl_facts hda
  have hσ := hda.nonneg
  have hna := (nClass_edgeVal hda hk hkp).1
  have hup := rl_nClass_anti hσ hN hx1
  rcases lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    rw [rl_cum_zero] at hna ⊢
    have := rl_nClass_nonneg (N := N) σ x
    push_cast at hna ⊢
    linarith
  · have hb := edgeVal_band_lt N σ hσ hN hS hk hkp
    have h0 := (rl_edge_mem hda (k := 2 * k) (by omega) (by omega)).1
    have hpos : 0 < edgeVal N σ (2 * (k - 1)) := by
      rw [show 2 * (k - 1) = 2 * k - 2 by omega]; linarith [hx2 hk2]
    have hnb := (nClass_edgeVal hda (k := k - 1) (by omega) (by omega)).2 hpos
    rw [show 2 * (k - 1) = 2 * k - 2 by omega] at hnb
    have hlo := rl_nClass_anti hσ hN (hx2 hk2)
    linarith

/-- In the gap below the band `k` (between `a_{2k+1}` and `a_{2k}`, or in `(0, a_{2p}]`):
`n(x) = d_k`. -/
private lemma rl_n_gap_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσp : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ edgeVal N σ (2 * k)) (hx2 : k < numBands N σ → edgeVal N σ (2 * k + 1) ≤ x) :
    nClass N σ x = cumCount N σ k := by
  obtain ⟨hN, hM, hS⟩ := rl_facts hda
  have hσ := hda.nonneg
  have hna := (nClass_edgeVal hda hk hkp).2 (by linarith)
  have hlo := rl_nClass_anti hσ hN hx1
  rcases lt_or_eq_of_le hkp with hlt | heq
  · have hnb := (nClass_edgeVal hda (k := k + 1) (by omega) (by omega)).1
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega] at hnb
    have hup := rl_nClass_anti hσ hN (hx2 hlt)
    linarith
  · have hcp := (rl_cum hda hσp hk hkp).2
    rw [← heq] at hcp
    have hz := (Ni_sum N σ hσp hN hM).1
    have := isProbabilityMeasure_varrho N σ hσ hN
    have hdisj : Disjoint ({0} : Set ℝ) (Set.Ici x) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      rw [Set.mem_singleton_iff] at ht1
      rw [ht1, Set.mem_Ici] at ht2
      linarith
    have hsum : varrho N σ {0} + varrho N σ (Set.Ici x) ≤ 1 := by
      rw [← measure_union hdisj measurableSet_Ici]
      exact prob_le_one
    have hsum' : (varrho N σ {0}).toReal + (varrho N σ (Set.Ici x)).toReal ≤ 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      have := ENNReal.toReal_mono ENNReal.one_ne_top hsum
      simpa using this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hmul := mul_le_mul_of_nonneg_left hsum' hN0
    have hle : nClass N σ x ≤ (min M N : ℕ) := by
      unfold nClass
      rw [Nat.cast_min]
      rcases le_total M N with hMN | hMN
      · rw [min_eq_left (by exact_mod_cast hMN)]
        rw [max_eq_left (by have : (M : ℝ) ≤ N := by exact_mod_cast hMN
                            linarith)] at hz
        nlinarith
      · rw [min_eq_right (by exact_mod_cast hMN)]
        have : 0 ≤ (varrho N σ {0}).toReal := ENNReal.toReal_nonneg
        nlinarith
    rw [hcp] at hna ⊢
    linarith

/-- The index facts at `N − 1`: for `1 ≤ l ≤ ṗ`, `1 ≤ i ≤ Ṅ_l`, `j = ḋ_{l−1} + i` lies in
`[1, M ∧ (N − 1)]`, `ṅ(γ̇_j) = j − 1/2`, `γ̇_j ∈ (ȧ_{2l}, ȧ_{2l−1})`, `ḋ_{l−1} = ṅ(ȧ_{2l−1})`,
and `j ≤ ḋ_l`. -/
private lemma rl_dot_idx {τ₁ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ K σ)
    (hσ : ∀ j, 0 < σ j) {l i : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ numBands K σ) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat K σ l) :
    1 ≤ cumCount K σ (l - 1) + i ∧ cumCount K σ (l - 1) + i ≤ min M K ∧
      nClass K σ (gammaLoc K σ (cumCount K σ (l - 1) + i)) =
        ((cumCount K σ (l - 1) + i : ℕ) : ℝ) - 1 / 2 ∧
      edgeVal K σ (2 * l) < gammaLoc K σ (cumCount K σ (l - 1) + i) ∧
      gammaLoc K σ (cumCount K σ (l - 1) + i) < edgeVal K σ (2 * l - 1) ∧
      nClass K σ (edgeVal K σ (2 * l - 1)) = cumCount K σ (l - 1) ∧
      cumCount K σ (l - 1) + i ≤ cumCount K σ l := by
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hl1 hlp
  have hcl := (rl_cum hda hσ hl1 hlp).1
  have hj1 : 1 ≤ cumCount K σ (l - 1) + i := by omega
  have hjM : cumCount K σ (l - 1) + i ≤ min M K := by omega
  obtain ⟨-, hn⟩ := nClass_gammaLoc hda hσ hj1 hjM
  have hmem := gammaBand_mem hda hσ hl1 hlp hi hiN
  exact ⟨hj1, hjM, hn, hmem.1, hmem.2, (nClass_edgeVal hda hl1 hlp).1, by omega⟩

/-- `rigBound` is monotone in `ε` for `N ≥ 1`. -/
private lemma rl_rigBound_mono {Nk i : ℕ} {ε ε' : ℝ} (hN : 1 ≤ N) (h : ε' ≤ ε) :
    rigBound N Nk i ε' ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have := Real.rpow_le_rpow_of_exponent_le hN1 h
  have h0 : (0 : ℝ) ≤ ((min i (Nk + 1 - i) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h0) h3

/-! ## Comparison of a point with a classical location near a regular edge -/

/-- Below an upper edge `a = a_{2k−1}` regular at `τ`: a point `E` and a classical location `γ`
with `n(γ) − n(a) = ι − 1/2`, compared through a count `m` within `s` of the classical mass on
`[a − τ₀(τ), a]`, satisfy `|γ − E| ≤ E_c ι^{−1/3} N^{−2/3}`. -/
private lemma rl_cmp_up {τ s y Ec : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hτ1 : τ ≤ 1) {k : ℕ} (hk : 1 ≤ k) (hreg : RegularEdge τ N σ (2 * k - 1)) {ι : ℕ}
    (hι : 1 ≤ ι) {γ E : ℝ}
    (hγ : nClass N σ γ - nClass N σ (edgeVal N σ (2 * k - 1)) = (ι : ℝ) - 1 / 2)
    (hγa : γ < edgeVal N σ (2 * k - 1))
    (hγt : edgeVal N σ (2 * k - 1) - edgeTau0 τ / 2 ≤ γ) (m : ℝ → ℝ)
    (hcount : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → |m v - (nClass N σ (edgeVal N σ (2 * k - 1) - v) -
      nClass N σ (edgeVal N σ (2 * k - 1)))| ≤ s)
    (h1 : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → (ι : ℝ) + 1 ≤ m v → edgeVal N σ (2 * k - 1) - E ≤ v)
    (h2 : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → edgeVal N σ (2 * k - 1) - E < v → (ι : ℝ) ≤ m v)
    (hexcl : E ≤ edgeVal N σ (2 * k - 1) + y ^ 2)
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau0 τ)
    (hA2 : (rlK (rlC1 τ) (rlC2 τ) + 1) * s + 1 ≤ N * rlC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rlK (rlC1 τ) (rlC2 τ) ^ 3 * s ^ 3 ≤ rlC1 τ ^ 2 * Ec ^ 3)
    (hA4 : 8 * rlK (rlC1 τ) (rlC2 τ) * s * y ^ 6 * N ^ 2 ≤ Ec ^ 3)
    (hA5 : rlL (rlC1 τ) (rlC2 τ) * s ≤ Ec) :
    |γ - E| ≤ Ec * ((ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτ := hda.pos
  set a := edgeVal N σ (2 * k - 1) with ha
  have haτ : τ ≤ a := hreg.2.2.1
  have ht0 := rl_tau0_le hτ hτ1
  obtain ⟨ht'0, ht0e, -⟩ := rl_tau_facts hτ hτ1
  have hρ : ∀ x, a - edgeTau0 τ ≤ x → x ≤ a →
      rlC1 τ * √(a - x) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rlC2 τ * √(a - x) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k - 1 + 1) * (x - a) ≤ 0 := by
      rw [show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num; linarith
    have := rl_rho_edge hda hreg hx hside
    rwa [abs_of_nonpos (by linarith), neg_sub] at this
  obtain ⟨hβ, hβi⟩ := rl_beta (a := (ι : ℝ)) (b := (N : ℝ)) (by exact_mod_cast hι) hNr
  have key := rl_edge_core (N := (N : ℝ)) (i := ι) (t := edgeTau0 τ)
    (Φ := fun v => nClass N σ (a - v) - nClass N σ a) (m := m)
    (u := a - γ) (μ := a - E) hNr hs hy (rl_C1_pos hτ) hβ hβi hι
    (by linarith) (by linarith) hYt (by simp)
    (by simp only [sub_sub_cancel]; exact hγ)
    (rl_lo_up hda.nonneg hN0 (by linarith) (rl_C1_pos hτ).le fun x h1 h2 => (hρ x h1 h2).1)
    (rl_hi_up hda.nonneg hN0 (by linarith) (rl_C2_pos hτ).le fun x h1 h2 => (hρ x h1 h2).2)
    hcount h1 h2 (by linarith) hA2 hA3 hA4 hA5
  rw [show a - E - (a - γ) = γ - E by ring] at key
  exact key

/-- Above a lower edge `a = a_{2k}` regular at `τ`: a point `E` and a classical location `γ`
with `n(a) − n(γ) = ι − 1/2`, compared through a count `m` within `s` of the classical mass on
`[a, a + τ₀(τ)]`, satisfy `|γ − E| ≤ E_c ι^{−1/3} N^{−2/3}`. -/
private lemma rl_cmp_dn {τ s y Ec : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    {k : ℕ} (hreg : RegularEdge τ N σ (2 * k)) {ι : ℕ}
    (hι : 1 ≤ ι) {γ E : ℝ}
    (hγ : nClass N σ (edgeVal N σ (2 * k)) - nClass N σ γ = (ι : ℝ) - 1 / 2)
    (hγa : edgeVal N σ (2 * k) < γ)
    (hγt : γ ≤ edgeVal N σ (2 * k) + edgeTau0 τ / 2) (m : ℝ → ℝ)
    (hcount : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → |m v - (nClass N σ (edgeVal N σ (2 * k)) -
      nClass N σ (edgeVal N σ (2 * k) + v))| ≤ s)
    (h1 : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → (ι : ℝ) + 1 ≤ m v → E - edgeVal N σ (2 * k) ≤ v)
    (h2 : ∀ v, 0 ≤ v → v ≤ edgeTau0 τ → E - edgeVal N σ (2 * k) < v → (ι : ℝ) ≤ m v)
    (hexcl : edgeVal N σ (2 * k) - y ^ 2 ≤ E)
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau0 τ)
    (hA2 : (rlK (rlC1 τ) (rlC2 τ) + 1) * s + 1 ≤ N * rlC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rlK (rlC1 τ) (rlC2 τ) ^ 3 * s ^ 3 ≤ rlC1 τ ^ 2 * Ec ^ 3)
    (hA4 : 8 * rlK (rlC1 τ) (rlC2 τ) * s * y ^ 6 * N ^ 2 ≤ Ec ^ 3)
    (hA5 : rlL (rlC1 τ) (rlC2 τ) * s ≤ Ec) :
    |γ - E| ≤ Ec * ((ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτ := hda.pos
  set a := edgeVal N σ (2 * k) with ha
  have haτ : τ ≤ a := hreg.2.2.1
  have hρ : ∀ x, a ≤ x → x ≤ a + edgeTau0 τ →
      rlC1 τ * √(x - a) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rlC2 τ * √(x - a) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k + 1) * (x - a) ≤ 0 := by
      rw [pow_succ, pow_mul]; norm_num; linarith
    have := rl_rho_edge hda hreg hx hside
    rwa [abs_of_nonneg (by linarith)] at this
  obtain ⟨hβ, hβi⟩ := rl_beta (a := (ι : ℝ)) (b := (N : ℝ)) (by exact_mod_cast hι) hNr
  have key := rl_edge_core (N := (N : ℝ)) (i := ι) (t := edgeTau0 τ)
    (Φ := fun v => nClass N σ a - nClass N σ (a + v)) (m := m)
    (u := γ - a) (μ := E - a) hNr hs hy (rl_C1_pos hτ) hβ hβi hι
    (by linarith) (by linarith) hYt (by simp)
    (by simp only [add_sub_cancel]; exact hγ)
    (rl_lo_dn hda.nonneg hN0 (by linarith) (rl_C1_pos hτ).le fun x h1 h2 => (hρ x h1 h2).1)
    (rl_hi_dn hda.nonneg hN0 (by linarith) (rl_C2_pos hτ).le fun x h1 h2 => (hρ x h1 h2).2)
    hcount h1 h2 (by linarith) hA2 hA3 hA4 hA5
  rw [show E - a - (γ - a) = -(γ - E) by ring, abs_neg] at key
  exact key

/-! ## The edge piece at one index -/

/-- `N⁻¹ ≤ β ≤ N^{−2/3}` for `β = ι^{−1/3} N^{−2/3}`, `1 ≤ ι ≤ N`. -/
private lemma rl_beta_bounds {ι : ℕ} (hι : 1 ≤ ι) (hιN : ι ≤ N) :
    0 < (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ∧
      (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) ∧
      (N : ℝ)⁻¹ ≤ (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hι1 : (1 : ℝ) ≤ ι := by exact_mod_cast hι
  have hNι : (ι : ℝ) ≤ N := by exact_mod_cast hιN
  have hN0 : (0 : ℝ) < N := by linarith
  have h2 : (0 : ℝ) < (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · have : (ι : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hι1 (by norm_num)
    nlinarith
  · have e : (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hN0, show -(1 / 3 : ℝ) + -(2 / 3) = -1 by norm_num, Real.rpow_neg_one]
    rw [e]
    have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < ι) hNι
      (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    exact mul_le_mul_of_nonneg_right this h2.le

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- The upper edge `a_{2k−1}` of the band `k` at one index of `N − 1`, on the rigidity event of
Theorem 3.14 (iii) at `N`: interlacing, the classical comparison and the index alignment
`ḋ_{l−1} ≥ d_{k−1}` give `|λ̇_{l,i} − γ̇_{l,i}| ≤ rigBound N Ṅ_l i ε`. -/
private lemma rl_edge_up_det {τ ε ε₁ δ s y Ec : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hda : DensityAssumptions τ N (specOf Sig))
    (hσ : ∀ j, 0 < specOf Sig j) (hSig : Sig.IsHermitian) (hN2 : 2 ≤ N) (hτ1 : τ ≤ 1)
    (hk : 1 ≤ k) (hkp : k ≤ numBands N (specOf Sig))
    (hreg : RegularEdge τ N (specOf Sig) (2 * k - 1))
    (hsub : ∀ x, τ / 2 ≤ x →
      |nClass (N - 1) (specOf Sig) x - nClass N (specOf Sig) x| ≤ (N : ℝ) ^ δ)
    (hgap : nClass (N - 1) (specOf Sig) (edgeVal N (specOf Sig) (2 * k - 1) + τ / 2) =
      nClass N (specOf Sig) (edgeVal N (specOf Sig) (2 * k - 1) + τ / 2))
    (hpart : ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) → ∀ x,
      edgeVal (N - 1) (specOf Sig) (2 * l) < x → x < edgeVal (N - 1) (specOf Sig) (2 * l - 1) →
      |x - edgeVal N (specOf Sig) (2 * k - 1)| ≤ edgeTau0 τ / 16 →
      edgeVal (N - 1) (specOf Sig) (2 * l - 1) ≤ edgeVal N (specOf Sig) (2 * k - 1) + y ^ 2)
    (hω : ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k →
      gammaBand N (specOf Sig) k i ∈
        Set.Icc (edgeVal N (specOf Sig) (2 * k - 1) - edgeTau' τ / 2)
          (edgeVal N (specOf Sig) (2 * k - 1) + edgeTau' τ / 2) →
      |lamBand Sig Xm k i - gammaBand N (specOf Sig) k i| ≤
        rigBound N (bandNat N (specOf Sig) k) i ε₁)
    (hmass : (N : ℝ) ^ δ + 2 ≤ N * (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)))
    (hsδ : (N : ℝ) ^ δ + 3 / 2 ≤ s) (hs1 : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau0 τ)
    (hA2 : (rlK (rlC1 τ) (rlC2 τ) + 1) * s + 1 ≤ N * rlC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rlK (rlC1 τ) (rlC2 τ) ^ 3 * s ^ 3 ≤ rlC1 τ ^ 2 * Ec ^ 3)
    (hA4 : 8 * rlK (rlC1 τ) (rlC2 τ) * s * y ^ 6 * N ^ 2 ≤ Ec ^ 3)
    (hA5 : rlL (rlC1 τ) (rlC2 τ) * s ≤ Ec)
    (hfin : Ec + (N : ℝ) ^ ε₁ *
        (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) +
        2 * (2 * τ⁻¹ * (1 + τ⁻¹) + 1) ≤ (N : ℝ) ^ ε)
    (hsmall : (N : ℝ) ^ ε * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ τ / 4)
    {l i : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ numBands (N - 1) (specOf Sig)) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat (N - 1) (specOf Sig) l)
    (hE : gammaBand (N - 1) (specOf Sig) l i ∈
      Set.Icc (edgeVal N (specOf Sig) (2 * k - 1) - edgeTau' τ / 4)
        (edgeVal N (specOf Sig) (2 * k - 1) + edgeTau' τ / 4)) :
    |lamDotBand Sig Xm l i - gammaBand (N - 1) (specOf Sig) l i| ≤
      rigBound N (bandNat (N - 1) (specOf Sig) l) i ε := by
  have hτ := hda.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨ht'0, ht0e, -⟩ := rl_tau_facts hτ hτ1
  have ht0 := rl_tau0_le hτ hτ1
  have ht0p : 0 < edgeTau0 τ := by linarith
  set σ := specOf Sig with hσdef
  have hdaN1 := rl_da_pred hda hN2
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  have hN10 : 0 < N - 1 := by omega
  set t₀ := edgeTau0 τ with ht₀
  set a := edgeVal N σ (2 * k - 1) with ha
  have haτ : τ ≤ a := hreg.2.2.1
  have haC := (rl_edge_mem hda (k := 2 * k - 1) (by omega) (by omega)).2
  rw [← ha] at haC
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  set cf := rlC1 τ * √(t₀ / 16) * (t₀ / 16) with hcf
  have hcf0 : 0 < cf := by have := rl_C1_pos hτ; rw [hcf]; positivity
  set cs := min cf (1 / 2) with hcs
  have hcs0 : 0 < cs := lt_min hcf0 (by norm_num)
  have hcs1 : cs ≤ 1 / 2 := min_le_right _ _
  have hcscf : cs ≤ cf := min_le_left _ _
  obtain ⟨hj1, hjM, hnE, hE1, hE2, hcl1, hjl⟩ := rl_dot_idx hdaN1 hσ hl1 hlp hi hiN
  have hEdef : gammaBand (N - 1) σ l i = gammaLoc (N - 1) σ (cumCount (N - 1) σ (l - 1) + i) :=
    rfl
  rw [hEdef] at hE ⊢
  rw [rl_lamDot_eq hSig Xm hN2 hj1
    (by have := min_le_right M (N - 1); omega : cumCount (N - 1) σ (l - 1) + i ≤ N)]
  set j := cumCount (N - 1) σ (l - 1) + i with hj
  set E := gammaLoc (N - 1) σ j with hEd
  have hE' : |E - a| ≤ t₀ / 16 := by
    rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
  have hEτ : τ / 2 ≤ E := by linarith [hE.1]
  have hpa := hpart l hl1 hlp E hE1 hE2 hE'
  -- `ḋ_{l−1} ≥ d_{k−1}`
  have hna := (nClass_edgeVal hda hk hkp).1
  rw [← ha] at hna
  have hnstar : nClass N σ (a + τ / 2) = cumCount N σ (k - 1) :=
    rl_n_gap_up hda hk hkp (by linarith) fun h2 => by
      have := rl_sep_up hda h2 hreg; linarith
  have hc1 : (cumCount N σ (k - 1) : ℝ) ≤ cumCount (N - 1) σ (l - 1) := by
    rw [← hcl1, ← hnstar, ← hgap]
    exact rl_nClass_anti hdaN1.nonneg hN10 (by linarith)
  have hc1' : cumCount N σ (k - 1) + i ≤ j := by
    have : cumCount N σ (k - 1) ≤ cumCount (N - 1) σ (l - 1) := by exact_mod_cast hc1
    omega
  have hsE := hsub E hEτ
  rw [abs_le, hnE] at hsE
  -- the mass of `ϱ` below `a`
  have hρ : ∀ x, a - t₀ ≤ x → x ≤ a →
      rlC1 τ * √(a - x) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rlC2 τ * √(a - x) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k - 1 + 1) * (x - a) ≤ 0 := by
      rw [show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num; linarith
    have := rl_rho_edge hda hreg hx hside
    rwa [abs_of_nonpos (by linarith), neg_sub] at this
  have hlo := rl_lo_up hda.nonneg hN0 (t := t₀) (by linarith) (rl_C1_pos hτ).le
    fun x h1 h2 => (hρ x h1 h2).1
  have hm8 := hlo (t₀ / 16) (t₀ / 8) (by positivity) (by linarith) (by linarith)
  have hm2 := hlo (t₀ / 16) (t₀ / 2) (by positivity) (by linarith) (by linarith)
  have e8 : (N : ℝ) * rlC1 τ * √(t₀ / 16) * (t₀ / 8 - t₀ / 16) = N * cf := by rw [hcf]; ring
  have e2 : (N : ℝ) * rlC1 τ * √(t₀ / 16) * (t₀ / 2 - t₀ / 16) = 7 * (N * cf) := by
    rw [hcf]; ring
  rw [e8] at hm8
  rw [e2] at hm2
  have hnE16 : nClass N σ E ≤ nClass N σ (a - t₀ / 16) :=
    rl_nClass_anti hda.nonneg hN0 (by linarith [hE.1])
  -- the far count: `d_k − j ≥ 6 N c_f`
  have hwide := rl_band_wide hda hk hkp (Or.inr hreg)
  rw [← ha] at hwide
  have hck : nClass N σ (a - t₀ / 2) ≤ cumCount N σ k :=
    rl_n_le_cum hda hk hkp (by linarith)
  have hfar : (j : ℝ) + 6 * (N * cf) + 1 ≤ cumCount N σ k := by linarith
  have hj1k : j + 1 ≤ cumCount N σ k := by
    have h6 : (0 : ℝ) ≤ 6 * (N * cf) := by positivity
    have : (j : ℝ) + 1 ≤ cumCount N σ k := by linarith
    exact_mod_cast this
  have hcm := (rl_cum hda hσ hk hkp).1
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 (by omega)
  obtain ⟨-, hnγ'⟩ := nClass_gammaLoc hda hσ (by omega : 1 ≤ j + 1) (by omega)
  push_cast at hnγ'
  set γ := gammaLoc N σ j with hγd
  set γ' := gammaLoc N σ (j + 1) with hγd'
  have hc1r : (cumCount N σ (k - 1) : ℝ) + i ≤ j := by exact_mod_cast hc1'
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  -- locations of `γ_j`, `γ_{j+1}`
  have hγa : γ < a := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
    linarith
  have hγ'a : γ' < a := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
    linarith
  have hγ'γ : γ' < γ := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
    linarith
  have hγ'8 : a - t₀ / 8 ≤ γ' := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_le.mp hc).le
    linarith
  -- the band index `i' = j − d_{k−1}`
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk hkp
  set i' := j - cumCount N σ (k - 1) with hi'
  have hi'j : cumCount N σ (k - 1) + i' = j := by omega
  have hi'j' : cumCount N σ (k - 1) + (i' + 1) = j + 1 := by omega
  have hi'1 : 1 ≤ i' := by omega
  have hii' : i ≤ i' := by omega
  have hi'N : i' ≤ N := by have := min_le_right M (N - 1); omega
  have hi'r : (i' : ℝ) = j - cumCount N σ (k - 1) := by
    rw [hi', Nat.cast_sub (by omega)]
  -- rigidity at `N` for `j` and `j + 1`
  have hwin : ∀ x, a - t₀ / 8 ≤ x → x < a →
      x ∈ Set.Icc (a - edgeTau' τ / 2) (a + edgeTau' τ / 2) := by
    intro x h1 h2; constructor <;> linarith
  have hr1 := hω i' hi'1 (by omega) (by rw [gammaBand, hi'j]; exact hwin _ (by linarith) hγa)
  have hr2 := hω (i' + 1) (by omega) (by omega)
    (by rw [gammaBand, hi'j']; exact hwin _ hγ'8 hγ'a)
  rw [lamBand, gammaBand, hi'j] at hr1
  rw [lamBand, gammaBand, hi'j'] at hr2
  have hfarN : cs * i' ≤ (cumCount N σ k : ℝ) - j := by
    have : cs * (i' : ℝ) ≤ cf * N := by
      have := mul_le_mul hcscf (by exact_mod_cast hi'N : (i' : ℝ) ≤ N) (Nat.cast_nonneg _)
        hcf0.le
      exact this
    linarith
  have hbn : (bandNat N σ k : ℝ) = cumCount N σ k - cumCount N σ (k - 1) := by
    rw [← hcs]; push_cast; ring
  have hi'0 : (0 : ℝ) ≤ i' := Nat.cast_nonneg _
  have hmin1 : cs * i' ≤ ((min i' (bandNat N σ k + 1 - i') : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub (show i' ≤ bandNat N σ k + 1 by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    have hcsl := mul_le_mul_of_nonneg_right hcs1 hi'0
    refine le_min (by linarith) (by rw [hbn]; linarith)
  have hmin2 : cs * i' ≤ ((min (i' + 1) (bandNat N σ k + 1 - (i' + 1)) : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub (show i' + 1 ≤ bandNat N σ k + 1 by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    have hcsl := mul_le_mul_of_nonneg_right hcs1 hi'0
    refine le_min (by linarith) (by rw [hbn]; linarith)
  have hcsi : 0 < cs * (i' : ℝ) := by
    have : (1 : ℝ) ≤ i' := by exact_mod_cast hi'1
    positivity
  have hb1 := (abs_le.1 (hr1.trans (rl_rig_ge (N := N) hcsi hmin1)))
  have hb2 := (abs_le.1 (hr2.trans (rl_rig_ge (N := N) hcsi hmin2)))
  -- the classical comparisons
  have hcount0 : ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 3 / 2 → ∀ v, 0 ≤ v → v ≤ t₀ →
      |(nClass (N - 1) σ (a - v) + θ - cumCount N σ (k - 1)) -
        (nClass N σ (a - v) - nClass N σ a)| ≤ s := by
    intro θ hθ0 hθ1 v hv0 hvt
    have := hsub (a - v) (by linarith)
    rw [abs_le] at this ⊢
    constructor <;> linarith
  have hcmp1 := rl_cmp_up hda hτ1 hk hreg (ι := i') hi'1 (γ := γ) (E := E)
    (by rw [hnγ, hna, hi'r]; ring) hγa (by linarith)
    (fun v => nClass (N - 1) σ (a - v) + 1 / 2 - cumCount N σ (k - 1))
    (hcount0 (1 / 2) (by norm_num) (by norm_num))
    (fun v hv0 hvt hm => by
      have h3 : (j : ℝ) - 1 / 2 ≤ nClass (N - 1) σ (a - v) := by
        rw [hi'r] at hm; linarith
      have := rl_le_gamma hdaN1 hj1 (by linarith) h3
      linarith)
    (fun v hv0 hvt hlt => by
      have := rl_nClass_anti hdaN1.nonneg hN10 (show a - v ≤ E by linarith)
      rw [hi'r]; linarith)
    (by linarith) hs1 hy hYt hA2 hA3 hA4 hA5
  have hcmp2 := rl_cmp_up hda hτ1 hk hreg (ι := i' + 1) (by omega) (γ := γ') (E := E)
    (by rw [hnγ', hna]; push_cast; rw [hi'r]; ring) hγ'a (by linarith)
    (fun v => nClass (N - 1) σ (a - v) + 3 / 2 - cumCount N σ (k - 1))
    (hcount0 (3 / 2) (by norm_num) le_rfl)
    (fun v hv0 hvt hm => by
      have h3 : (j : ℝ) - 1 / 2 ≤ nClass (N - 1) σ (a - v) := by
        push_cast at hm; rw [hi'r] at hm; linarith
      have := rl_le_gamma hdaN1 hj1 (by linarith) h3
      linarith)
    (fun v hv0 hvt hlt => by
      have := rl_nClass_anti hdaN1.nonneg hN10 (show a - v ≤ E by linarith)
      push_cast; rw [hi'r]; linarith)
    (by linarith) hs1 hy hYt hA2 hA3 hA4 hA5
  -- the scale `β = i'^{−1/3} N^{−2/3}`
  obtain ⟨hB0, hBN, hNB⟩ := rl_beta_bounds hi'1 hi'N
  set B := (i' : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) with hB
  have hβ2 : ((i' + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ B := by
    have := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hi'1 : (0 : ℝ) < i')
      (by push_cast; linarith : (i' : ℝ) ≤ ((i' + 1 : ℕ) : ℝ)) (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hcsr : (cs * (i' : ℝ)) ^ (-(1 / 3 : ℝ)) = cs ^ (-(1 / 3 : ℝ)) * (i' : ℝ) ^ (-(1 / 3 : ℝ)) :=
    Real.mul_rpow hcs0.le (Nat.cast_nonneg _)
  set R := (N : ℝ) ^ ε₁ * cs ^ (-(1 / 3 : ℝ)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hrig : (N : ℝ) ^ ε₁ * (cs * (i' : ℝ)) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) =
      R * B := by rw [hcsr, hR, hB]; ring
  rw [hrig] at hb1 hb2
  have hEc0 : 0 ≤ Ec := le_trans (by unfold rlL rlM; have := rl_C1_pos hτ; positivity) hA5
  have hcmp2' : |γ' - E| ≤ Ec * B := hcmp2.trans (mul_le_mul_of_nonneg_left hβ2 hEc0)
  rw [abs_le] at hcmp1 hcmp2'
  -- interlacing and the factor `N/(N − 1)`
  set L := sortedEig (QN Sig Xm) (j + 1) with hL
  set U := sortedEig (QN Sig Xm) j with hU
  have hNεB : (N : ℝ) ^ ε * B ≤ τ / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hBN (by positivity)) hsmall
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have htot : Ec * B + R * B + 2 * (Ca + 1) * B ≤ (N : ℝ) ^ ε * B := by
    have := mul_le_mul_of_nonneg_right hfin hB0.le
    linarith
  have hRB0 : 0 ≤ R * B := by positivity
  have hCB0 : 0 ≤ 2 * (Ca + 1) * B := by positivity
  have hL0 : 0 < L := by linarith
  have hLj := rl_interlace_lo hSig Xm hj1 (hj1k.trans (hcm.trans (min_le_right _ _)))
  obtain ⟨hd1, hd2⟩ := rl_dot_bounds hSig Xm hN2 hj1 (by omega) hL0 hLj le_rfl
  have hU0 : 0 ≤ U := by linarith
  have hUle : U ≤ Ca + 1 := by linarith
  have hdiv := rl_div_pred hU0 hN2
  have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have h2U : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * B := by
    have h1 : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hNi
    have h2 : 2 * (Ca + 1) * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * B :=
      mul_le_mul_of_nonneg_left hNB (by positivity)
    linarith
  have hfinal : |(N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j - E| ≤ (N : ℝ) ^ ε * B := by
    rw [abs_le]; constructor <;> linarith
  refine hfinal.trans ?_
  have hrl := rl_rig_le (N := N) (Nk := bandNat (N - 1) σ l) (i := i) (i₀ := i') (ε := ε)
    (le_min hi (by omega)) ((min_le_left _ _).trans hii')
  rw [hB, ← mul_assoc]
  exact hrl

/-- `(ι − 1)^{−1/3} ≤ 2 ι^{−1/3}` for `ι ≥ 2`. -/
private lemma rl_rpow_pred {ι : ℕ} (hι : 2 ≤ ι) :
    ((ι - 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * (ι : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hι2 : (2 : ℝ) ≤ ι := by exact_mod_cast hι
  have hc : ((ι - 1 : ℕ) : ℝ) = ι - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have h1 : (1 / 2 : ℝ) * ι ≤ ((ι - 1 : ℕ) : ℝ) := by rw [hc]; linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 / 2 * ι) h1
    (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
  have h3 : (1 / 2 : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
    norm_num
    calc (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : (0 : ℝ) ≤ (ι : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  nlinarith

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- The lower edge `a_{2k}` of the band `k` at one index of `N − 1`, on the rigidity event of
Theorem 3.14 (iii) at `N`: interlacing (or, at the bottom index `j = d_k`, the secular count
`eigCount_compress_secular`), the classical comparison and the index alignment `ḋ_l ≤ d_k` give
`|λ̇_{l,i} − γ̇_{l,i}| ≤ rigBound N Ṅ_l i ε`. -/
private lemma rl_edge_dn_det {τ ε ε₁ δ s y Ec y₂ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hda : DensityAssumptions τ N (specOf Sig))
    (hσ : ∀ j, 0 < specOf Sig j) (hSig : Sig.IsHermitian) (hN2 : 2 ≤ N) (hτ1 : τ ≤ 1)
    (hk : 1 ≤ k) (hkp : k ≤ numBands N (specOf Sig))
    (hreg : RegularEdge τ N (specOf Sig) (2 * k))
    (hsub : ∀ x, τ / 2 ≤ x →
      |nClass (N - 1) (specOf Sig) x - nClass N (specOf Sig) x| ≤ (N : ℝ) ^ δ)
    (hpart : ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) → ∀ x,
      edgeVal (N - 1) (specOf Sig) (2 * l) < x → x < edgeVal (N - 1) (specOf Sig) (2 * l - 1) →
      |x - edgeVal N (specOf Sig) (2 * k)| ≤ edgeTau0 τ / 16 →
      edgeVal N (specOf Sig) (2 * k) - y ^ 2 ≤ edgeVal (N - 1) (specOf Sig) (2 * l) ∧
        cumCount (N - 1) (specOf Sig) l ≤ cumCount N (specOf Sig) k)
    (hω : ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k →
      gammaBand N (specOf Sig) k i ∈
        Set.Icc (edgeVal N (specOf Sig) (2 * k) - edgeTau' τ / 2)
          (edgeVal N (specOf Sig) (2 * k) + edgeTau' τ / 2) →
      |lamBand Sig Xm k i - gammaBand N (specOf Sig) k i| ≤
        rigBound N (bandNat N (specOf Sig) k) i ε₁)
    (hsec : (k < numBands N (specOf Sig) ∨ M < N) →
      eigCount (QN Sig (Xdot Xm)) (edgeVal N (specOf Sig) (2 * k) - y₂) =
        eigCount (QN Sig Xm) (edgeVal N (specOf Sig) (2 * k) - y₂))
    (hmass : (N : ℝ) ^ δ + 2 ≤ N * (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)))
    (hsδ : (N : ℝ) ^ δ + 3 / 2 ≤ s) (hs1 : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau0 τ)
    (hA2 : (rlK (rlC1 τ) (rlC2 τ) + 1) * s + 1 ≤ N * rlC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rlK (rlC1 τ) (rlC2 τ) ^ 3 * s ^ 3 ≤ rlC1 τ ^ 2 * Ec ^ 3)
    (hA4 : 8 * rlK (rlC1 τ) (rlC2 τ) * s * y ^ 6 * N ^ 2 ≤ Ec ^ 3)
    (hA5 : rlL (rlC1 τ) (rlC2 τ) * s ≤ Ec)
    (hfin : 2 * Ec + (N : ℝ) ^ ε₁ *
        (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) +
        2 * (2 * τ⁻¹ * (1 + τ⁻¹) + 1) ≤ (N : ℝ) ^ ε)
    (hsmall : (N : ℝ) ^ ε * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ τ / 4)
    (hR2 : (N : ℝ) ^ ε₁ *
        (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) *
        (N : ℝ) ^ (-(2 / 3 : ℝ)) < y₂)
    (hsecfin : Ec * (N : ℝ) ^ (-(2 / 3 : ℝ)) + y ^ 2 + y₂ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-(2 / 3 : ℝ)))
    (hy₂ : y₂ ≤ τ / 4)
    {l i : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ numBands (N - 1) (specOf Sig)) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat (N - 1) (specOf Sig) l)
    (hE : gammaBand (N - 1) (specOf Sig) l i ∈
      Set.Icc (edgeVal N (specOf Sig) (2 * k) - edgeTau' τ / 4)
        (edgeVal N (specOf Sig) (2 * k) + edgeTau' τ / 4)) :
    |lamDotBand Sig Xm l i - gammaBand (N - 1) (specOf Sig) l i| ≤
      rigBound N (bandNat (N - 1) (specOf Sig) l) i ε := by
  have hτ := hda.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨ht'0, ht0e, -⟩ := rl_tau_facts hτ hτ1
  have ht0 := rl_tau0_le hτ hτ1
  have ht0p : 0 < edgeTau0 τ := by linarith
  set σ := specOf Sig with hσdef
  have hdaN1 := rl_da_pred hda hN2
  obtain ⟨hN0, -, -⟩ := rl_facts hda
  have hN10 : 0 < N - 1 := by omega
  set t₀ := edgeTau0 τ with ht₀
  set a := edgeVal N σ (2 * k) with ha
  have haτ : τ ≤ a := hreg.2.2.1
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have haC := (rl_edge_mem hda (k := 2 * k) (by omega) (by omega)).2
  rw [← ha, ← hCa] at haC
  set cf := rlC1 τ * √(t₀ / 16) * (t₀ / 16) with hcf
  have hcf0 : 0 < cf := by have := rl_C1_pos hτ; rw [hcf]; positivity
  set cs := min cf (1 / 2) with hcs
  have hcs0 : 0 < cs := lt_min hcf0 (by norm_num)
  have hcs1 : cs ≤ 1 / 2 := min_le_right _ _
  have hcscf : cs ≤ cf := min_le_left _ _
  obtain ⟨hj1, hjM, hnE, hE1, hE2, -, hjl⟩ := rl_dot_idx hdaN1 hσ hl1 hlp hi hiN
  have hEdef : gammaBand (N - 1) σ l i = gammaLoc (N - 1) σ (cumCount (N - 1) σ (l - 1) + i) :=
    rfl
  rw [hEdef] at hE ⊢
  rw [rl_lamDot_eq hSig Xm hN2 hj1
    (by have := min_le_right M (N - 1); omega : cumCount (N - 1) σ (l - 1) + i ≤ N)]
  set j := cumCount (N - 1) σ (l - 1) + i with hj
  set E := gammaLoc (N - 1) σ j with hEd
  have hE' : |E - a| ≤ t₀ / 16 := by
    rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
  have hEτ : τ / 2 ≤ E := by linarith [hE.1]
  obtain ⟨hpa, hcl⟩ := hpart l hl1 hlp E hE1 hE2 hE'
  have hjk : j ≤ cumCount N σ k := hjl.trans hcl
  have hsE := hsub E hEτ
  rw [abs_le, hnE] at hsE
  -- the mass of `ϱ` above `a`
  have hρ : ∀ x, a ≤ x → x ≤ a + t₀ →
      rlC1 τ * √(x - a) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rlC2 τ * √(x - a) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k + 1) * (x - a) ≤ 0 := by
      rw [pow_succ, pow_mul]; norm_num; linarith
    have := rl_rho_edge hda hreg hx hside
    rwa [abs_of_nonneg (by linarith)] at this
  have hlo := rl_lo_dn hda.nonneg hN0 (t := t₀) (by linarith) (rl_C1_pos hτ).le
    fun x h1 h2 => (hρ x h1 h2).1
  have hm8 := hlo (t₀ / 16) (t₀ / 8) (by positivity) (by linarith) (by linarith)
  have hm2 := hlo (t₀ / 16) (t₀ / 2) (by positivity) (by linarith) (by linarith)
  have e8 : (N : ℝ) * rlC1 τ * √(t₀ / 16) * (t₀ / 8 - t₀ / 16) = N * cf := by rw [hcf]; ring
  have e2 : (N : ℝ) * rlC1 τ * √(t₀ / 16) * (t₀ / 2 - t₀ / 16) = 7 * (N * cf) := by
    rw [hcf]; ring
  rw [e8] at hm8
  rw [e2] at hm2
  have hnE16 : nClass N σ (a + t₀ / 16) ≤ nClass N σ E :=
    rl_nClass_anti hda.nonneg hN0 (by linarith [hE.2])
  -- the far count: `j − d_{k−1} ≥ 6 N c_f`
  have hwide := rl_band_wide hda hk hkp (Or.inl hreg)
  rw [← ha] at hwide
  have hna1 := (nClass_edgeVal hda hk hkp).1
  have hck1 : (cumCount N σ (k - 1) : ℝ) ≤ nClass N σ (a + t₀ / 2) := by
    rw [← hna1]; exact rl_nClass_anti hda.nonneg hN0 (by linarith)
  have hfar : (cumCount N σ (k - 1) : ℝ) + 6 * (N * cf) + 1 ≤ j := by linarith
  have hna := (nClass_edgeVal hda hk hkp).2 (by linarith)
  rw [← ha] at hna
  have hcm := (rl_cum hda hσ hk hkp).1
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 (by omega)
  set γ := gammaLoc N σ j with hγd
  have hjkr : (j : ℝ) ≤ cumCount N σ k := by exact_mod_cast hjk
  have hγa : a < γ := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
    linarith
  have hγ8 : γ ≤ a + t₀ / 8 := by
    by_contra hc
    have := rl_nClass_anti hda.nonneg hN0 (not_le.mp hc).le
    linarith
  -- the band indices `i' = j − d_{k−1}` and `i'' = d_k − j + 1`
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk hkp
  have hc1' : cumCount N σ (k - 1) + 1 ≤ j := by
    have h6 : (0 : ℝ) ≤ 6 * (N * cf) := by positivity
    have : (cumCount N σ (k - 1) : ℝ) + 1 ≤ j := by linarith
    exact_mod_cast this
  set i' := j - cumCount N σ (k - 1) with hi'
  set i'' := cumCount N σ k + 1 - j with hi''
  have hi'j : cumCount N σ (k - 1) + i' = j := by omega
  have hi'1 : 1 ≤ i' := by omega
  have hi''1 : 1 ≤ i'' := by omega
  have hi'r : (i' : ℝ) = j - cumCount N σ (k - 1) := by
    rw [hi', Nat.cast_sub (by omega)]
  have hi''r : (i'' : ℝ) = cumCount N σ k + 1 - j := by
    rw [hi'', Nat.cast_sub (by omega)]; push_cast; ring
  have hi''N : i'' ≤ N := by omega
  have hbn : (bandNat N σ k : ℝ) = cumCount N σ k - cumCount N σ (k - 1) := by
    rw [← hcs]; push_cast; ring
  have hi''0 : (0 : ℝ) ≤ i'' := Nat.cast_nonneg _
  have hfarN : cs * i'' ≤ (j : ℝ) - cumCount N σ (k - 1) := by
    have : cs * (i'' : ℝ) ≤ cf * N :=
      mul_le_mul hcscf (by exact_mod_cast hi''N : (i'' : ℝ) ≤ N) hi''0 hcf0.le
    linarith
  have hcsi : 0 < cs * (i'' : ℝ) := by
    have : (1 : ℝ) ≤ i'' := by exact_mod_cast hi''1
    positivity
  -- rigidity at `N` for `j`
  have hwin : ∀ x, a < x → x ≤ a + t₀ / 8 →
      x ∈ Set.Icc (a - edgeTau' τ / 2) (a + edgeTau' τ / 2) := by
    intro x h1 h2; constructor <;> linarith
  have hr1 := hω i' hi'1 (by omega) (by rw [gammaBand, hi'j]; exact hwin _ hγa hγ8)
  rw [lamBand, gammaBand, hi'j] at hr1
  have hmin1 : cs * i'' ≤ ((min i' (bandNat N σ k + 1 - i') : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_sub (show i' ≤ bandNat N σ k + 1 by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    have hcsl := mul_le_mul_of_nonneg_right hcs1 hi''0
    refine le_min (by rw [hi'r]; linarith) (by rw [hbn, hi'r]; linarith)
  have hb1 := abs_le.1 (hr1.trans (rl_rig_ge (N := N) hcsi hmin1))
  -- the classical comparison at `j`
  have hcount0 : ∀ (θ : ℝ), -1 / 2 ≤ θ → θ ≤ 1 / 2 → ∀ v, 0 ≤ v → v ≤ t₀ →
      |((cumCount N σ k : ℝ) - nClass (N - 1) σ (a + v) + θ) -
        (nClass N σ a - nClass N σ (a + v))| ≤ s := by
    intro θ hθ0 hθ1 v hv0 hvt
    have := hsub (a + v) (by linarith)
    rw [abs_le] at this ⊢
    constructor <;> linarith
  have hcmp1 := rl_cmp_dn hda hreg (ι := i'') hi''1 (γ := γ) (E := E)
    (by rw [hnγ, hna, hi''r]; ring) hγa (by linarith)
    (fun v => (cumCount N σ k : ℝ) - nClass (N - 1) σ (a + v) + 1 / 2)
    (hcount0 (1 / 2) (by norm_num) le_rfl)
    (fun v hv0 hvt hm => by
      rw [hi''r] at hm
      by_contra hc
      have := rl_nClass_anti hdaN1.nonneg hN10 (show a + v ≤ E by linarith)
      linarith)
    (fun v hv0 hvt hlt => by
      rw [hi''r]
      by_contra hc
      have := rl_le_gamma hdaN1 hj1 (by linarith) (show (j : ℝ) - 1 / 2 ≤
        nClass (N - 1) σ (a + v) by linarith)
      linarith)
    (by linarith) hs1 hy hYt hA2 hA3 hA4 hA5
  -- the scale `β = i''^{−1/3} N^{−2/3}`
  obtain ⟨hB0, hBN, hNB⟩ := rl_beta_bounds hi''1 hi''N
  set B := (i'' : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) with hB
  have hcsr : (cs * (i'' : ℝ)) ^ (-(1 / 3 : ℝ)) =
      cs ^ (-(1 / 3 : ℝ)) * (i'' : ℝ) ^ (-(1 / 3 : ℝ)) :=
    Real.mul_rpow hcs0.le (Nat.cast_nonneg _)
  set R := (N : ℝ) ^ ε₁ * cs ^ (-(1 / 3 : ℝ)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hrig : (N : ℝ) ^ ε₁ * (cs * (i'' : ℝ)) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) =
      R * B := by rw [hcsr, hR, hB]; ring
  rw [hrig] at hb1
  have hEc0 : 0 ≤ Ec := le_trans (by unfold rlL rlM; have := rl_C1_pos hτ; positivity) hA5
  rw [abs_le] at hcmp1
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hNεB : (N : ℝ) ^ ε * B ≤ τ / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hBN (by positivity)) hsmall
  have htot : 2 * Ec * B + R * B + 2 * (Ca + 1) * B ≤ (N : ℝ) ^ ε * B := by
    have := mul_le_mul_of_nonneg_right hfin hB0.le
    linarith
  have hRB0 : 0 ≤ R * B := by positivity
  have hEcB0 : 0 ≤ Ec * B := by positivity
  have hCB0 : 0 ≤ 2 * (Ca + 1) * B := by positivity
  set U := sortedEig (QN Sig Xm) j with hU
  have hU0 : 0 ≤ U := by linarith
  have hUle : U ≤ Ca + 1 := by linarith
  have hdiv := rl_div_pred hU0 hN2
  have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have h2U : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * B := by
    have h1 : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hNi
    have h2 : 2 * (Ca + 1) * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * B :=
      mul_le_mul_of_nonneg_left hNB (by positivity)
    linarith
  have hjN : j ≤ N := by have := min_le_right M (N - 1); omega
  -- the lower bound for `λ_j(π̄ B π̄)`
  obtain ⟨L, hL0, hLj, hLE⟩ : ∃ L : ℝ, 0 < L ∧ L ≤ sortedEig (QN Sig (Xdot Xm)) j ∧
      E - L ≤ (N : ℝ) ^ ε * B := by
    by_cases hbot : j + 1 ≤ cumCount N σ k
    · -- interlacing with `λ_{j+1}`
      have hi''2 : 2 ≤ i'' := by omega
      obtain ⟨-, hnγ'⟩ := nClass_gammaLoc hda hσ (by omega : 1 ≤ j + 1) (by omega)
      push_cast at hnγ'
      set γ' := gammaLoc N σ (j + 1) with hγd'
      have hγ'a : a < γ' := by
        by_contra hc
        have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
        have : (j : ℝ) + 1 ≤ cumCount N σ k := by exact_mod_cast hbot
        linarith
      have hγ'γ : γ' < γ := by
        by_contra hc
        have := rl_nClass_anti hda.nonneg hN0 (not_lt.mp hc)
        linarith
      have hi'j' : cumCount N σ (k - 1) + (i' + 1) = j + 1 := by omega
      have hr2 := hω (i' + 1) (by omega) (by omega)
        (by rw [gammaBand, hi'j']; exact hwin _ hγ'a (by linarith))
      rw [lamBand, gammaBand, hi'j'] at hr2
      have hmin2 : cs * i'' ≤ ((min (i' + 1) (bandNat N σ k + 1 - (i' + 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_min, Nat.cast_sub (show i' + 1 ≤ bandNat N σ k + 1 by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
        have h2 : (2 : ℝ) ≤ i'' := by exact_mod_cast hi''2
        have hcsl := mul_le_mul_of_nonneg_right hcs1 hi''0
        refine le_min (by rw [hi'r]; linarith) (by rw [hbn, hi'r]; linarith)
      have hb2 := abs_le.1 (hr2.trans (rl_rig_ge (N := N) hcsi hmin2))
      rw [hrig] at hb2
      have hι1 : 1 ≤ i'' - 1 := by omega
      have hcmp2 := rl_cmp_dn hda hreg (ι := i'' - 1) hι1 (γ := γ') (E := E)
        (by rw [hnγ', hna, Nat.cast_sub (by omega), hi''r]; push_cast; ring) hγ'a (by linarith)
        (fun v => (cumCount N σ k : ℝ) - nClass (N - 1) σ (a + v) - 1 / 2)
        (by
          intro v hv0 hvt
          have := hcount0 (-1 / 2) (by norm_num) (by norm_num) v hv0 hvt
          rwa [show (cumCount N σ k : ℝ) - nClass (N - 1) σ (a + v) + -1 / 2 =
            (cumCount N σ k : ℝ) - nClass (N - 1) σ (a + v) - 1 / 2 by ring] at this)
        (fun v hv0 hvt hm => by
          rw [Nat.cast_sub (by omega), hi''r] at hm
          push_cast at hm
          by_contra hc
          have := rl_nClass_anti hdaN1.nonneg hN10 (show a + v ≤ E by linarith)
          linarith)
        (fun v hv0 hvt hlt => by
          rw [Nat.cast_sub (by omega), hi''r]
          push_cast
          by_contra hc
          have := rl_le_gamma hdaN1 hj1 (by linarith) (show (j : ℝ) - 1 / 2 ≤
            nClass (N - 1) σ (a + v) by linarith)
          linarith)
        (by linarith) hs1 hy hYt hA2 hA3 hA4 hA5
      have hβ2 : ((i'' - 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 2 * B := by
        have := mul_le_mul_of_nonneg_right (rl_rpow_pred hi''2)
          (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)))
        rw [hB]; linarith
      have hcmp2' : |γ' - E| ≤ Ec * (2 * B) :=
        hcmp2.trans (mul_le_mul_of_nonneg_left hβ2 hEc0)
      rw [abs_le] at hcmp2'
      refine ⟨sortedEig (QN Sig Xm) (j + 1), by linarith, ?_, by linarith⟩
      exact rl_interlace_lo hSig Xm hj1 (hbot.trans (hcm.trans (min_le_right _ _)))
    · -- the bottom index `j = d_k`: the secular count
      have hjk' : j = cumCount N σ k := by omega
      have hi''one : i'' = 1 := by omega
      have hcase : k < numBands N σ ∨ M < N := by
        by_contra hc
        push Not at hc
        have hkp' : k = numBands N σ := le_antisymm hkp hc.1
        have hcp : cumCount N σ k = min M N := by
          have := (rl_cum hda hσ hk hkp).2
          rwa [← hkp'] at this
        rw [min_eq_right hc.2] at hcp
        have : j ≤ N - 1 := hjM.trans (min_le_right _ _)
        omega
      have hB1 : B = (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [hB, hi''one]; simp
      have hlamj : a - y₂ ≤ U := by
        have : R * B < y₂ := by rw [hB1]; rw [hR] ; exact hR2
        linarith
      have hc1 := (sortedEig_ge_iff (XSX_isHermitian hSig Xm) hj1 hjN _).1 hlamj
      have hc2 : j ≤ eigCount (QN Sig (Xdot Xm)) (a - y₂) := le_of_le_of_eq hc1 (hsec hcase).symm
      have hLj := (sortedEig_ge_iff (XSX_isHermitian hSig (Xdot Xm)) hj1 hjN _).2 hc2
      have hu : γ - a ≤ y ^ 2 := by
        by_contra hc
        push Not at hc
        have hY := rl_mass_low (N := (N : ℝ)) hNpos (rl_C1_pos hτ)
          (Φ := fun v => nClass N σ a - nClass N σ (a + v)) (by simp) hlo (v := y ^ 2)
          (by positivity) hYt
        rw [Real.sqrt_sq hy.le] at hY
        have hmono := rl_nClass_anti hda.nonneg hN0 (show a + y ^ 2 ≤ γ by linarith)
        have hK0 : 0 ≤ rlK (rlC1 τ) (rlC2 τ) := by
          unfold rlK rlL rlM; have := rl_C1_pos hτ; positivity
        have e : (N : ℝ) * rlC1 τ * y * y ^ 2 / 4 = N * rlC1 τ * y ^ 3 / 4 := by ring
        rw [hi''one] at hi''r
        have hKs : 1 ≤ (rlK (rlC1 τ) (rlC2 τ) + 1) * s :=
          one_le_mul_of_one_le_of_one_le (by linarith) hs1
        push_cast at hi''r
        linarith
      refine ⟨a - y₂, by linarith, hLj, ?_⟩
      rw [hB1]
      rw [hB1] at hcmp1
      linarith
  obtain ⟨hd1, hd2⟩ := rl_dot_bounds hSig Xm hN2 hj1 hjN hL0 hLj le_rfl
  have hfinal : |(N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j - E| ≤ (N : ℝ) ^ ε * B := by
    rw [abs_le]; constructor <;> linarith
  refine hfinal.trans ?_
  have hrl := rl_rig_le (N := N) (Nk := bandNat (N - 1) σ l) (i := i) (i₀ := i'') (ε := ε)
    (le_min hi (by omega)) ((min_le_right _ _).trans (by
      obtain ⟨-, -, hcs'⟩ := cumCount_spec hdaN1 hl1 hlp
      omega))
  rw [hB, ← mul_assoc]
  exact hrl

/-! ## The secular count at a lower edge -/

/-- `Σ̲⁻¹ = diag(Σ⁻¹, 1)` for `Σ > 0`. -/
private lemma rl_ulSigma_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (ulSigma N Sig)⁻¹ = fromBlocks (cplx Sig)⁻¹ 0 0 1 := by
  have hu : IsUnit (cplx Sig) := hSig.isUnit.map (algebraMap ℝ ℂ).mapMatrix
  rw [ulSigma, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hu isUnit_one)]
  simp

/-- The `𝓘_N × 𝓘_N` block of `Σ̲⁻¹ (G − Π) Σ̲⁻¹` is `G_N − m`. -/
private lemma rl_lawMat_22 {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (lawMat Sig Xm z).toBlocks₂₂ = GN Sig Xm z - mFun N (specOf Sig) z • 1 := by
  have h2 : ∀ K : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (fromBlocks (cplx Sig)⁻¹ 0 0 1 * K * fromBlocks (cplx Sig)⁻¹ 0 0 1).toBlocks₂₂ =
        K.toBlocks₂₂ := by
    intro K
    rw [← fromBlocks_toBlocks K]
    simp [fromBlocks_multiply]
  unfold lawMat
  rw [rl_ulSigma_inv hSig, h2]
  ext i j
  simp [toBlocks₂₂, piMat, (GeqG hSig Xm hz).1]

/-- `⟨(0, 1_N), A (0, 1_N)⟩ = ⟨1_N, A_{𝓘_N 𝓘_N} 1_N⟩`. -/
private lemma rl_testBilin_inr (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) :
    testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) A
      (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) =
      testBilin (fun _ : Fin N => (1 : ℝ)) A.toBlocks₂₂ (fun _ => 1) := by
  simp [testBilin, dotProduct, mulVec, Fintype.sum_sum_type, toBlocks₂₂]

/-- `|(0, 1_N)| = √N`. -/
private lemma rl_testNorm_inr :
    testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) = √N := by
  simp [testNorm, Fintype.sum_sum_type]

/-- `⟨1, (G − w) 1⟩ = ⟨1, G 1⟩ − N w`. -/
private lemma rl_testBilin_sub (G : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
    testBilin (fun _ : Fin N => (1 : ℝ)) (G - w • 1) (fun _ => 1) =
      testBilin (fun _ : Fin N => (1 : ℝ)) G (fun _ => 1) - N * w := by
  simp only [testBilin, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul]
  simp [dotProduct]
  ring

/-- `A − E` is invertible when `E` is not an eigenvalue of the symmetric matrix `A`. -/
private lemma rl_isUnit_sub {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {E : ℝ}
    (hne : ∀ j, specOf A j ≠ E) : IsUnit (A - E • (1 : Matrix (Fin K) (Fin K) ℝ)) := by
  have hE : E ∉ spectrum ℝ A := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro ⟨j, hj⟩
    exact hne j (by rw [specOf_eq hA]; exact hj)
  rw [spectrum.mem_iff, not_not] at hE
  have e : A - E • (1 : Matrix (Fin K) (Fin K) ℝ) =
      -(algebraMap ℝ (Matrix (Fin K) (Fin K) ℝ) E - A) := by
    rw [Algebra.algebraMap_eq_smul_one]; abel
  rw [e]
  exact hE.neg

/-- The secular count at `E₁ > 0`, `z₁ = E₁ + i δ₁`: if no eigenvalue of `B = XᵀΣX` lies within
`δ₁` of `E₁`, the anisotropic law holds at `z₁` for the test vector `(0, 1_N)`, and
`Re m(z₁) + Im m(z₁) + 2 N^{ε} Ψ(z₁) < 0`, then `π̄ B π̄` and `B` have the same number of
eigenvalues `≥ E₁`. -/
private lemma rl_secular {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 0 < N) {E₁ δ₁ ε₄ : ℝ} (hE₁ : 0 < E₁) (hδ : 0 < δ₁)
    (hgap : ∀ j, δ₁ ≤ |specOf (QN Sig Xm) j - E₁|)
    (hlaw : ‖testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))
        (lawMat Sig Xm ((E₁ : ℂ) + δ₁ * Complex.I)) (Sum.elim 0 fun _ => 1)‖ ≤
      (N : ℝ) ^ ε₄ * (Psi N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))))
    (hsign : (mFun N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)).re +
        (mFun N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)).im +
        2 * ((N : ℝ) ^ ε₄ * Psi N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)) < 0) :
    eigCount (QN Sig (Xdot Xm)) E₁ = eigCount (QN Sig Xm) E₁ := by
  set z₁ : ℂ := (E₁ : ℂ) + δ₁ * Complex.I with hz₁
  have hz : 0 < z₁.im := by simp [hz₁, hδ]
  have hB := XSX_isHermitian hSig.1 Xm
  have hres : (fun _ => (1 : ℝ)) ⬝ᵥ ((QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ *ᵥ
      fun _ => 1) ≤ (testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1)).re +
        (testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1)).im :=
    resolvent_real_le hB (fun _ => (1 : ℝ)) hδ hgap
  rw [rl_testBilin_inr, rl_lawMat_22 hSig Xm hz, rl_testBilin_sub, rl_testNorm_inr] at hlaw
  set T := testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1) with hT
  set m := mFun N (specOf Sig) z₁ with hm
  set P := (N : ℝ) ^ ε₄ * Psi N (specOf Sig) z₁ with hP
  have hNN : √(N : ℝ) * √N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have h1 : ‖T - N * m‖ ≤ P * N := by
    have e : (N : ℝ) ^ ε₄ * (Psi N (specOf Sig) z₁ * √(N : ℝ) * √N) = P * N := by
      rw [hP, mul_assoc (Psi N (specOf Sig) z₁), hNN]; ring
    rw [← e]; exact hlaw
  have hre := (abs_le.1 ((Complex.abs_re_le_norm (T - N * m)).trans h1)).2
  have him := (abs_le.1 ((Complex.abs_im_le_norm (T - N * m)).trans h1)).2
  have e1 : (T - N * m).re = T.re - N * m.re := by simp
  have e2 : (T - N * m).im = T.im - N * m.im := by simp
  rw [e1] at hre
  rw [e2] at him
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hneg : (fun _ => (1 : ℝ)) ⬝ᵥ ((QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ *ᵥ
      fun _ => 1) < 0 := by
    have : (N : ℝ) * (m.re + m.im + 2 * P) < 0 := mul_neg_of_pos_of_neg hNpos hsign
    linarith
  have hinv : IsUnit (QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ)) :=
    rl_isUnit_sub (A := QN Sig Xm) hB (E := E₁) (fun j h => by
      have := hgap j; rw [h, sub_self, abs_zero] at this; linarith)
  exact eigCount_compress_secular hSig.1 Xm hE₁ hinv hneg

/-- Near a regular edge `a_k` with `x_k < 0`: for `Im z > 0` and `|z − a_k| ≤ τ₀(τ)`,
`Re m(z) + Im m(z) ≤ −c_x(τ) + 4 √(|z − a_k| / c₂(τ))` and `Im m(z) ≤ 1`. -/
private lemma rl_sign {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) (hτ1 : τ ≤ 1)
    {k : ℕ} (hreg : RegularEdge τ N σ k) (hx : xCrit N σ k < 0) {z : ℂ} (hz : 0 < z.im)
    (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    (mFun N σ z).re + (mFun N σ z).im ≤
      -edgecx τ + 4 * √(‖z - edgeVal N σ k‖ / edgec2 τ) ∧ (mFun N σ z).im ≤ 1 := by
  have hτ := hda.pos
  obtain ⟨hloc, -, hlow, -, -⟩ := z_a_taylor hda hreg hz.le hza
  have hm : mExt N σ z = mFun N σ z := by
    unfold mExt; rw [ite_eq_left_of_eq_true _ _ (eq_true hz)]
  rw [hm] at hloc hlow
  have hcx := (xCrit_bounds hda hreg).1
  rw [abs_of_neg hx] at hcx
  have hc2 := (rl_C_pos hτ).2
  set d := ‖mFun N σ z - xCrit N σ k‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdle : d ≤ 2 * √(‖z - edgeVal N σ k‖ / edgec2 τ) := by
    have h4 : d ^ 2 ≤ 4 * (‖z - edgeVal N σ k‖ / edgec2 τ) := by
      rw [mul_div_assoc']
      rw [le_div_iff₀ hc2]
      nlinarith
    have : d ≤ √(4 * (‖z - edgeVal N σ k‖ / edgec2 τ)) := Real.le_sqrt_of_sq_le h4
    rwa [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at this
  have hre : (mFun N σ z).re ≤ xCrit N σ k + d := by
    have := Complex.re_le_norm (mFun N σ z - xCrit N σ k)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have him : (mFun N σ z).im ≤ d := by
    have := Complex.im_le_norm (mFun N σ z - xCrit N σ k)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  have hρ1 : edgeRho1 τ ≤ 1 := by
    have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
    have : edgeRho0 τ ≤ τ / 2 := by unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
    linarith
  exact ⟨by linarith, by linarith⟩

/-- `Ψ(z) ≤ 2 √(1/(N η))` when `Im m(z) ≤ 1` and `N η ≥ 1`. -/
private lemma rl_psi_le {σ : Fin M → ℝ} {z : ℂ} (hm : (mFun N σ z).im ≤ 1)
    (hNη : 1 ≤ (N : ℝ) * z.im) : Psi N σ z ≤ 2 * √(1 / ((N : ℝ) * z.im)) := by
  unfold Psi
  have h0 : 0 < (N : ℝ) * z.im := by linarith
  have h1 : √((mFun N σ z).im / (N * z.im)) ≤ √(1 / ((N : ℝ) * z.im)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hm h0.le)
  have h2 : 1 / ((N : ℝ) * z.im) ≤ √(1 / ((N : ℝ) * z.im)) := by
    have h3 : 1 / ((N : ℝ) * z.im) ≤ 1 := by rw [div_le_one h0]; exact hNη
    have h4 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    calc 1 / ((N : ℝ) * z.im) = √((1 / ((N : ℝ) * z.im)) ^ 2) := (Real.sqrt_sq h4).symm
      _ ≤ √(1 / ((N : ℝ) * z.im)) := Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- `N^a ≤ c` for `a < 0`, `c > 0` and `N` large. -/
private lemma rl_ev_small {c a : ℝ} (hc : 0 < c) (ha : a < 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ a ≤ c := by
  obtain ⟨N₀, h⟩ := rl_ev (1 / c) (a := a) (b := 0) ha
  refine ⟨N₀, fun N hN => ?_⟩
  have := h N hN
  rw [Real.rpow_zero] at this
  rw [div_mul_eq_mul_div, one_mul, div_le_one hc] at this
  exact this

/-- `N^a N^b = N^{a+b}` for `N > 0`. -/
private lemma rl_rpow_mul {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
  (Real.rpow_add (by exact_mod_cast hN) a b).symm

/-- The exponent rows of the edge piece at one `N`, at `ε' ∈ (0, 1/2]` (with `δ = ε'/32`,
`η = ε'/16`, `ε₁ = ε'/8`, `ε₃ = ε'/4`, `ε₂ = ε'/2`, `ε₄ = ε'/16`, `s = N^η`, `y = N^{−1/3+η/2}`,
`E_c = N^{2η}`, `y₂ = N^{−2/3+ε₂}`, `y₃ = N^{−2/3+ε₃}`). -/
private def rlEdgeNum (τ ε' C₁ τ₂ : ℝ) (N : ℕ) : Prop :=
      2 ≤ N ∧
      (N : ℝ) ^ (ε' / 32) + 2 ≤ N * (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) ∧
      (N : ℝ) ^ (ε' / 32) + 3 / 2 ≤ (N : ℝ) ^ (ε' / 16) ∧
      1 ≤ (N : ℝ) ^ (ε' / 16) ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε' / 16 / 2)) ^ 2 = (N : ℝ) ^ (-2 / 3 + ε' / 16) ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε' / 16 / 2)) ^ 2 ≤ edgeTau0 τ ∧
      (rlK (rlC1 τ) (rlC2 τ) + 1) * (N : ℝ) ^ (ε' / 16) + 1 ≤
        N * rlC1 τ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε' / 16 / 2)) ^ 3 / 4 ∧
      128 * rlK (rlC1 τ) (rlC2 τ) ^ 3 * ((N : ℝ) ^ (ε' / 16)) ^ 3 ≤
        rlC1 τ ^ 2 * ((N : ℝ) ^ (2 * (ε' / 16))) ^ 3 ∧
      8 * rlK (rlC1 τ) (rlC2 τ) * (N : ℝ) ^ (ε' / 16) *
          ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε' / 16 / 2)) ^ 6 * (N : ℝ) ^ 2 ≤
        ((N : ℝ) ^ (2 * (ε' / 16))) ^ 3 ∧
      rlL (rlC1 τ) (rlC2 τ) * (N : ℝ) ^ (ε' / 16) ≤ (N : ℝ) ^ (2 * (ε' / 16)) ∧
      2 * (N : ℝ) ^ (2 * (ε' / 16)) + (N : ℝ) ^ (ε' / 8) *
          (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) +
          2 * (2 * τ⁻¹ * (1 + τ⁻¹) + 1) ≤ (N : ℝ) ^ ε' ∧
      (N : ℝ) ^ ε' * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ τ / 4 ∧
      (N : ℝ) ^ (ε' / 8) *
          (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(2 / 3 : ℝ)) < (N : ℝ) ^ (-2 / 3 + ε' / 2) ∧
      (N : ℝ) ^ (2 * (ε' / 16)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) + (N : ℝ) ^ (-2 / 3 + ε' / 16) +
          (N : ℝ) ^ (-2 / 3 + ε' / 2) ≤ (N : ℝ) ^ ε' * (N : ℝ) ^ (-(2 / 3 : ℝ)) ∧
      (N : ℝ) ^ (-2 / 3 + ε' / 2) ≤ edgeTau' τ ∧
      3 / 2 * (N : ℝ) ^ (-2 / 3 + ε' / 2) ≤ edgec2 τ * edgecx τ ^ 2 / 144 ∧
      2 * (N : ℝ) ^ (-2 / 3 + ε' / 4) ≤ (N : ℝ) ^ (-2 / 3 + ε' / 2) ∧
      2 * (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-2 / 3 + ε' / 2) ∧
      288 * (N : ℝ) ^ (2 * (ε' / 16)) ≤ edgecx τ ^ 2 * (N * (N : ℝ) ^ (-2 / 3 + ε' / 2)) ∧
      2 ≤ N * (N : ℝ) ^ (-2 / 3 + ε' / 2) ∧
      C₁ / N ≤ (N : ℝ) ^ (-2 / 3 + ε' / 16)

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- The exponent rows of the edge piece hold for `N` large. -/
private lemma rl_edge_num {τ ε' C₁ τ₂ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε' : 0 < ε')
    (hε'h : ε' ≤ 1 / 2) (hτ₂ : 0 < τ₂) (hτ₂4 : τ₂ ≤ 1 / 4) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → rlEdgeNum τ ε' C₁ τ₂ N := by
  obtain ⟨ht'0, ht0e, -⟩ := rl_tau_facts hτ hτ1
  have hτ0 : 0 < edgeTau0 τ := by linarith
  have hc₁ := rl_C1_pos hτ
  set cf := rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16) with hcf
  have hcf0 : 0 < cf := by rw [hcf]; positivity
  set Q := (min cf (1 / 2)) ^ (-(1 / 3 : ℝ)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hcx0 : 0 < edgecx τ := by unfold edgecx; have := Real.sqrt_pos.2 hτ; positivity
  have hc20 : 0 < edgec2 τ := (rl_C_pos hτ).2
  obtain ⟨N1, e1⟩ := rl_ev (3 / cf) (a := ε' / 32) (b := 1) (by linarith)
  obtain ⟨N2, e2⟩ := rl_ev (5 / 2) (a := ε' / 32) (b := ε' / 16) (by linarith)
  obtain ⟨N3, e3⟩ := rl_num (c₁ := rlC1 τ) (c₂ := rlC2 τ) hc₁ hτ0 (ε := 2 * (ε' / 16))
    (ε₁ := ε' / 16) (by positivity) le_rfl (by linarith)
  obtain ⟨N4, e4⟩ := rl_ev (2 + Q + 2 * (Ca + 1)) (a := ε' / 2) (b := ε') (by linarith)
  obtain ⟨N5, e5⟩ := rl_ev_small (c := τ / 4) (a := ε' - 2 / 3) (by positivity) (by linarith)
  obtain ⟨N6, e6⟩ := rl_ev (2 * Q) (a := ε' / 8) (b := ε' / 2) (by linarith)
  obtain ⟨N7, e7⟩ := rl_ev 3 (a := ε' / 2) (b := ε') (by linarith)
  obtain ⟨N8, e8⟩ := rl_ev_small (c := edgeTau' τ) (a := -2 / 3 + ε' / 2) ht'0 (by linarith)
  obtain ⟨N9, e9⟩ := rl_ev_small (c := edgec2 τ * edgecx τ ^ 2 / 216) (a := -2 / 3 + ε' / 2)
    (by positivity) (by linarith)
  obtain ⟨N10, e10⟩ := rl_ev 2 (a := -2 / 3 + ε' / 4) (b := -2 / 3 + ε' / 2) (by linarith)
  obtain ⟨N11, e11⟩ := rl_ev 2 (a := -1 + τ₂) (b := -2 / 3 + ε' / 2) (by linarith)
  obtain ⟨N12, e12⟩ := rl_ev (288 / edgecx τ ^ 2) (a := 2 * (ε' / 16)) (b := 1 / 3 + ε' / 2)
    (by linarith)
  obtain ⟨N13, e13⟩ := rl_ev 2 (a := 0) (b := 1 / 3 + ε' / 2) (by linarith)
  obtain ⟨N14, e14⟩ := rl_ev |C₁| (a := -1) (b := -2 / 3 + ε' / 16) (by linarith)
  refine ⟨max (max (max (max N1 N2) (max N3 N4)) (max (max N5 N6) (max N7 N8)))
    (max (max (max N9 N10) (max N11 N12)) (max (max N13 N14) 2)), fun N hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩, ⟨⟨h9, h10⟩, h11, h12⟩, ⟨h13, h14⟩, hN2⟩ := hN
  unfold rlEdgeNum
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : 0 < N := by omega
  have hpow : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hN1r h
  have hone : ∀ a : ℝ, 0 ≤ a → 1 ≤ (N : ℝ) ^ a := fun a h => Real.one_le_rpow hN1r h
  have f1 := e1 N h1
  have f2 := e2 N h2
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := e3 N h3
  have f4 := e4 N h4
  have f5 := e5 N h5
  have f6 := e6 N h6
  have f7 := e7 N h7
  have f8 := e8 N h8
  have f9 := e9 N h9
  have f10 := e10 N h10
  have f11 := e11 N h11
  have f12 := e12 N h12
  have f13 := e13 N h13
  have f14 := e14 N h14
  rw [Real.rpow_one] at f1
  rw [Real.rpow_zero, mul_one] at f13
  have hδ1 := hone (ε' / 32) (by positivity)
  have hy2 : (N : ℝ) ^ (-2 / 3 + ε' / 2) = (N : ℝ) ^ (ε' / 2) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [rl_rpow_mul hN0]; ring_nf
  have hNy2 : (N : ℝ) * (N : ℝ) ^ (-2 / 3 + ε' / 2) = (N : ℝ) ^ (1 / 3 + ε' / 2) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
    rw [rl_rpow_mul hN0]; ring_nf
  have hn23 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  refine ⟨hN2, ?_, ?_, g1, g2, g3, g4, g5, g6, g7, ?_, ?_, ?_, ?_, f8, ?_, f10, f11, ?_, ?_, ?_⟩
  · have h3 : 3 * (N : ℝ) ^ (ε' / 32) ≤ N * cf := by
      have := mul_le_mul_of_nonneg_left f1 hcf0.le
      rw [show cf * (3 / cf * (N : ℝ) ^ (ε' / 32)) = 3 * (N : ℝ) ^ (ε' / 32) by field_simp] at this
      linarith
    rw [← hcf]
    linarith
  · linarith
  · have a1 := hpow (2 * (ε' / 16)) (ε' / 2) (by linarith)
    have a2 := hpow (ε' / 8) (ε' / 2) (by linarith)
    have a3 := hone (ε' / 2) (by positivity)
    have b2 := mul_le_mul_of_nonneg_right a2 hQ0
    have b3 : 2 * (Ca + 1) ≤ 2 * (Ca + 1) * (N : ℝ) ^ (ε' / 2) := by
      have : 0 ≤ 2 * (Ca + 1) := by positivity
      nlinarith
    linarith
  · rw [rl_rpow_mul hN0, show ε' + -(2 / 3 : ℝ) = ε' - 2 / 3 by ring]; exact f5
  · rw [hy2]
    have b1 : (N : ℝ) ^ (ε' / 8) * Q ≤ (N : ℝ) ^ (ε' / 2) / 2 := by linarith
    have b2 := mul_le_mul_of_nonneg_right b1 hn23.le
    have b3 : 0 < (N : ℝ) ^ (ε' / 2) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    linarith
  · rw [hy2, show (N : ℝ) ^ (-2 / 3 + ε' / 16) = (N : ℝ) ^ (ε' / 16) * (N : ℝ) ^ (-(2 / 3 : ℝ))
      by rw [rl_rpow_mul hN0]; ring_nf]
    have a1 := hpow (2 * (ε' / 16)) (ε' / 2) (by linarith)
    have a2 := hpow (ε' / 16) (ε' / 2) (by linarith)
    have b : (N : ℝ) ^ (2 * (ε' / 16)) + (N : ℝ) ^ (ε' / 16) + (N : ℝ) ^ (ε' / 2) ≤
        (N : ℝ) ^ ε' := by linarith
    have := mul_le_mul_of_nonneg_right b hn23.le
    linarith
  · linarith
  · rw [hNy2]
    have := mul_le_mul_of_nonneg_left f12 (by positivity : (0 : ℝ) ≤ edgecx τ ^ 2)
    rw [show edgecx τ ^ 2 * (288 / edgecx τ ^ 2 * (N : ℝ) ^ (2 * (ε' / 16))) =
      288 * (N : ℝ) ^ (2 * (ε' / 16)) by field_simp] at this
    exact this
  · rw [hNy2]; exact f13
  · rw [Real.rpow_neg_one] at f14
    have : C₁ / N ≤ |C₁| * (N : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    linarith

/-- `R = #{σ_i > 0}/N = M/N` for positive `σ`. -/
private lemma rl_massRatio {σ : Fin M → ℝ} (hσ : ∀ j, 0 < σ j) :
    massRatio N σ = (M : ℝ) / N := by
  unfold massRatio
  rw [Finset.filter_true_of_mem (fun i _ => hσ i), Finset.card_univ, Fintype.card_fin]

/-- `0 ∈ supp ϱ` when `M < N` (the atom `(1 − M/N) δ₀`). -/
private lemma rl_zero_mem_supp {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (hMN : M < N) : (0 : ℝ) ∈ (varrho N σ).support := by
  obtain ⟨hN, hM, -⟩ := rl_facts hda
  have hz := (Ni_sum N σ hσ hN hM).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hMNr : (M : ℝ) < N := by exact_mod_cast hMN
  have hpos : 0 < (varrho N σ {0}).toReal := by
    have h1 : (0 : ℝ) < max ((N : ℝ) - M) 0 := lt_max_of_lt_left (by linarith)
    rw [← hz] at h1
    exact (mul_pos_iff_of_pos_left hN0).1 h1
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h0 : ({0} : Set ℝ) ⊆ U := Set.singleton_subset_iff.2 (mem_of_mem_nhds hU)
  exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 hpos).1 (measure_mono h0)

/-- An event of probability `≥ 1 − N^{−D−2}` has probability `≥ 1 − N^{−D−1}`, `N ≥ 1`. -/
private lemma rl_hp_succ {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A : Set Ω}
    (hN : 1 ≤ N) (h : HighProbAt N (D + 1 + 1) A) : HighProbAt N (D + 1) A := by
  unfold HighProbAt at *
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

set_option maxHeartbeats 16000000 in
-- many linear-arithmetic steps over a large context
/-- Theorem 11.3 near a regular edge `k`, at one `N`: from the partner edge of `N − 1`, the count
comparisons `n_{N−1}` against `n_N`, Theorem 3.14 (iii), the gap lemma below `a_k` and the
anisotropic law at `z₁ = a_k − y₂ + i y₂/2` (all at level `D + 2`), and the exponent rows. -/
private lemma rl_edge_fixed {τ ε' C₁ τ₂ D : ℝ} {C : ℕ → ℝ} {N : ℕ} {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {M : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτ₂ : 0 < τ₂)
    (hτ₂4 : τ₂ ≤ 1 / 4) (hτ₂C : τ₂ ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹)
    (hm : IsModel τ C M N Sig X) (hk : RegularEdge τ N (specOf Sig) k)
    (hnum : rlEdgeNum τ ε' C₁ τ₂ N)
    (hpred : ∃ l, l % 2 = k % 2 ∧
      |edgeVal (N - 1) (specOf Sig) l - edgeVal N (specOf Sig) k| ≤ C₁ / N ∧
      RegularEdge (τ / 2) (N - 1) (specOf Sig) l)
    (hsub : ∀ x, τ / 2 ≤ x →
      |nClass (N - 1) (specOf Sig) x - nClass N (specOf Sig) x| ≤ (N : ℝ) ^ (ε' / 32))
    (hgapc : ∀ E, τ / 2 ≤ E → τ / 4 ≤ Metric.infDist E (varrho N (specOf Sig)).support →
      (∃ x ∈ (varrho N (specOf Sig)).support, x < E) →
      nClass (N - 1) (specOf Sig) E = nClass N (specOf Sig) E)
    (hrig : HighProbAt N (D + 1 + 1) {ω | ∀ i, 1 ≤ i →
        i ≤ bandNat N (specOf Sig) ((k + 1) / 2) →
        gammaBand N (specOf Sig) ((k + 1) / 2) i ∈
          Set.Icc (edgeVal N (specOf Sig) k - edgeTau' τ / 2)
            (edgeVal N (specOf Sig) k + edgeTau' τ / 2) →
        |lamBand Sig (X ω) ((k + 1) / 2) i - gammaBand N (specOf Sig) ((k + 1) / 2) i| ≤
          rigBound N (bandNat N (specOf Sig) ((k + 1) / 2)) i (ε' / 8)})
    (hgw : ∀ W : Set ℝ, W ⊆ Set.Ici (τ / 2) →
      (∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) →
        Metric.infDist (edgeVal N (specOf Sig) l) W ≤ τ / 4 →
        RegularEdge (τ / 2) N (specOf Sig) l) →
      HighProbAt N (D + 1 + 1) {ω | ∀ j : Fin N, specOf (QN Sig (X ω)) j ∈ W →
        Metric.infDist (specOf (QN Sig (X ω)) j) (varrho N (specOf Sig)).support <
          (N : ℝ) ^ (-2 / 3 + ε' / 4)})
    (hlaw : AnisotropicLawAt N (ε' / 16) (D + 1 + 1) Sig X
      (edgeDomain τ₂ (edgeTau' τ) N (specOf Sig) k)) :
    HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf Sig) l →
        gammaBand (N - 1) (specOf Sig) l i ∈
          Set.Icc (edgeVal N (specOf Sig) k - edgeTau' τ / 4)
            (edgeVal N (specOf Sig) k + edgeTau' τ / 4) →
        |lamDotBand Sig (X ω) l i - gammaBand (N - 1) (specOf Sig) l i| ≤
          rigBound N (bandNat (N - 1) (specOf Sig) l) i ε'} := by
  unfold rlEdgeNum at hnum
  obtain ⟨hN2, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17,
    n18, n19, n20⟩ := hnum
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hN10 : 0 < N - 1 := by omega
  obtain ⟨ht'0, ht0e, -⟩ := rl_tau_facts hτ hτ1
  have ht0 := rl_tau0_le hτ hτ1
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := rl_sigma_pos hm
  have hSigPD := hm.sigma.posDef
  have hSig := hSigPD.isHermitian
  have hdaN1 := rl_da_pred hda hN2
  obtain ⟨hN0, hM0, -⟩ := rl_facts hda
  have hk1 := hk.1
  have hk2 := hk.2.1
  have hak : τ ≤ edgeVal N (specOf Sig) k := hk.2.2.1
  have haC := (rl_edge_mem hda hk1 hk2).2
  set y := (N : ℝ) ^ (-(1 / 3 : ℝ) + ε' / 16 / 2) with hy
  set y₂ := (N : ℝ) ^ (-2 / 3 + ε' / 2) with hy₂
  set y₃ := (N : ℝ) ^ (-2 / 3 + ε' / 4) with hy₃
  have hy0 : 0 < y := by positivity
  have hy₂0 : 0 < y₂ := by positivity
  have hy₃0 : 0 < y₃ := by positivity
  have hyy : y ^ 2 ≤ edgeTau0 τ := n5
  have hC1y : C₁ / N ≤ y ^ 2 := by rw [n4]; exact n20
  set σ := specOf Sig with hσdef
  set a := edgeVal N σ k with ha
  -- the partner edge of `N − 1`
  obtain ⟨l', hl'par, hl'a, hl'reg⟩ := hpred
  have hpartner : ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ → ∀ x,
      edgeVal (N - 1) σ (2 * l) < x → x < edgeVal (N - 1) σ (2 * l - 1) →
      |x - a| ≤ edgeTau0 τ / 16 → (l' % 2 = 1 → l' = 2 * l - 1) ∧ (l' % 2 = 0 → l' = 2 * l) :=
    fun l hl1 hlp x hx1 hx2 hxa => rl_partner hdaN1 hl1 hlp hl'reg hx1 hx2 hxa hl'a
      (by linarith)
  have hne : (varrho N σ).support.Nonempty := by
    obtain ⟨hNn, -, hS⟩ := rl_facts hda
    have hp := (card_innerCrit N σ hda.nonneg hNn hS).2
    have h1 := rl_anti hda (i := 1) (j := k) le_rfl hk1 hk2
    have h2 := rl_anti hda (i := 1) (j := 2 * numBands N σ) le_rfl (by omega) le_rfl
    have h3 := edgeVal_band_lt N σ hda.nonneg hNn hS (k := 1) le_rfl hp
    refine ⟨edgeVal N σ 1, rl_mem_supp hda (k := 1) le_rfl hp (by linarith)
      (by have := rl_anti hda (i := 2 * 1) (j := 2 * 1) (by norm_num) le_rfl (by omega)
          linarith) (by simp)⟩
  -- the three events
  have ht'τ : edgeTau' τ ≤ τ / 64 := by linarith
  set W := Set.Icc (a - τ / 8) (a - y₃) with hW
  have hWsub : W ⊆ Set.Ici (τ / 2) := fun x hx => by
    simp only [Set.mem_Ici]; linarith [hx.1]
  have hWreg : ∀ l, 1 ≤ l → l ≤ 2 * numBands N σ → Metric.infDist (edgeVal N σ l) W ≤ τ / 4 →
      RegularEdge (τ / 2) N σ l := by
    intro l hl1 hl2 hl
    rcases eq_or_ne l k with rfl | hlk
    · exact regularEdge_mono hk (by linarith)
    · exfalso
      have hy3W : y₃ ≤ τ / 8 := by linarith
      have hWne : W.Nonempty := ⟨a - y₃, by linarith, le_rfl⟩
      obtain ⟨z, hz, hdz⟩ := (Metric.infDist_lt_iff hWne).1
        (lt_of_le_of_lt hl (by linarith : τ / 4 < τ / 2))
      have hsep := hk.2.2.2.1 l hl1 hl2 hlk
      rw [← ha] at hsep
      rw [Real.dist_eq] at hdz
      have h1 := abs_sub_le a z (edgeVal N σ l)
      have h2 : |a - z| ≤ τ / 2 := by
        rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
      rw [abs_sub_comm z (edgeVal N σ l)] at h1
      linarith
  have hEv2 := hgw W hWsub hWreg
  set E₁ := a - y₂ with hE₁
  set δ₁ := y₂ / 2 with hδ₁
  set z₁ : ℂ := (E₁ : ℂ) + δ₁ * Complex.I with hz₁
  have hz₁re : z₁.re = E₁ := by simp [hz₁]
  have hz₁im : z₁.im = δ₁ := by simp [hz₁]
  have hE₁τ : τ / 2 ≤ E₁ := by linarith
  have hτ₂τ : τ₂ ≤ τ / 2 := by
    have h1 : τ / 2 ≥ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ := by
      rw [ge_iff_le, inv_le_comm₀ (by positivity) (by positivity)]
      have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
      rw [this]
      have : 0 ≤ 2 * τ⁻¹ * τ⁻¹ := by positivity
      nlinarith
    linarith
  have hτ₂inv : 2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ τ₂⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hτ₂]; exact hτ₂C
  have hz₁dom : z₁ ∈ edgeDomain τ₂ (edgeTau' τ) N σ k := by
    refine ⟨⟨by rw [hz₁im]; positivity, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := Complex.abs_re_le_norm z₁
      rw [hz₁re, abs_of_pos (by linarith)] at this
      linarith
    · rw [hz₁re, abs_of_pos (by linarith)]; linarith
    · rw [hz₁im]; linarith
    · rw [hz₁im]
      have : (4 : ℝ) ≤ τ₂⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hτ₂]; linarith
      linarith
    · rw [hz₁re]; constructor <;> linarith
  set v := Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)) with hv
  have hEv3 : HighProbAt N (D + 1 + 1) {ω | ‖testBilin v (lawMat Sig (X ω) z₁) v‖ ≤
      (N : ℝ) ^ (ε' / 16) * (Psi N σ z₁ * testNorm v * testNorm v)} := by
    have h := hlaw z₁ hz₁dom v v
    unfold DomAt at h
    unfold HighProbAt
    have hset : {ω | ‖testBilin v (lawMat Sig (X ω) z₁) v‖ ≤
        (N : ℝ) ^ (ε' / 16) * (Psi N σ z₁ * testNorm v * testNorm v)}ᶜ =
        {ω | (N : ℝ) ^ (ε' / 16) * (Psi N (specOf Sig) z₁ * testNorm v * testNorm v) <
          ‖testBilin v (lawMat Sig (X ω) z₁) v‖} := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      exact Iff.rfl
    rw [hset]
    exact h
  have hEv1 := rl_hp_succ (by omega) hrig
  refine rl_hp_mono (rl_hp_inter hN2 hEv1 (rl_hp_inter hN2 hEv2 hEv3)) ?_
  rintro ω ⟨h1, h2, h3⟩
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  intro l hl1 hlp i hi hiN hE
  have hcase_dist : ∀ {r x : ℝ}, 0 ≤ r → r ≤ x → (∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x) →
      r ≤ Metric.infDist x (varrho N σ).support :=
    fun hr hx hb => rl_dist hda hr hx hne hb
  rcases Nat.even_or_odd' k with ⟨m, hkm | hkm⟩
  · -- the lower edge `a_{2m}` of the band `m`
    subst hkm
    have hm1 : 1 ≤ m := by omega
    have hmp : m ≤ numBands N σ := by omega
    rw [show (2 * m + 1) / 2 = m by omega] at h1
    have hpart : ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ → ∀ x,
        edgeVal (N - 1) σ (2 * l) < x → x < edgeVal (N - 1) σ (2 * l - 1) →
        |x - a| ≤ edgeTau0 τ / 16 →
        a - y ^ 2 ≤ edgeVal (N - 1) σ (2 * l) ∧ cumCount (N - 1) σ l ≤ cumCount N σ m := by
      intro l hl1 hlp x hx1 hx2 hxa
      have hl'e : l' = 2 * l := (hpartner l hl1 hlp x hx1 hx2 hxa).2 (by omega)
      rw [hl'e] at hl'a
      have hlo : a - y ^ 2 ≤ edgeVal (N - 1) σ (2 * l) := by
        rw [abs_le] at hl'a; linarith [hl'a.1]
      refine ⟨hlo, ?_⟩
      have hcl := (rl_cum hdaN1 hσ hl1 hlp).1
      by_cases hcase : m < numBands N σ ∨ M < N
      · obtain ⟨Es, hEs1, hEs2, hEs3⟩ : ∃ Es : ℝ, τ / 2 ≤ Es ∧ Es ≤ a - y ^ 2 ∧
            nClass (N - 1) σ Es = cumCount N σ m := by
          rcases lt_or_eq_of_le hmp with hlt | heq
          · have hsep := rl_sep_dn hda hm1 hlt hk
            have hb0 := edgeVal_band_lt N σ hda.nonneg hN0 (rl_facts hda).2.2
              (k := m + 1) (by omega) (by omega)
            rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hb0
            have hb00 := (rl_edge_mem hda (k := 2 * (m + 1)) (by omega) (by omega)).1
            refine ⟨a - τ / 2, by linarith, by linarith, ?_⟩
            rw [hgapc (a - τ / 2) (by linarith) ?_ ?_]
            · exact rl_n_gap_dn hda hσ hm1 hmp (by linarith) (by linarith)
                (fun _ => by linarith)
            · have := hcase_dist (r := τ / 2) (x := a - τ / 2) (by linarith) (by linarith)
                fun l'' hl''1 hl''2 => by
                  rcases le_or_gt l'' m with hle | hgt
                  · left
                    have := rl_anti hda (i := 2 * l'') (j := 2 * m) (by omega) (by omega)
                      (by omega)
                    linarith
                  · right
                    have := rl_anti hda (i := 2 * m + 1) (j := 2 * l'' - 1) (by omega)
                      (by omega) (by omega)
                    linarith
              linarith
            · have hbm1 : edgeVal N σ (2 * (m + 1)) ≤ edgeVal N σ (2 * m + 1) :=
                rl_anti hda (i := 2 * m + 1) (j := 2 * (m + 1)) (by omega) (by omega) (by omega)
              have hmem := rl_mem_supp hda (k := m + 1) (by omega) (by omega) (by linarith) hbm1
                (by rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega])
              exact ⟨_, hmem, by linarith⟩
          · have hMN : M < N := hcase.resolve_left (by omega)
            refine ⟨a / 2, by linarith, by linarith, ?_⟩
            rw [hgapc (a / 2) (by linarith) ?_ ⟨0, rl_zero_mem_supp hda hσ hMN, by linarith⟩]
            · exact rl_n_gap_dn hda hσ hm1 hmp (by linarith) (by linarith)
                (fun h => absurd h (by omega))
            · have := hcase_dist (r := a / 2) (x := a / 2) (by linarith) le_rfl
                fun l'' hl''1 hl''2 => by
                  left
                  have := rl_anti hda (i := 2 * l'') (j := 2 * m) (by omega) (by omega)
                    (by omega)
                  linarith
              linarith
        have hdl : 0 < edgeVal (N - 1) σ (2 * l) := by linarith
        have hn1 := (nClass_edgeVal hdaN1 hl1 hlp).2 hdl
        have hmono := rl_nClass_anti hdaN1.nonneg hN10 (show Es ≤ edgeVal (N - 1) σ (2 * l) by
          linarith)
        have : (cumCount (N - 1) σ l : ℝ) ≤ cumCount N σ m := by linarith
        exact_mod_cast this
      · push Not at hcase
        have hkp' : m = numBands N σ := le_antisymm hmp hcase.1
        have hcp : cumCount N σ m = min M N := by
          have := (rl_cum hda hσ hm1 hmp).2
          rwa [← hkp'] at this
        rw [hcp, min_eq_right hcase.2]
        have := min_le_right M (N - 1)
        omega
    have hsec : (m < numBands N σ ∨ M < N) →
        eigCount (QN Sig (Xdot (X ω))) (edgeVal N σ (2 * m) - y₂) =
          eigCount (QN Sig (X ω)) (edgeVal N σ (2 * m) - y₂) := by
      intro hcase
      have hxneg : xCrit N σ (2 * m) < 0 := rl_xCrit_neg hda hm1 hmp (hcase.imp id fun h => by
        rw [rl_massRatio hσ, div_lt_one hNpos]; exact_mod_cast h)
      have hgapB : ∀ j, δ₁ ≤ |specOf (QN Sig (X ω)) j - E₁| := by
        intro j
        set lam := specOf (QN Sig (X ω)) j with hlam
        rcases lt_or_ge lam (a - τ / 8) with hlo | hlo
        · rw [abs_of_neg (by linarith)]; linarith
        · rcases lt_or_ge (a - y₃) lam with hhi | hhi
          · rw [abs_of_pos (by linarith)]; linarith
          · exfalso
            have hd := h2 j ⟨hlo, hhi⟩
            have := hcase_dist (r := y₃) (x := lam) hy₃0.le (by linarith)
              fun l'' hl''1 hl''2 => by
                rcases le_or_gt l'' m with hle | hgt
                · left
                  have := rl_anti hda (i := 2 * l'') (j := 2 * m) (by omega) (by omega)
                    (by omega)
                  linarith
                · right
                  have hsep := rl_sep_dn hda hm1 (by omega) hk
                  have := rl_anti hda (i := 2 * m + 1) (j := 2 * l'' - 1) (by omega)
                    (by omega) (by omega)
                  linarith
            linarith
      have hza : ‖z₁ - (edgeVal N σ (2 * m) : ℂ)‖ ≤ 3 / 2 * y₂ := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have e1 : (z₁ - (edgeVal N σ (2 * m) : ℂ)).re = -y₂ := by
          rw [Complex.sub_re, hz₁re, Complex.ofReal_re]; ring
        have e2 : (z₁ - (edgeVal N σ (2 * m) : ℂ)).im = y₂ / 2 := by
          rw [Complex.sub_im, hz₁im, Complex.ofReal_im]; ring
        rw [e1, e2, abs_neg, abs_of_pos hy₂0, abs_of_pos (by positivity)]
        linarith
      have hza' : ‖z₁ - (edgeVal N σ (2 * m) : ℂ)‖ ≤ edgeTau0 τ := by
        have : 3 / 2 * y₂ ≤ edgeTau0 τ := by linarith
        exact hza.trans this
      obtain ⟨hs1, hs2⟩ := rl_sign hda hτ1 hk hxneg (by rw [hz₁im]; positivity) hza'
      have hNim : 1 ≤ (N : ℝ) * z₁.im := by rw [hz₁im, hδ₁]; linarith
      have hpsi := rl_psi_le (N := N) (σ := σ) hs2 hNim
      have hcx0 : 0 < edgecx τ := by unfold edgecx; have := Real.sqrt_pos.2 hτ; positivity
      have hc20 : 0 < edgec2 τ := (rl_C_pos hτ).2
      have hq1 : 4 * √(‖z₁ - (edgeVal N σ (2 * m) : ℂ)‖ / edgec2 τ) ≤ edgecx τ / 3 := by
        have : ‖z₁ - (edgeVal N σ (2 * m) : ℂ)‖ / edgec2 τ ≤ (edgecx τ / 12) ^ 2 := by
          rw [div_le_iff₀ hc20]; nlinarith
        have := Real.sqrt_le_sqrt this
        rw [Real.sqrt_sq (by positivity)] at this
        linarith
      have hq2 : 2 * ((N : ℝ) ^ (ε' / 16) * (2 * √(1 / ((N : ℝ) * z₁.im)))) ≤ edgecx τ / 3 := by
        rw [hz₁im]
        have hsq : (N : ℝ) ^ (2 * (ε' / 16)) = ((N : ℝ) ^ (ε' / 16)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
        set P := (N : ℝ) ^ (ε' / 16) with hP
        have hP0 : 0 ≤ P := by positivity
        have hNd : 0 < (N : ℝ) * (y₂ / 2) := by positivity
        have hsq2 : (4 * P * √(1 / ((N : ℝ) * (y₂ / 2)))) ^ 2 =
            16 * P ^ 2 / ((N : ℝ) * (y₂ / 2)) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
        have hle : (4 * P * √(1 / ((N : ℝ) * (y₂ / 2)))) ^ 2 ≤ (edgecx τ / 3) ^ 2 := by
          rw [hsq2, div_le_iff₀ hNd]
          rw [hsq] at n18
          nlinarith
        have hX0 : 0 ≤ 4 * P * √(1 / ((N : ℝ) * (y₂ / 2))) := by positivity
        have := (pow_le_pow_iff_left₀ hX0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hle
        linarith
      refine rl_secular hSigPD (X ω) hN0 (by linarith) (by positivity) hgapB h3 ?_
      have hP0 : 0 ≤ (N : ℝ) ^ (ε' / 16) := by positivity
      have := mul_le_mul_of_nonneg_left hpsi hP0
      linarith
    have hfin := n10
    exact rl_edge_dn_det (k := m) (ε₁ := ε' / 8) (δ := ε' / 32) (s := (N : ℝ) ^ (ε' / 16))
      (y := y) (Ec := (N : ℝ) ^ (2 * (ε' / 16))) (y₂ := y₂) hda hσ hSig hN2 hτ1 hm1 hmp hk hsub
      hpart h1 hsec n1 n2 n3 hy0 hyy n6 n7 n8 n9 hfin n11 n12 (by rw [n4]; exact n13)
      (by linarith) hl1 hlp hi hiN hE
  · -- the upper edge `a_{2m+1}` of the band `m + 1`
    subst hkm
    have e1 : 2 * m + 1 = 2 * (m + 1) - 1 := by omega
    have hmp : m + 1 ≤ numBands N σ := by omega
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega] at h1
    have hk' : RegularEdge τ N σ (2 * (m + 1) - 1) := by rw [← e1]; exact hk
    have hgap : nClass (N - 1) σ (a + τ / 2) = nClass N σ (a + τ / 2) := by
      refine hgapc (a + τ / 2) (by linarith) ?_ ⟨a, ?_, by linarith⟩
      · have := hcase_dist (r := τ / 2) (x := a + τ / 2) (by linarith) (by linarith)
          fun l'' hl''1 hl''2 => by
            rcases le_or_gt (m + 1) l'' with hle | hgt
            · right
              have := rl_anti hda (i := 2 * m + 1) (j := 2 * l'' - 1) (by omega) (by omega)
                (by omega)
              linarith
            · left
              have hsep := rl_sep_up hda (k := m + 1) (by omega) hk'
              rw [← e1, show 2 * (m + 1) - 2 = 2 * m by omega] at hsep
              have := rl_anti hda (i := 2 * l'') (j := 2 * m) (by omega) (by omega) (by omega)
              linarith
        linarith
      · refine rl_mem_supp hda (k := m + 1) (by omega) hmp (by linarith) ?_ (by rw [← e1])
        have := rl_anti hda (i := 2 * m + 1) (j := 2 * (m + 1)) (by omega) (by omega)
          (by omega)
        linarith
    have hpart : ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ → ∀ x,
        edgeVal (N - 1) σ (2 * l) < x → x < edgeVal (N - 1) σ (2 * l - 1) →
        |x - edgeVal N σ (2 * (m + 1) - 1)| ≤ edgeTau0 τ / 16 →
        edgeVal (N - 1) σ (2 * l - 1) ≤ edgeVal N σ (2 * (m + 1) - 1) + y ^ 2 := by
      intro l hl1 hlp x hx1 hx2 hxa
      rw [← e1] at hxa ⊢
      have hl'e : l' = 2 * l - 1 := (hpartner l hl1 hlp x hx1 hx2 hxa).1 (by omega)
      rw [hl'e] at hl'a
      rw [abs_le] at hl'a; linarith [hl'a.2]
    have hfin : (N : ℝ) ^ (2 * (ε' / 16)) + (N : ℝ) ^ (ε' / 8) *
        (min (rlC1 τ * √(edgeTau0 τ / 16) * (edgeTau0 τ / 16)) (1 / 2)) ^ (-(1 / 3 : ℝ)) +
        2 * (2 * τ⁻¹ * (1 + τ⁻¹) + 1) ≤ (N : ℝ) ^ ε' := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ (2 * (ε' / 16)) := by positivity
      linarith
    exact rl_edge_up_det (k := m + 1) (ε₁ := ε' / 8) (δ := ε' / 32) (s := (N : ℝ) ^ (ε' / 16))
      (y := y) (Ec := (N : ℝ) ^ (2 * (ε' / 16))) hda hσ hSig hN2 hτ1 (by omega) hmp hk' hsub hgap
      hpart h1 n1 n2 n3 hy0 hyy n6 n7 n8 n9 hfin n11 hl1 hlp hi hiN hE

/-- Rigidity of `λ̇` near a regular edge `k` (`N − 1` classical locations in the window
`[a_k − τ'/4, a_k + τ'/4]`, `τ' = edgeTau' τ`), under (T_diag). -/
theorem rigidity_dot_edge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf Sig) l →
        gammaBand (N - 1) (specOf Sig) l i ∈
          Set.Icc (edgeVal N (specOf Sig) k - edgeTau' τ / 4)
            (edgeVal N (specOf Sig) k + edgeTau' τ / 4) →
        |lamDotBand Sig (X ω) l i - gammaBand (N - 1) (specOf Sig) l i| ≤
          rigBound N (bandNat (N - 1) (specOf Sig) l) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k hm _ => absurd hm.tau_le_one hτ1⟩
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'h : ε' ≤ 1 / 2 := min_le_right _ _
  set τ₂ := min (1 / 4) (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ with hτ₂
  have hτ₂0 : 0 < τ₂ := lt_min (by norm_num) (by positivity)
  have hτ₂4 : τ₂ ≤ 1 / 4 := min_le_left _ _
  have hτ₂C : τ₂ ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ := min_le_right _ _
  have hτ₂τ : τ₂ ≤ τ := by
    refine hτ₂C.trans ?_
    rw [inv_le_comm₀ (by positivity) hτ]
    have : 0 ≤ 2 * τ⁻¹ * τ⁻¹ := by positivity
    nlinarith [inv_pos.mpr hτ]
  obtain ⟨C₁, Na, hpred⟩ := edge_pred τ hτ
  obtain ⟨Nb, hsubN⟩ := nClass_pred_sub (τ / 2) (ε' / 32) (by linarith) (by positivity)
  obtain ⟨Nc, hgapN⟩ := nClass_pred_gap τ hτ
  obtain ⟨Nd, hrigN⟩ := rigidity_edge τ C (ε' / 8) (D + 1 + 1) hτ (by positivity)
  obtain ⟨Ne, hgwN⟩ := gap_window τ C (ε' / 4) (D + 1 + 1) (τ / 2) hτ (by positivity)
    (by linarith) (by linarith)
  obtain ⟨Nf, hlawN⟩ := edge_law' τ τ₂ (edgeTau' τ) C (ε' / 16) (D + 1 + 1) hτ₂0 hτ₂τ
    (edgeTau'_pos hτ) le_rfl (by positivity)
  obtain ⟨Ng, hnumN⟩ := rl_edge_num (C₁ := C₁) hτ hτ1 hε'0 hε'h hτ₂0 hτ₂4
  refine ⟨max (max (max Na Nb) (max Nc Nd)) (max (max Ne Nf) Ng),
    fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hNa, hNb⟩, hNc, hNd⟩, ⟨hNe, hNf⟩, hNg⟩ := hN
  have hnum := hnumN N hNg
  have hN2 : 2 ≤ N := hnum.1
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hda2 : DensityAssumptions (τ / 2) N (specOf Sig) := hda.mono (by linarith) (by linarith)
  have hmain := rl_edge_fixed (D := D) hτ hτ1 hτ₂0 hτ₂4 hτ₂C hm hk hnum
    (hpred N hNa M (specOf Sig) hda k hk)
    (fun x hx => hsubN N hNb M (specOf Sig) hda2 x hx)
    (fun E h1 h2 h3 => hgapN N hNc M (specOf Sig) hda E h1 h2 h3)
    (hrigN N hNd M Sig X k hm hk)
    (fun W hW hreg => hgwN N hNe M Sig X W hm hW hreg)
    (hlawN N hNf M Sig X k hm hk).1
  refine rl_hp_mono hmain fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro l hl1 hlp i hi hiN hE
  exact (hω l hl1 hlp i hi hiN hE).trans (rl_rigBound_mono (by omega) hε'ε)

/-! ## Instances: `Σ = I_{2n}`, `N = n`, Gaussian `X` (`φ = 2`, rank `Σ ≥ N`) -/

/-- `rigidity_dot_edge` at `Σ = I_{2n}`, `N = n`, Gaussian `X`, `τ = 1/20`, at the lower edge
`a₂ = (√2 − 1)²` of the single band (`k = 2 = 2p`, `M ≥ N`): every hypothesis is discharged. -/
example (ε D : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ n ≥ N₀,
    HighProbAt n D {ω | ∀ l, 1 ≤ l →
      l ≤ numBands (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l →
      gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l i ∈
        Set.Icc (edgeVal n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2 -
            edgeTau' (1 / 10 / 2) / 4)
          (edgeVal n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2 +
            edgeTau' (1 / 10 / 2) / 4) →
      |lamDotBand 1 (gaussX (2 * n) n ω) l i -
          gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l i| ≤
        rigBound n (bandNat (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l) i
          ε} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_edge (1 / 10 / 2) gaussMoment ε D (by norm_num) hε
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hm := (isModel_two hn1).mono (τ₂ := 1 / 10 / 2) (by norm_num) (by norm_num)
  refine h n (le_of_max_le_left hn) (2 * n) 1 (gaussX (2 * n) n) 2 hm ?_
  rw [specOf_one_eq]
  exact regularEdge_two (by omega) (by norm_num) le_rfl

/-- `rigidity_dot_bulk` at `Σ = I_{2n}`, `N = n`, Gaussian `X`, `τ = 1/20`,
`c(t) = min(t, 1)/50`, `τ' = 1`, the band `k = 1` (window `[a₂ + 1, a₁ − 1]`): every hypothesis
is discharged. -/
example (ε D : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ n ≥ N₀,
    HighProbAt n D {ω | ∀ l, 1 ≤ l →
      l ≤ numBands (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l →
      gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l i ∈
        Set.Icc (edgeVal n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) (2 * 1) + 1)
          (edgeVal n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) (2 * 1 - 1) - 1) →
      |lamDotBand 1 (gaussX (2 * n) n ω) l i -
          gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) l i| ≤
        (n : ℝ) ^ ε * (n : ℝ)⁻¹} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_bulk (1 / 10 / 2) 1 (fun t => min t 1 / 50) gaussMoment ε D
    (by norm_num) one_pos hε
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hm := (isModel_two hn1).mono (τ₂ := 1 / 10 / 2) (by norm_num) (by norm_num)
  refine h n (le_of_max_le_left hn) (2 * n) 1 (gaussX (2 * n) n) 1 hm ?_ (Or.inr ?_)
  · rw [specOf_one_eq]; exact regularBulk_two (by omega)
  · rw [specOf_one_eq]; exact regularEdge_two (by omega) (by norm_num) (by norm_num)

#print axioms rigidity_dot_edge
#print axioms rigidity_dot_bulk

end Anisotropic
