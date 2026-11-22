module

public import Anisotropic.Density.Boundary
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Varrho
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.GeneralT.Model
public import Anisotropic.GeneralT.Spectra
public import Anisotropic.LinAlg.Blocks

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The limit `κ ↓ 0` at fixed `N`: `m_κ → m` uniformly on compacts, the limit of `G`, and the probability limit on strict events -/

/-- The eigenvalues of `T Tᵀ` are nonnegative. -/
private theorem limit_specOf_nonneg {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    ∀ i, 0 ≤ specOf (T * Tᵀ) i := by
  have hP : (T * Tᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
  intro i
  rw [specOf_eq hP.isHermitian]
  exact hP.eigenvalues_nonneg i

/-- The eigenvalues of `Ŝ + κ P₀` are nonnegative for `κ > 0`. -/
private theorem limit_specOf_regS_nonneg {K : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (T : Matrix (Fin M) (Fin K) ℝ) : ∀ i, 0 ≤ specOf (regS κ (Tᵀ * T)) i := by
  have hP := regS_posDef hκ T
  intro i
  rw [specOf_eq hP.isHermitian]
  exact (hP.eigenvalues_pos i).le

/-- `R ≤ K / N` for `K` eigenvalues. -/
private theorem limit_massRatio_le {K : ℕ} (N : ℕ) (σ : Fin K → ℝ) :
    massRatio N σ ≤ (K : ℝ) / N := by
  unfold massRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- `m` of `Ŝ + κ P₀` tends to `m` of `Σ = T Tᵀ` uniformly on compact subsets of `ℂ₊`. -/
theorem tendstoUniformlyOn_mFun_regS {K : ℕ} (hN : 1 ≤ N) (T : Matrix (Fin M) (Fin K) ℝ)
    {L : Set ℂ} (hL : IsCompact L) (hL0 : ∀ z ∈ L, 0 < z.im) :
    TendstoUniformlyOn (fun κ z => mFun N (specOf (regS κ (Tᵀ * T))) z)
      (mFun N (specOf (T * Tᵀ))) (𝓝[>] 0) L := by
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · rw [hLe]
    exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀L, hz₀min⟩ := hL.exists_isMinOn hLne Complex.continuous_im.continuousOn
  set η := z₀.im with hη
  have hη0 : 0 < η := hL0 z₀ hz₀L
  have hηle : ∀ z ∈ L, η ≤ z.im := fun z hz => hz₀min hz
  set r := η / 2 with hr
  have hr0 : 0 < r := by positivity
  set L₁ : Set ℂ := (fun p : ℂ × ℂ => p.1 + p.2) '' (L ×ˢ Metric.closedBall 0 r) with hL₁def
  have hL₁ : IsCompact L₁ :=
    (hL.prod (isCompact_closedBall 0 r)).image (continuous_fst.add continuous_snd)
  have hmemL₁ : ∀ z ∈ L, ∀ u : ℂ, ‖u‖ ≤ r → z + u ∈ L₁ := fun z hz u hu =>
    ⟨(z, u), ⟨hz, by simpa using hu⟩, rfl⟩
  have hL₁im : ∀ y ∈ L₁, r ≤ y.im := by
    rintro _ ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
    have h1 := hηle z hz
    have h2 : |u.im| ≤ r := (Complex.abs_im_le_norm u).trans (by simpa using hu)
    simp only [Complex.add_im]
    linarith [neg_abs_le u.im]
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ := limit_specOf_nonneg T
  have hcont : ContinuousOn (mFun N σ) L₁ := fun y hy =>
    ((analyticOnNhd_mFun N σ hσ y
      (show 0 < y.im from lt_of_lt_of_le hr0 (hL₁im y hy))).continuousAt).continuousWithinAt
  have huc := hL₁.uniformContinuousOn_of_continuous hcont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := ((K - T.rank : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  set C₀ := (1 + √((K : ℝ) / N)) / η with hC₀
  have hC₀ : 0 < C₀ := by positivity
  set B := 2 * a / N with hB
  have hB0 : 0 ≤ B := by positivity
  set κ₀ := min (1 / (2 * C₀)) (min δ r / (B + 1)) with hκ₀
  have hκ₀0 : 0 < κ₀ := by
    have : 0 < min δ r := lt_min hδ hr0
    positivity
  filter_upwards [Ioo_mem_nhdsGT hκ₀0] with κ hκ z hz
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hσκ := limit_specOf_regS_nonneg hκ0 T
  have hzim := hL0 z hz
  set w := mFun N (specOf (regS κ (Tᵀ * T))) z with hw
  obtain ⟨hwim, hfw⟩ := mFun_spec N _ hσκ hzim
  rw [← hw] at hwim hfw
  -- `|m_κ(z)| ≤ C₀`
  have hwle : ‖w‖ ≤ C₀ := by
    have h1 := norm_mFun_le N _ hσκ hzim
    rw [← hw] at h1
    have hzn : η ≤ ‖z‖ := (hηle z hz).trans (Complex.im_le_norm z)
    refine h1.trans ?_
    apply div_le_div₀ (by positivity) _ hη0 hzn
    gcongr
    exact limit_massRatio_le N _
  have hκC : κ * ‖w‖ ≤ 1 / 2 := by
    have h1 : κ ≤ 1 / (2 * C₀) := hκ1.le.trans (min_le_left _ _)
    calc κ * ‖w‖ ≤ (1 / (2 * C₀)) * C₀ :=
          mul_le_mul h1 hwle (norm_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
  have h1κw : 1 / 2 ≤ ‖1 + (κ : ℂ) * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-((κ : ℂ) * w))
    rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ0, norm_one] at h
    linarith
  set c : ℂ := ((K - T.rank : ℕ) : ℂ) * κ / (N * (1 + κ * w)) with hc
  have hcle : ‖c‖ ≤ B * κ := by
    rw [hc, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ0,
      Complex.norm_natCast, Complex.norm_natCast]
    have h2 : (N : ℝ) * (1 / 2) ≤ N * ‖1 + (κ : ℂ) * w‖ :=
      mul_le_mul_of_nonneg_left h1κw hNpos.le
    calc ((K - T.rank : ℕ) : ℝ) * κ / (N * ‖1 + (κ : ℂ) * w‖)
        ≤ ((K - T.rank : ℕ) : ℝ) * κ / (N * (1 / 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = B * κ := by rw [hB, ha]; field_simp
  have hBκ : B * κ < min δ r := by
    have h1 : κ < min δ r / (B + 1) := hκ1.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hfw' : fC N σ w = z - c := by
    rw [← hfw, fC_regS N hκ0 T w]
    ring
  have hz'L₁ : z - c ∈ L₁ := by
    have := hmemL₁ z hz (-c) (by rw [norm_neg]; exact hcle.trans (hBκ.le.trans (min_le_right _ _)))
    simpa [sub_eq_add_neg] using this
  have hzL₁ : z ∈ L₁ := by
    simpa using hmemL₁ z hz 0 (by simp [hr0.le])
  have hz'im : 0 < (z - c).im := lt_of_lt_of_le hr0 (hL₁im _ hz'L₁)
  have hmz' : mFun N σ (z - c) = w := mFun_eq_of_fC_eq N σ hσ hz'im hwim hfw'
  have hdist : dist z (z - c) < δ := by
    rw [dist_eq_norm, sub_sub_cancel]
    exact hcle.trans_lt (hBκ.trans_le (min_le_left _ _))
  have := hδuc z hzL₁ (z - c) hz'L₁ hdist
  rwa [hmz'] at this

/-- Fatou for events: if every point of `B` lies eventually in `B i`, then `ℙ B ≤ c` once
`ℙ (B i) ≤ c` eventually. -/
theorem measure_le_of_eventually {Ω : Type*} [MeasureSpace Ω] {ι : Type*} {l : Filter ι}
    [l.NeBot] [l.IsCountablyGenerated] {B : Set Ω} {Bi : ι → Set Ω} {c : ℝ≥0∞}
    (hB : ∀ ω ∈ B, ∀ᶠ i in l, ω ∈ Bi i) (h : ∀ᶠ i in l, ℙ (Bi i) ≤ c) : ℙ B ≤ c := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  set Cm : ℕ → Set Ω := fun m => ⋂ n ≥ m, Bi (u n) with hCm
  have hmono : Monotone Cm := fun m m' hmm' ω hω => by
    simp only [hCm, Set.mem_iInter] at hω ⊢
    exact fun n hn => hω n (le_trans hmm' hn)
  have hBC : B ⊆ ⋃ m, Cm m := by
    intro ω hω
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 (hu.eventually (hB ω hω))
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    simp only [hCm, Set.mem_iInter]
    exact hm
  have hC : ∀ m, ℙ (Cm m) ≤ c := by
    intro m
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hu.eventually h)
    have hsub : Cm m ⊆ Bi (u (max m n₀)) := fun ω hω => by
      simp only [hCm, Set.mem_iInter] at hω
      exact hω _ (le_max_left _ _)
    exact (measure_mono hsub).trans (hn₀ _ (le_max_right _ _))
  calc ℙ B ≤ ℙ (⋃ m, Cm m) := measure_mono hBC
    _ = ⨆ m, ℙ (Cm m) := hmono.measure_iUnion
    _ ≤ c := iSup_le hC

/-! ## Spectral calculus for `Ŝ = Tᵀ T`, `Σ = T Tᵀ` and `Ŝ + κ P₀` -/

/-- The spectrum of a positive semidefinite matrix lies in `[0, ∞)`. -/
private theorem limit_spec_nonneg {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) :
    ∀ x ∈ spectrum ℝ S, 0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hS.eigenvalues_nonneg i

/-- Every real function is continuous on the (finite) spectrum of a symmetric matrix. -/
private theorem limit_contOn {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsHermitian)
    (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ S) := by
  rw [hS.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

/-- Products of spectral calculi. -/
private theorem limit_cfc_mul {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsHermitian)
    (f g h : ℝ → ℝ) (hfg : ∀ x ∈ spectrum ℝ S, f x * g x = h x) :
    cfc f S * cfc g S = cfc h S := by
  rw [← cfc_mul f g S (limit_contOn hS f) (limit_contOn hS g)]
  exact cfc_congr fun x hx => hfg x hx

/-- `Tᵀ T ≥ 0`. -/
private theorem limit_TtT_psd {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) : (Tᵀ * T).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self T

/-- `T Tᵀ ≥ 0`. -/
private theorem limit_TTt_psd {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) : (T * Tᵀ).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose T

/-- The projection `P₀` on `ker S`, by spectral calculus. -/
private def limitP0 {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) S

/-- `S + κ P₀` for `S ≥ 0`. -/
private theorem limit_regS_eq {n : ℕ} (κ : ℝ) {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) : regS κ S = S + κ • limitP0 S := by
  unfold regS limitP0
  have h1 : cfc (fun x : ℝ => if 0 < x then x else κ) S =
      cfc (fun x : ℝ => (if 0 < x then x else 0) + κ * (if 0 < x then (0 : ℝ) else 1)) S :=
    cfc_congr fun x _ => by split_ifs <;> ring
  have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hS.1
  rw [h1, cfc_add (a := S) (fun x : ℝ => if 0 < x then x else 0)
      (fun x : ℝ => κ * (if 0 < x then (0 : ℝ) else 1)) (limit_contOn hS.1 _)
      (limit_contOn hS.1 _),
    cfc_const_mul κ (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) S (limit_contOn hS.1 _)]
  congr 1
  rw [cfc_congr (g := id) fun x hx => ?_]
  · exact hid
  · have := limit_spec_nonneg hS x hx
    split_ifs with h
    · rfl
    · simp only [id]
      linarith

/-- `P₀ᵀ = P₀`. -/
private theorem limitP0_transpose {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    (limitP0 S)ᵀ = limitP0 S := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) S : IsSelfAdjoint _).star_eq

/-- `S P₀ = 0` for `S ≥ 0`. -/
private theorem limit_mul_P0 {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) :
    S * limitP0 S = 0 := by
  have h := limit_cfc_mul hS.1 id (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) 0 fun x hx => by
    have := limit_spec_nonneg hS x hx
    split_ifs with h
    · simp
    · simp only [id, Pi.zero_apply, mul_one]
      linarith
  have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hS.1
  rw [hid, cfc_zero] at h
  exact h

/-- `T P₀ = 0`, with `P₀` the projection on `ker Tᵀ T`. -/
private theorem limit_T_mul_P0 {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    T * limitP0 (Tᵀ * T) = 0 := by
  have h0 := limit_mul_P0 (limit_TtT_psd T)
  have h1 : (T * limitP0 (Tᵀ * T))ᴴ * (T * limitP0 (Tᵀ * T)) = 0 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Tᵀ, h0, Matrix.mul_zero]
  exact Matrix.conjTranspose_mul_self_eq_zero.1 h1

/-- `(Ŝ + κ P₀) Tᵀ = Tᵀ Σ`. -/
private theorem limit_regS_mul_transpose {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) :
    regS κ (Tᵀ * T) * Tᵀ = Tᵀ * (T * Tᵀ) := by
  have hP0T : limitP0 (Tᵀ * T) * Tᵀ = 0 := by
    have := congrArg transpose (limit_T_mul_P0 T)
    rwa [transpose_mul, limitP0_transpose, transpose_zero] at this
  rw [limit_regS_eq κ (limit_TtT_psd T), Matrix.add_mul, Matrix.smul_mul, hP0T, smul_zero,
    add_zero, Matrix.mul_assoc]

/-- `(Σ^r)ᵀ = Σ^r`. -/
private theorem limit_sigPow_transpose {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    (sigPow S r)ᵀ = sigPow S r := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then x ^ r else 0) S : IsSelfAdjoint _).star_eq

/-- `Σ^{1/2} Σ^{1/2} = Σ` for `Σ ≥ 0`. -/
private theorem limit_sigPow_half_mul {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) : sigPow S (1 / 2) * sigPow S (1 / 2) = S := by
  have h := limit_cfc_mul hS.1 (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0)
    (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0) id fun x hx => by
    by_cases h0 : 0 < x
    · simp only [h0, ↓reduceIte, id]
      rw [← Real.rpow_add h0]
      norm_num
    · have : x = 0 := le_antisymm (not_lt.1 h0) (limit_spec_nonneg hS x hx)
      simp [this]
  have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hS.1
  rw [hid] at h
  exact h

/-- `Σ^{1/2} Σ = Σ Σ^{1/2}`. -/
private theorem limit_sigPow_comm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsHermitian) :
    sigPow S (1 / 2) * S = S * sigPow S (1 / 2) := by
  have h := (cfc_commute_cfc (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0) id S).eq
  have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hS
  rw [hid] at h
  exact h

/-! ## Complexification, invertibility and continuity of the inverse -/

/-- Complexification is multiplicative. -/
private theorem limit_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B := Matrix.map_mul

/-- Complexification commutes with transposition. -/
private theorem limit_cplx_transpose {p q : Type*} (A : Matrix p q ℝ) :
    cplx Aᵀ = (cplx A)ᵀ := by
  ext i j
  rfl

/-- Complexification of `B Bᵀ − z` is invertible for `Im z > 0`. -/
private theorem limit_isUnit_gram {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (cplx (B * Bᵀ) - z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have h := GN_isUnit (Matrix.PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef) Bᵀ hz
  rwa [transpose_transpose, Matrix.mul_one] at h

/-- `1 + μ A` is invertible for `Im μ > 0` when `A − z` is invertible for every `z ∈ ℂ₊`. -/
private theorem limit_isUnit_one_add {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : 0 < μ.im) (h : ∀ z : ℂ, 0 < z.im → IsUnit (A - z • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    IsUnit (1 + μ • A) := by
  have hμ0 : μ ≠ 0 := fun h0 => by simp [h0] at hμ
  have hz : 0 < (-μ⁻¹).im := by
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hμ (Complex.normSq_pos.2 hμ0)
  have he : 1 + μ • A = μ • (A - (-μ⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ hμ0, neg_smul, one_smul, sub_neg_eq_add,
      add_comm]
  rw [he, Matrix.isUnit_iff_isUnit_det, det_smul]
  exact (hμ0.isUnit.pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 (h _ hz))

/-- `P⁻¹ Q = Q P⁻¹` for commuting square matrices `P`, `Q`. -/
private theorem limit_inv_comm {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Q * P = P * Q) :
    P⁻¹ * Q = Q * P⁻¹ := by
  by_cases hP : IsUnit P.det
  · calc P⁻¹ * Q = P⁻¹ * (Q * P) * P⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = Q * P⁻¹ := by
          rw [h, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hP, Matrix.zero_mul, Matrix.mul_zero]

/-- The inverse is continuous at an invertible matrix. -/
private theorem limit_tendsto_inv {α : Type*} {n : ℕ} {l : Filter α}
    {F : α → Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) (Fin n) ℂ} (hF : Tendsto F l (𝓝 A))
    (hA : IsUnit A.det) : Tendsto (fun a => (F a)⁻¹) l (𝓝 A⁻¹) := by
  simp only [Matrix.inv_def]
  have hdet : Tendsto (fun a => (F a).det) l (𝓝 A.det) :=
    ((continuous_id.matrix_det).tendsto A).comp hF
  have hadj : Tendsto (fun a => (F a).adjugate) l (𝓝 A.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto A).comp hF
  have hinv : Tendsto (fun a => Ring.inverse (F a).det) l (𝓝 (Ring.inverse A.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hA.ne_zero
  exact hinv.smul hadj

/-! ## `Σ̲⁻¹ (G − Π) Σ̲⁻¹` for `Σ > 0` -/

/-- `Σ̲⁻¹ = diag(Σ⁻¹, 1)` for `Σ > 0`. -/
private theorem limit_ulSigma_inv {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    (ulSigma N S)⁻¹ = fromBlocks (cplx S)⁻¹ 0 0 1 := by
  have hu : IsUnit (cplx S) := hS.isUnit.map (algebraMap ℝ ℂ).mapMatrix
  rw [ulSigma, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hu isUnit_one)]
  simp

/-- `1 + μ S` is invertible for `S > 0`, `Im μ > 0`. -/
private theorem limit_isUnit_posDef {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    {μ : ℂ} (hμ : 0 < μ.im) : IsUnit (1 + μ • cplx S) :=
  limit_isUnit_one_add hμ fun z hz => by
    have h := GN_isUnit hS (1 : Matrix (Fin n) (Fin n) ℝ) hz
    simpa using h

/-- `1 + μ T Tᵀ` is invertible for `Im μ > 0`. -/
private theorem limit_isUnit_gramT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) {μ : ℂ}
    (hμ : 0 < μ.im) : IsUnit (1 + μ • cplx (T * Tᵀ)) :=
  limit_isUnit_one_add hμ fun _ hz => limit_isUnit_gram T hz

/-- `Σ̲⁻¹ (G − Π) Σ̲⁻¹` in blocks for `Σ > 0`:
`(X G_N Xᵀ − m (1 + mΣ)⁻¹, X G_N; G_N Xᵀ, G_N − m)`. -/
private theorem limit_lawMat_eq {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (X : Matrix (Fin n) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    lawMat S X z = fromBlocks
      (cplx X * GN S X z * cplx Xᵀ - mFun N (specOf S) z • (1 + mFun N (specOf S) z • cplx S)⁻¹)
      (cplx X * GN S X z) (GN S X z * cplx Xᵀ) (GN S X z - mFun N (specOf S) z • 1) := by
  set μ := mFun N (specOf S) z with hμdef
  have hσ : ∀ i, 0 ≤ specOf S i := fun i => by
    rw [specOf_eq hS.isHermitian]
    exact (hS.eigenvalues_pos i).le
  have hμ : 0 < μ.im := (mFun_spec N _ hσ hz).1
  have hQd := (isUnit_iff_isUnit_det _).1 (limit_isUnit_posDef hS hμ)
  set Q := (1 + μ • cplx S)⁻¹ with hQdef
  have hQ : Q * (1 + μ • cplx S) = 1 := nonsing_inv_mul _ hQd
  have hSd := (isUnit_iff_isUnit_det _).1
    (hS.isUnit.map (algebraMap ℝ ℂ).mapMatrix : IsUnit (cplx S))
  have h1 : (cplx S)⁻¹ * cplx S = 1 := nonsing_inv_mul _ hSd
  have h2 : cplx S * (cplx S)⁻¹ = 1 := mul_nonsing_inv _ hSd
  have e1 : Q * (cplx S)⁻¹ = (cplx S)⁻¹ - μ • Q := by
    have : (cplx S)⁻¹ = Q * (cplx S)⁻¹ + μ • Q := by
      calc (cplx S)⁻¹ = Q * (1 + μ • cplx S) * (cplx S)⁻¹ := by rw [hQ, Matrix.one_mul]
        _ = Q * (cplx S)⁻¹ + μ • Q := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc Q, h2, Matrix.mul_one]
    exact eq_sub_of_add_eq this.symm
  unfold lawMat
  rw [limit_ulSigma_inv hS, (GeqG hS X hz).1]
  unfold piMat
  rw [sub_eq_add_neg (fromBlocks _ _ _ _) (fromBlocks _ _ _ _), fromBlocks_neg, fromBlocks_add,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
    Matrix.mul_one, neg_zero]
  rw [← hμdef, ← hQdef]
  congr 1
  · simp only [neg_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    have t1 : (cplx S)⁻¹ * (cplx S * cplx X * GN S X z * cplx Xᵀ * cplx S) * (cplx S)⁻¹ =
        cplx X * GN S X z * cplx Xᵀ := by
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
      rw [Matrix.mul_assoc _ (cplx S), h2, Matrix.mul_one]
    have t3 : (cplx S)⁻¹ * (cplx S * Q) * (cplx S)⁻¹ = Q * (cplx S)⁻¹ := by
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [t1, t3, h1, Matrix.one_mul, e1]
    abel
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, h2, Matrix.mul_one]

/-! ## Test vectors `(Tᵀ Σ^{1/2} a, b)` and the block matrix of the limit -/

/-- The real matrix `diag(Tᵀ Σ^{1/2}, 1)`, mapping `(a, b)` to `(Tᵀ Σ^{1/2} a, b)`. -/
private def limitJ {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    Matrix (Fin K ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  fromBlocks (Tᵀ * sigPow (T * Tᵀ) (1 / 2)) 0 0 1

/-- The block matrix `(Y G Yᵀ − μ Σ^{1/2} Σ Q Σ^{1/2}, Y G; G Yᵀ, G − μ)`, `Y = Σ^{1/2} T X`,
as a function of `(G, μ, Q)`. -/
private def limitPhi {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    (p : Matrix (Fin N) (Fin N) ℂ × ℂ × Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  fromBlocks
    (cplx (sigPow (T * Tᵀ) (1 / 2) * T * X) * p.1 * cplx ((sigPow (T * Tᵀ) (1 / 2) * T * X)ᵀ) -
      p.2.1 • (cplx (sigPow (T * Tᵀ) (1 / 2)) * cplx (T * Tᵀ) * p.2.2 *
        cplx (sigPow (T * Tᵀ) (1 / 2))))
    (cplx (sigPow (T * Tᵀ) (1 / 2) * T * X) * p.1)
    (p.1 * cplx ((sigPow (T * Tᵀ) (1 / 2) * T * X)ᵀ)) (p.1 - p.2.1 • 1)

/-- `limitPhi` is continuous. -/
private theorem limit_continuous_phi {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) : Continuous (limitPhi T X) := by
  unfold limitPhi
  exact Continuous.matrix_fromBlocks
    (((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).sub
      (continuous_snd.fst.smul
        ((continuous_const.matrix_mul continuous_snd.snd).matrix_mul continuous_const)))
    (continuous_const.matrix_mul continuous_fst) (continuous_fst.matrix_mul continuous_const)
    (continuous_fst.sub (continuous_snd.fst.smul continuous_const))

/-- The complexification of a real vector `A v` is `cplx A` applied to the complexified `v`. -/
private theorem limit_cvec_mulVec {p q : Type*} [Fintype q] (A : Matrix p q ℝ) (v : q → ℝ) :
    (fun s => (((A *ᵥ v) s : ℝ) : ℂ)) = cplx A *ᵥ fun t => ((v t : ℝ) : ℂ) := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℝ ℂ) A v i

/-- `⟨J v, A J w⟩ = ⟨v, Jᵀ A J w⟩` for a real matrix `J`. -/
private theorem limit_testBilin_mulVec {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (J : Matrix ι' ι ℝ) (A : Matrix ι' ι' ℂ) (v w : ι → ℝ) :
    testBilin (J *ᵥ v) A (J *ᵥ w) = testBilin v ((cplx J)ᵀ * A * cplx J) w := by
  unfold testBilin
  rw [limit_cvec_mulVec, limit_cvec_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- `cplx J = diag(Tᵀ Σ^{1/2}, 1)` over `ℂ`. -/
private theorem limit_cplx_J {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    cplx (limitJ (N := N) T) =
      fromBlocks (cplx Tᵀ * cplx (sigPow (T * Tᵀ) (1 / 2))) 0 0 1 := by
  unfold limitJ
  change (fromBlocks _ _ _ _).map (algebraMap ℝ ℂ) = _
  rw [fromBlocks_map, Matrix.map_mul]
  simp only [Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

/-- For `κ > 0`: `Jᵀ Σ̲_κ⁻¹ (G_κ − Π_κ) Σ̲_κ⁻¹ J = Φ(G_N^κ, m_κ, (1 + m_κ Σ)⁻¹)`. -/
private theorem limit_sandwich {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im) :
    (cplx (limitJ (N := N) T))ᵀ * lawMat (regS κ (Tᵀ * T)) X z * cplx (limitJ (N := N) T) =
      limitPhi T X (GN (regS κ (Tᵀ * T)) X z, mFun N (specOf (regS κ (Tᵀ * T))) z,
        (1 + mFun N (specOf (regS κ (Tᵀ * T))) z • cplx (T * Tᵀ))⁻¹) := by
  have hS := regS_posDef hκ T
  set S := regS κ (Tᵀ * T) with hSdef
  set μ := mFun N (specOf S) z with hμdef
  have hμ : 0 < μ.im := (mFun_spec N _ (limit_specOf_regS_nonneg hκ T) hz).1
  set P := sigPow (T * Tᵀ) (1 / 2) with hPdef
  have hPt : (cplx P)ᵀ = cplx P := by rw [← limit_cplx_transpose, limit_sigPow_transpose]
  have hQd := (isUnit_iff_isUnit_det _).1 (limit_isUnit_posDef hS hμ)
  have hQ₀d := (isUnit_iff_isUnit_det _).1 (limit_isUnit_gramT T hμ)
  have hST : (1 + μ • cplx S) * cplx Tᵀ = cplx Tᵀ * (1 + μ • cplx (T * Tᵀ)) := by
    have := congrArg cplx (limit_regS_mul_transpose κ T)
    rw [limit_cplx_mul, limit_cplx_mul] at this
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hSdef, this]
  have hQT : (1 + μ • cplx S)⁻¹ * cplx Tᵀ = cplx Tᵀ * (1 + μ • cplx (T * Tᵀ))⁻¹ := by
    calc (1 + μ • cplx S)⁻¹ * cplx Tᵀ
        = (1 + μ • cplx S)⁻¹ * cplx Tᵀ *
            ((1 + μ • cplx (T * Tᵀ)) * (1 + μ • cplx (T * Tᵀ))⁻¹) := by
          rw [mul_nonsing_inv _ hQ₀d, Matrix.mul_one]
      _ = (1 + μ • cplx S)⁻¹ * ((1 + μ • cplx S) * cplx Tᵀ) * (1 + μ • cplx (T * Tᵀ))⁻¹ := by
          rw [hST]
          simp only [Matrix.mul_assoc]
      _ = cplx Tᵀ * (1 + μ • cplx (T * Tᵀ))⁻¹ := by
          rw [← Matrix.mul_assoc _ (1 + μ • cplx S), nonsing_inv_mul _ hQd, Matrix.one_mul]
  set Q₀ := (1 + μ • cplx (T * Tᵀ))⁻¹ with hQ₀
  rw [limit_lawMat_eq hS X hz, limit_cplx_J, fromBlocks_transpose]
  simp only [transpose_zero, transpose_one]
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  unfold limitPhi
  rw [← hμdef, ← hPdef]
  have hY : cplx (P * T * X) = cplx P * cplx T * cplx X := by
    rw [limit_cplx_mul, limit_cplx_mul]
  have hYt : cplx ((P * T * X)ᵀ) = cplx Xᵀ * cplx Tᵀ * cplx P := by
    rw [transpose_mul, transpose_mul, limit_cplx_mul, limit_cplx_mul, limit_sigPow_transpose,
      Matrix.mul_assoc]
  have hTt : (cplx Tᵀ)ᵀ = cplx T := by
    ext i j
    rfl
  rw [hY, hYt, transpose_mul, hPt, hTt, limit_cplx_mul T Tᵀ]
  congr 1
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    · simp only [Matrix.mul_assoc]
    · congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc _ (cplx Tᵀ), hQT]
      simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]

/-- At `κ = 0`: `Φ(R_N, m, (1 + mΣ)⁻¹) = G − Π` with `G` of (def_block_G), by `Y R_N Yᵀ = 1 + z R_M`
(`Y = T X`) and `Σ^{1/2} Σ^{1/2} = Σ`. -/
private theorem limit_phi_limit {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) :
    limitPhi T X (RN T X z, m, (1 + m • cplx (T * Tᵀ))⁻¹) = blockG T X z - piMat (T * Tᵀ) m := by
  set P := sigPow (T * Tᵀ) (1 / 2) with hPdef
  set Sg := cplx (T * Tᵀ) with hSg
  set Q₀ := (1 + m • Sg)⁻¹ with hQ₀
  have hQ₀d := (isUnit_iff_isUnit_det _).1 (limit_isUnit_gramT T hm)
  have hQ₀1 : Q₀ * (1 + m • Sg) = 1 := nonsing_inv_mul _ hQ₀d
  have hPP : cplx P * cplx P = Sg := by
    rw [← limit_cplx_mul, limit_sigPow_half_mul (limit_TTt_psd T)]
  have hPS : cplx P * Sg = Sg * cplx P := by
    rw [hSg, ← limit_cplx_mul, ← limit_cplx_mul, limit_sigPow_comm (limit_TTt_psd T).1]
  have hPQ : cplx P * Q₀ = Q₀ * cplx P := by
    have hc : cplx P * (1 + m • Sg) = (1 + m • Sg) * cplx P := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
        Matrix.smul_mul, hPS]
    exact (limit_inv_comm hc).symm
  set Yc := cplx (T * X) with hYc
  set Yct := cplx ((T * X)ᵀ) with hYct
  have hAN : cplx (Xᵀ * Tᵀ * T * X) = Yct * Yc := by
    rw [hYc, hYct, ← limit_cplx_mul, transpose_mul]
    simp only [Matrix.mul_assoc]
  have hAM : cplx (T * X * Xᵀ * Tᵀ) = Yc * Yct := by
    rw [hYc, hYct, ← limit_cplx_mul, transpose_mul]
    simp only [Matrix.mul_assoc]
  have hNu : IsUnit (cplx (Xᵀ * Tᵀ * T * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    have h := limit_isUnit_gram (T * X)ᵀ hz
    rwa [transpose_transpose, transpose_mul,
      show Xᵀ * Tᵀ * (T * X) = Xᵀ * Tᵀ * T * X by simp only [Matrix.mul_assoc]] at h
  have hMu : IsUnit (cplx (T * X * Xᵀ * Tᵀ) - z • (1 : Matrix (Fin M) (Fin M) ℂ)) := by
    have h := limit_isUnit_gram (T * X) hz
    rwa [transpose_mul,
      show T * X * (Xᵀ * Tᵀ) = T * X * Xᵀ * Tᵀ by simp only [Matrix.mul_assoc]] at h
  have hRN1 : (cplx (Xᵀ * Tᵀ * T * X) - z • 1) * RN T X z = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hNu)
  have hRM1 : RM T X z * (cplx (T * X * Xᵀ * Tᵀ) - z • 1) = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hMu)
  have hpush : RM T X z * Yc = Yc * RN T X z := by
    calc RM T X z * Yc
        = RM T X z * Yc * ((cplx (Xᵀ * Tᵀ * T * X) - z • 1) * RN T X z) := by
          rw [hRN1, Matrix.mul_one]
      _ = RM T X z * ((cplx (T * X * Xᵀ * Tᵀ) - z • 1) * Yc) * RN T X z := by
          rw [hAN, hAM]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.one_mul, Matrix.mul_assoc]
      _ = Yc * RN T X z := by rw [← Matrix.mul_assoc, hRM1, Matrix.one_mul]
  have hYRY : Yc * RN T X z * Yct = 1 + z • RM T X z := by
    rw [← hpush, Matrix.mul_assoc, ← hAM]
    calc RM T X z * cplx (T * X * Xᵀ * Tᵀ)
        = RM T X z * (cplx (T * X * Xᵀ * Tᵀ) - z • 1) + z • RM T X z := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_add_cancel]
      _ = 1 + z • RM T X z := by rw [hRM1]
  have hY : cplx (P * T * X) = cplx P * Yc := by rw [Matrix.mul_assoc, limit_cplx_mul]
  have hYt : cplx ((P * T * X)ᵀ) = Yct * cplx P := by
    rw [Matrix.mul_assoc, transpose_mul, limit_cplx_mul, limit_sigPow_transpose]
  have e1 : cplx P * Yc * RN T X z * (Yct * cplx P) = Sg + z • (cplx P * RM T X z * cplx P) := by
    calc cplx P * Yc * RN T X z * (Yct * cplx P)
        = cplx P * (Yc * RN T X z * Yct) * cplx P := by simp only [Matrix.mul_assoc]
      _ = cplx P * (1 + z • RM T X z) * cplx P := by rw [hYRY]
      _ = Sg + z • (cplx P * RM T X z * cplx P) := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_smul,
            Matrix.smul_mul]
  have e2 : cplx P * Sg * Q₀ * cplx P = Sg * Q₀ * Sg := by
    calc cplx P * Sg * Q₀ * cplx P = Sg * (cplx P * Q₀) * cplx P := by
          rw [hPS]
          simp only [Matrix.mul_assoc]
      _ = Sg * Q₀ * (cplx P * cplx P) := by
          rw [hPQ]
          simp only [Matrix.mul_assoc]
      _ = Sg * Q₀ * Sg := by rw [hPP]
  have e3 : Sg - m • (Sg * Q₀ * Sg) = Sg * Q₀ := by
    have h1 : Q₀ + m • (Q₀ * Sg) = 1 := by
      rw [← hQ₀1, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    calc Sg - m • (Sg * Q₀ * Sg) = Sg * (Q₀ + m • (Q₀ * Sg)) - m • (Sg * Q₀ * Sg) := by
          rw [h1, Matrix.mul_one]
      _ = Sg * Q₀ := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc Sg Q₀ Sg]
          abel
  unfold limitPhi blockG piMat
  rw [← hPdef, ← hSg, ← hQ₀, hY, hYt]
  rw [sub_eq_add_neg (fromBlocks _ _ _ _) (fromBlocks _ _ _ _), fromBlocks_neg, fromBlocks_add]
  simp only [neg_zero, add_zero, neg_neg]
  congr 1
  rw [e1, e2, add_sub_right_comm, e3, add_comm]

/-- `⟨v, A w⟩` is continuous in `A`. -/
private theorem limit_continuous_testBilin {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    Continuous (fun A : Matrix ι ι ℂ => testBilin v A w) := by
  unfold testBilin
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- `G_N` of `Ŝ + κ P₀` tends to `R_N` as `κ ↓ 0`. -/
private theorem limit_tendsto_GN {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun κ : ℝ => GN (regS κ (Tᵀ * T)) X z) (𝓝[>] 0) (𝓝 (RN T X z)) := by
  set A := cplx (Xᵀ * (Tᵀ * T) * X) with hA
  set B := cplx (Xᵀ * limitP0 (Tᵀ * T) * X) with hB
  have hF : ∀ κ : ℝ, cplx (Xᵀ * regS κ (Tᵀ * T) * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      A + (κ : ℂ) • B - z • 1 := by
    intro κ
    rw [limit_regS_eq κ (limit_TtT_psd T), Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    congr 1
    rw [hA, hB]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, Complex.coe_algebraMap]
  have hcont : Continuous (fun κ : ℝ => A + (κ : ℂ) • B - z • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).sub continuous_const
  have h0 : A + ((0 : ℝ) : ℂ) • B - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx (Xᵀ * Tᵀ * T * X) - z • 1 := by
    simp [hA, Matrix.mul_assoc]
  have hlim : Tendsto (fun κ : ℝ => A + (κ : ℂ) • B - z • (1 : Matrix (Fin N) (Fin N) ℂ))
      (𝓝[>] 0) (𝓝 (cplx (Xᵀ * Tᵀ * T * X) - z • 1)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu : IsUnit (cplx (Xᵀ * Tᵀ * T * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
    have h := limit_isUnit_gram (T * X)ᵀ hz
    rw [transpose_transpose, transpose_mul,
      show Xᵀ * Tᵀ * (T * X) = Xᵀ * Tᵀ * T * X by simp only [Matrix.mul_assoc]] at h
    exact (isUnit_iff_isUnit_det _).1 h
  have := limit_tendsto_inv hlim hu
  unfold GN RN
  simp_rw [hF]
  exact this

/-- `|B a|² = ⟨Bᵀ B a, a⟩`. -/
private theorem limit_sum_sq {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ)
    (a : n → ℝ) : ∑ i, (B *ᵥ a) i ^ 2 = ((Bᵀ * B) *ᵥ a) ⬝ᵥ a := by
  have h : ∑ i, (B *ᵥ a) i ^ 2 = (B *ᵥ a) ⬝ᵥ (B *ᵥ a) := by simp [dotProduct, sq]
  rw [h, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]

/-- `|(Tᵀ Σ^{1/2} a, b)| = |(Σ a, b)| = |Σ̲ v|`. -/
private theorem limit_testNorm_J {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) :
    testNorm (limitJ (N := N) T *ᵥ v) = testNorm (SigU (T * Tᵀ) *ᵥ v) := by
  unfold testNorm limitJ SigU
  congr 1
  rw [fromBlocks_mulVec, fromBlocks_mulVec]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero,
    zero_add, Matrix.one_mulVec]
  congr 1
  rw [limit_sum_sq, limit_sum_sq]
  congr 2
  have hP := limit_sigPow_half_mul (limit_TTt_psd T)
  have hC := limit_sigPow_comm (limit_TTt_psd T).1
  rw [transpose_mul, transpose_transpose, limit_sigPow_transpose, transpose_mul,
    transpose_transpose]
  calc sigPow (T * Tᵀ) (1 / 2) * T * (Tᵀ * sigPow (T * Tᵀ) (1 / 2))
      = sigPow (T * Tᵀ) (1 / 2) * (T * Tᵀ) * sigPow (T * Tᵀ) (1 / 2) := by
        simp only [Matrix.mul_assoc]
    _ = T * Tᵀ * (sigPow (T * Tᵀ) (1 / 2) * sigPow (T * Tᵀ) (1 / 2)) := by
        rw [hC, Matrix.mul_assoc]
    _ = T * Tᵀ * (T * Tᵀ) := by rw [hP]

/-- The `κ ↓ 0` limit at a fixed `z ∈ ℂ₊` and fixed `N`: the laws under (T_diag) for
`(Ŝ + κ P₀, X)` for all small `κ` give the laws for `G` of (def_block_G) and `N⁻¹ tr R_N`. -/
theorem lawT_of_regS {Ω : Type*} [MeasureSpace Ω] {K : ℕ} (hN : 1 ≤ N)
    (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) {ε D : ℝ} {z : ℂ}
    (hz : 0 < z.im)
    (h : ∀ᶠ κ in 𝓝[>] (0 : ℝ), AnisotropicLawAt N ε D (regS κ (Tᵀ * T)) X {z} ∧
      AveragedLawAt N ε D (regS κ (Tᵀ * T)) X {z}) :
    AnisotropicLawTAt N ε D T X {z} ∧ AveragedLawTAt N ε D T X {z} := by
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ := limit_specOf_nonneg T
  have hm0 : 0 < (mFun N σ z).im := (mFun_spec N σ hσ hz).1
  have hm : Tendsto (fun κ => mFun N (specOf (regS κ (Tᵀ * T))) z) (𝓝[>] 0)
      (𝓝 (mFun N σ z)) :=
    (tendstoUniformlyOn_mFun_regS hN T isCompact_singleton
      (fun w hw => by rw [Set.mem_singleton_iff.1 hw]; exact hz)).tendsto_at
      (Set.mem_singleton z)
  have hΨ : Tendsto (fun κ => Psi N (specOf (regS κ (Tᵀ * T))) z) (𝓝[>] 0)
      (𝓝 (Psi N σ z)) := by
    unfold Psi
    exact ((Real.continuous_sqrt.tendsto _).comp
      (((Complex.continuous_im.tendsto _).comp hm).div_const _)).add_const _
  have hQ : Tendsto (fun κ => (1 + mFun N (specOf (regS κ (Tᵀ * T))) z • cplx (T * Tᵀ))⁻¹)
      (𝓝[>] 0) (𝓝 ((1 + mFun N σ z • cplx (T * Tᵀ))⁻¹)) :=
    limit_tendsto_inv (tendsto_const_nhds.add (hm.smul_const _))
      ((isUnit_iff_isUnit_det _).1 (limit_isUnit_gramT T hm0))
  have hpos : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ := self_mem_nhdsWithin
  constructor
  · intro z' hz' v w
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    unfold DomAt
    refine measure_le_of_eventually (l := 𝓝[>] (0 : ℝ))
      (Bi := fun κ => {ω | (N : ℝ) ^ ε * (Psi N (specOf (regS κ (Tᵀ * T))) z' *
        testNorm (limitJ (N := N) T *ᵥ v) * testNorm (limitJ (N := N) T *ᵥ w)) <
        ‖testBilin (limitJ (N := N) T *ᵥ v) (lawMat (regS κ (Tᵀ * T)) (X ω) z')
          (limitJ (N := N) T *ᵥ w)‖}) ?_ ?_
    · intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      have hG := limit_tendsto_GN T (X ω) hz
      have hΦ : Tendsto (fun κ => testBilin v (limitPhi T (X ω)
          (GN (regS κ (Tᵀ * T)) (X ω) z', mFun N (specOf (regS κ (Tᵀ * T))) z',
            (1 + mFun N (specOf (regS κ (Tᵀ * T))) z' • cplx (T * Tᵀ))⁻¹)) w) (𝓝[>] 0)
          (𝓝 (testBilin v (blockG T (X ω) z' - piMat (T * Tᵀ) (mFun N σ z')) w)) := by
        rw [← limit_phi_limit T (X ω) hz hm0]
        exact ((limit_continuous_testBilin v w).tendsto _).comp
          (((limit_continuous_phi T (X ω)).tendsto _).comp (hG.prodMk_nhds (hm.prodMk_nhds hQ)))
      have hlim := hΦ.norm.sub (((hΨ.mul_const (testNorm (SigU (T * Tᵀ) *ᵥ v))).mul_const
        (testNorm (SigU (T * Tᵀ) *ᵥ w))).const_mul ((N : ℝ) ^ ε))
      filter_upwards [hlim.eventually (lt_mem_nhds (sub_pos.2 hω)), hpos] with κ hκ hκ0
      rw [limit_testBilin_mulVec, limit_sandwich T (X ω) hκ0 hz, limit_testNorm_J,
        limit_testNorm_J]
      exact sub_pos.1 hκ
    · filter_upwards [h] with κ hκ
      exact hκ.1 z' rfl _ _
  · intro z' hz'
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    unfold ODomAt DomAt
    refine measure_le_of_eventually (l := 𝓝[>] (0 : ℝ))
      (Bi := fun κ => {ω | (N : ℝ) ^ ε * (1 / (N * z'.im)) <
        ‖mN (regS κ (Tᵀ * T)) (X ω) z' - mFun N (specOf (regS κ (Tᵀ * T))) z'‖}) ?_ ?_
    · intro ω hω
      simp only [Set.mem_ofPred_eq, mNT] at hω
      have hG := limit_tendsto_GN T (X ω) hz
      have htr : Tendsto (fun κ => (N : ℂ)⁻¹ * trace (GN (regS κ (Tᵀ * T)) (X ω) z')) (𝓝[>] 0)
          (𝓝 ((N : ℂ)⁻¹ * trace (RN T (X ω) z'))) :=
        (((continuous_id.matrix_trace).tendsto _).comp hG).const_mul _
      have hlim := ((htr.sub hm).norm).sub_const ((N : ℝ) ^ ε * (1 / (N * z'.im)))
      filter_upwards [hlim.eventually (lt_mem_nhds (sub_pos.2 hω)), hpos] with κ hκ hκ0
      rw [mN_eq_trace_GN (regS_posDef hκ0 T) (X ω) hz]
      exact sub_pos.1 hκ
    · filter_upwards [h] with κ hκ
      exact hκ.2 z' rfl

/-! ## Instances -/

/-- `T = (1, 1)` (`Σ = (2)`, `Ŝ` of rank `1 < K = 2`), `N = 2`, `L` the closed disc of radius
`1/2` about `i`. -/
example : TendstoUniformlyOn
    (fun κ z => mFun 2 (specOf (regS κ ((!![(1 : ℝ), 1])ᵀ * !![(1 : ℝ), 1]))) z)
    (mFun 2 (specOf (!![(1 : ℝ), 1] * (!![(1 : ℝ), 1])ᵀ))) (𝓝[>] 0)
    (Metric.closedBall Complex.I (1 / 2)) :=
  tendstoUniformlyOn_mFun_regS (by norm_num) _ (isCompact_closedBall _ _) fun z hz => by
    have h1 : |(z - Complex.I).im| ≤ 1 / 2 :=
      (Complex.abs_im_le_norm _).trans (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hz)
    rw [Complex.sub_im, Complex.I_im] at h1
    linarith [neg_abs_le (z.im - 1)]

/-- Lebesgue measure on `ℝ`, `B = [0, 1]`, `B κ = (−κ, 1 + κ)` along `κ ↓ 0`, `c = 3/2`. -/
example : ℙ (Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (3 / 2) :=
  measure_le_of_eventually (l := 𝓝[>] (0 : ℝ)) (Bi := fun κ => Set.Ioo (-κ) (1 + κ))
    (fun ω hω => by
      filter_upwards [self_mem_nhdsWithin] with κ hκ
      have hκ0 : (0 : ℝ) < κ := hκ
      exact ⟨by linarith [hω.1], by linarith [hω.2]⟩)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with κ hκ
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_le_ofReal (by linarith [hκ.2]))

#print axioms Anisotropic.tendstoUniformlyOn_mFun_regS
#print axioms Anisotropic.measure_le_of_eventually
#print axioms Anisotropic.lawT_of_regS

end Anisotropic
