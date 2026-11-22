module

public import Anisotropic.Entrywise.LambdaO
public import Anisotropic.Framework.DominationUnion

@[expose] public section

/-! # Lemma 5.2: (Lambda_o_Z_bound) and (Lambda_o_Z_bound_initial)

`Σ = diag(σ)`, at fixed `N`, pointwise in `z ∈ 𝐃`.

(Lambda_o_Z_bound): by (Gst_step1) for every pair `s ≠ t` and a union bound over the pairs,
`1_Ξ Λ_o ≺ ((Im m + Θ + Λ_o²) Φ)^{1/2}`; with the `Z_s` step this gives
`1_Ξ (|Z_s| + Λ_o) ≺ Ψ_Θ + Φ^{1/2} Λ_o`, and `Φ^{1/2} ≤ N^{-τ/2}` on `𝐃` absorbs the last term.

(Lambda_o_Z_bound_initial): for `η ≥ 1` the entries of every minor `G^{(T)}` obey
`|G^{(T)}_{uu}| ≤ (1 + 10τ⁻¹) σ̲_u` by (opbound) of Lemma 4.6 applied to the restricted model;
the identities (Gab), (Gij), (Gia2) of Lemma 4.4, the Ward identities (GMaa4), (GMaa), (GMaa3),
Lemma 4.8 for `‖XᵀX‖` and the large deviation estimates then bound `|G_{st}| / (σ̲_s σ̲_t)` and
`|Z_s|` by `N^{-1/2}`, and `N^{-1/2} ≤ C Ψ_Θ` by (Im_m_geq_c).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Union bounds -/

section Union

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Two dominations at level `D + 1` and a deterministic implication give a domination at
level `D`. -/
private theorem lob_union2 {N : ℕ} (hN : 2 ≤ N) {e ε D : ℝ} {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : Ω → ℝ}
    (h₁ : DomAt N e (D + 1) ξ₁ ζ₁) (h₂ : DomAt N e (D + 1) ξ₂ ζ₂)
    (hdet : ∀ ω, ξ₁ ω ≤ (N : ℝ) ^ e * ζ₁ ω → ξ₂ ω ≤ (N : ℝ) ^ e * ζ₂ ω →
      ξ ω ≤ (N : ℝ) ^ ε * ζ ω) :
    DomAt N ε D ξ ζ := by
  unfold DomAt at *
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hp : 0 ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hpos.le _
  have hsub : {ω | (N : ℝ) ^ ε * ζ ω < ξ ω} ⊆
      {ω | (N : ℝ) ^ e * ζ₁ ω < ξ₁ ω} ∪ {ω | (N : ℝ) ^ e * ζ₂ ω < ξ₂ ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hc
    push Not at hc
    exact absurd (hdet ω hc.1 hc.2) (not_le.2 hω)
  calc ℙ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}
      ≤ ℙ ({ω | (N : ℝ) ^ e * ζ₁ ω < ξ₁ ω} ∪ {ω | (N : ℝ) ^ e * ζ₂ ω < ξ₂ ω}) :=
        measure_mono hsub
    _ ≤ ℙ {ω | (N : ℝ) ^ e * ζ₁ ω < ξ₁ ω} + ℙ {ω | (N : ℝ) ^ e * ζ₂ ω < ξ₂ ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h₁ h₂
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * (N : ℝ) ^ (1 : ℝ) := by
          rw [← Real.rpow_add hpos]
          ring_nf
        rw [e, Real.rpow_one]
        nlinarith

end Union

/-! ## The maximum over the pairs `s ≠ t` -/

section Max

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The number of pairs `s ≠ t` in `𝓘 × 𝓘` is at most `N³` once `M ≤ τ⁻¹ N` and
`(1 + τ⁻¹)² ≤ N`. -/
private theorem lob_card_pairs {τ : ℝ} {N : ℕ} (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (hN : (1 + τ⁻¹) ^ 2 ≤ (N : ℝ)) :
    ((Finset.univ : Finset {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2}).card : ℝ)
      ≤ (N : ℝ) ^ (3 : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : ((Finset.univ : Finset {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2}).card
      : ℝ) ≤ ((M : ℝ) + N) ^ 2 := by
    rw [Finset.card_univ]
    have := Fintype.card_subtype_le (fun p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) => p.1 ≠ p.2)
    rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this
    calc _ ≤ (((M + N) * (M + N) : ℕ) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  have h2 : (M : ℝ) + N ≤ (1 + τ⁻¹) * N := by nlinarith
  have hMN : (0 : ℝ) ≤ (M : ℝ) + N := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc _ ≤ ((M : ℝ) + N) ^ 2 := h1
    _ ≤ ((1 + τ⁻¹) * N) ^ 2 := pow_le_pow_left₀ hMN h2 2
    _ = (1 + τ⁻¹) ^ 2 * N ^ 2 := by ring
    _ ≤ (N : ℝ) * N ^ 2 := by gcongr
    _ = (N : ℝ) ^ 3 := by ring

/-- Union bound over the pairs `s ≠ t`: from `w |G_{st}| ≺ σ̲_s σ̲_t B` at level `D + 3` for
every pair, `w Λ_o ≺ B` at level `D`. -/
private theorem lob_max {N : ℕ} {τ e D : ℝ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {z : ℂ} (hM0 : 0 < M) (hN : 1 ≤ N)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (hN3 : (1 + τ⁻¹) ^ 2 ≤ (N : ℝ)) (w B : Ω → ℝ)
    (h : ∀ s t : Fin M ⊕ Fin N, s ≠ t →
      DomAt N e (D + 3) (fun ω => w ω * ‖G (diagonal σ) (X ω) z s t‖)
        (fun ω => sigS σ s * sigS σ t * B ω)) :
    DomAt N e D (fun ω => w ω * LambdaO σ (X ω) z) B := by
  have hsig : ∀ s : Fin M ⊕ Fin N, 0 < sigS σ s := by
    rintro (i | μ)
    · exact hσ i
    · exact one_pos
  have : Nonempty {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} :=
    ⟨⟨(Sum.inl ⟨0, hM0⟩, Sum.inr ⟨0, hN⟩), Sum.inl_ne_inr⟩⟩
  have hmeas := DomAt.measure_exists_lt
    (Finset.univ : Finset {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2}) hN
    (lob_card_pairs hM hN3)
    (ξ := fun p ω => w ω * ‖G (diagonal σ) (X ω) z p.1.1 p.1.2‖)
    (ζ := fun p ω => sigS σ p.1.1 * sigS σ p.1.2 * B ω) (fun p _ => h p.1.1 p.1.2 p.2)
  unfold DomAt
  refine le_trans (measure_mono ?_) hmeas
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p :
    {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) (X ω) z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
  refine ⟨p, Finset.mem_univ _, ?_⟩
  have hL : LambdaO σ (X ω) z
      = ‖G (diagonal σ) (X ω) z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2) := hp.symm
  rw [hL] at hω
  have hpos : 0 < sigS σ p.1.1 * sigS σ p.1.2 := mul_pos (hsig _) (hsig _)
  rw [mul_div_assoc', lt_div_iff₀ hpos] at hω
  calc (N : ℝ) ^ e * (sigS σ p.1.1 * sigS σ p.1.2 * B ω)
      = (N : ℝ) ^ e * B ω * (sigS σ p.1.1 * sigS σ p.1.2) := by ring
    _ < w ω * ‖G (diagonal σ) (X ω) z p.1.1 p.1.2‖ := hω

end Max

/-! ## (Lambda_o_Z_bound): absorption of `Λ_o` -/

section Absorb

/-- `√((a + Λ²) Φ) ≤ √(a Φ) + Φ^{1/2} Λ` for `a, Φ, Λ ≥ 0`. -/
private theorem lob_sqrt_split {a Φ L : ℝ} (ha : 0 ≤ a) (hΦ : 0 ≤ Φ) (hL : 0 ≤ L) :
    √((a + L ^ 2) * Φ) ≤ √(a * Φ) + √Φ * L := by
  rw [Real.sqrt_le_iff]
  have h1 := Real.sq_sqrt (mul_nonneg ha hΦ)
  have h2 := Real.sq_sqrt hΦ
  have h3 : 0 ≤ √(a * Φ) := Real.sqrt_nonneg _
  have h4 : 0 ≤ √Φ := Real.sqrt_nonneg _
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg h3 (mul_nonneg h4 hL)]

/-- The absorption step: from `x Λ ≤ r B`, `x |Z| ≤ r B`, `B ≤ Ψ + φ Λ`, `r φ ≤ 1/2`,
`4 r ≤ R` and `x ∈ {0, 1}`: `x (|Z| + Λ) ≤ R Ψ`. -/
private theorem lob_absorb {x L Zn P B r φ R : ℝ} (hx : x = 0 ∨ x = 1) (hL : 0 ≤ L)
    (hP : 0 ≤ P) (hr : 0 ≤ r) (h₁ : x * L ≤ r * B) (h₂ : x * Zn ≤ r * B)
    (hB : B ≤ P + φ * L) (hrφ : r * φ ≤ 1 / 2) (hR : 4 * r ≤ R) :
    x * (Zn + L) ≤ R * P := by
  rcases hx with rfl | rfl
  · simp only [zero_mul]
    exact mul_nonneg (by linarith) hP
  · simp only [one_mul] at h₁ h₂ ⊢
    have hrB : r * B ≤ r * P + r * φ * L := by nlinarith
    have hL2 : L ≤ 2 * (r * P) := by nlinarith
    have hZ : Zn ≤ 2 * (r * P) := by nlinarith
    nlinarith

/-- `C_m > 0`. -/
private theorem lob_Cm_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)

/-- `Λ_o ≥ 0`. -/
private theorem lob_LambdaO_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ LambdaO σ Xm z := by
  have hsig : ∀ s : Fin M ⊕ Fin N, 0 < sigS σ s := by
    rintro (i | μ)
    · exact hσ i
    · exact one_pos
  exact Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _) (mul_pos (hsig _) (hsig _)).le

/-- On `𝐃(τ, N)`: `N^e Φ^{1/2} ≤ 1/2` for `0 < e ≤ τ/4` once `2 ≤ N^{τ/4}`. -/
private theorem lob_phi_small {τ e : ℝ} {N : ℕ} {z : ℂ} (hN : 1 ≤ N) (hz : z ∈ specDomain τ N)
    (he : 0 < e) (heτ : e ≤ τ / 4) (h2 : (2 : ℝ) ≤ (N : ℝ) ^ (τ / 4)) :
    (N : ℝ) ^ e * √(PhiN N z) ≤ 1 / 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set y := (N : ℝ) ^ (τ / 4) with hy
  have hy0 : 0 < y := by linarith
  have hey : (N : ℝ) ^ e ≤ y := Real.rpow_le_rpow_of_exponent_le hN1 heτ
  have hy4 : y ^ 4 = (N : ℝ) ^ τ := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hNη : y ^ 4 ≤ (N : ℝ) * z.im := by
    rw [hy4]
    have h1 : (N : ℝ) ^ τ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by
      rw [← Real.rpow_one_add' hNpos.le (by ring_nf; linarith [hz.2.2.2.1, hz.1] )]
      ring_nf
    rw [h1]
    exact mul_le_mul_of_nonneg_left hz.2.2.2.1 hNpos.le
  have hΦ : PhiN N z ≤ (y ^ 2)⁻¹ ^ 2 := by
    unfold PhiN
    rw [show (y ^ 2)⁻¹ ^ 2 = (y ^ 4)⁻¹ by rw [← inv_pow, ← pow_mul, inv_pow]]
    exact inv_anti₀ (by positivity) hNη
  have hs : √(PhiN N z) ≤ (y ^ 2)⁻¹ := by
    calc √(PhiN N z) ≤ √((y ^ 2)⁻¹ ^ 2) := Real.sqrt_le_sqrt hΦ
      _ = (y ^ 2)⁻¹ := Real.sqrt_sq (by positivity)
  have he0 : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hNpos.le _
  calc (N : ℝ) ^ e * √(PhiN N z) ≤ y * (y ^ 2)⁻¹ :=
        mul_le_mul hey hs (Real.sqrt_nonneg _) hy0.le
    _ = y⁻¹ := by field_simp
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

/-- `4 N^e ≤ N^ε` once `4 ≤ N^{3e}` and `4e ≤ ε`. -/
private theorem lob_four {e ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (h4 : (4 : ℝ) ≤ (N : ℝ) ^ (3 * e))
    (heε : 4 * e ≤ ε) : 4 * (N : ℝ) ^ e ≤ (N : ℝ) ^ ε := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have he0 : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hNpos.le _
  calc 4 * (N : ℝ) ^ e ≤ (N : ℝ) ^ (3 * e) * (N : ℝ) ^ e := mul_le_mul_of_nonneg_right h4 he0
    _ = (N : ℝ) ^ (4 * e) := by rw [← Real.rpow_add hNpos]; ring_nf
    _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 heε

end Absorb

/-- For `τ, ε > 0` and `e = min(ε, τ)/4`: eventually `N ≥ 2`, `(1 + τ⁻¹)² ≤ N`,
`2 ≤ N^{τ/4}` and `4 ≤ N^{3e}`. -/
private theorem lob_threshold1 {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 2 ≤ N ∧ (1 + τ⁻¹) ^ 2 ≤ (N : ℝ) ∧ (2 : ℝ) ≤ (N : ℝ) ^ (τ / 4) ∧
      (4 : ℝ) ≤ (N : ℝ) ^ (3 * (min ε τ / 4)) := by
  have he : 0 < 3 * (min ε τ / 4) := by have := lt_min hε hτ; positivity
  have t1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (τ / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 * (min ε τ / 4))) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have ev := ((eventually_ge_atTop 2).and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ((1 + τ⁻¹) ^ 2))).and
    ((t1.eventually_ge_atTop 2).and (t2.eventually_ge_atTop 4))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ev
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1.1, (hN₁ N hN).1.2, (hN₁ N hN).2.1, (hN₁ N hN).2.2⟩⟩

/-! # Lemma 5.2: the bound (Lambda_o_Z_bound) -/

/-- Lemma 5.2, (Lambda_o_Z_bound). -/
theorem lambdaO_Z_bound (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ s : Fin M ⊕ Fin N,
      DomAt N ε D (fun ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
        (fun ω => PsiTheta σ (X ω) z) := by
  set e := min ε τ / 4 with he_def
  have he : 0 < e := by have := lt_min hε hτ; positivity
  have heτ : e ≤ τ / 4 := by have := min_le_right ε τ; linarith
  have heε : 4 * e ≤ ε := by have := min_le_left ε τ; linarith
  obtain ⟨N₁, h₁⟩ := Gst_step1 τ c C e (D + 1 + 3) hτ hc he
  obtain ⟨N₂, h₂⟩ := Z_step1 τ c C e (D + 1) hτ hc he
  obtain ⟨N₃, h₃⟩ := lob_threshold1 hτ hε
  refine ⟨max (max N₁ N₂) N₃, fun N hN Ω _ _ M σ X hD z hz hx s => ?_⟩
  have hN₁ : N ≥ N₁ := le_trans (by omega) hN
  have hN₂ : N ≥ N₂ := le_trans (by omega) hN
  have hN₃ : N ≥ N₃ := le_trans (by omega) hN
  obtain ⟨hN2, hN3, hτ4, h4⟩ := h₃ N hN₃
  rw [← he_def] at h4
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hNpos : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                 linarith
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · have := hD.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hD.ratio_le
    rwa [div_le_iff₀ hNpos] at this
  have hΛ := lob_max (e := e) (D := D + 1) hσ hM0 (by omega) hM hN3
    (fun ω => xiInd σ (X ω) z)
    (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z))
    (fun s t hst => h₁ N hN₁ M σ X hD z hz hx s t hst)
  have hZ := h₂ N hN₂ M σ X hD z hz hx s
  refine lob_union2 hN2 hΛ hZ fun ω hω₁ hω₂ => ?_
  obtain ⟨-, -, him⟩ := gen_prop_m_specDomain h hz
  have hmpos : 0 < (mFun N σ z).im :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 (lob_Cm_pos hτ)) hz.1) him
  have hΘ : 0 ≤ Theta σ (X ω) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΦ : 0 ≤ PhiN N z := by unfold PhiN; have := hz.1; positivity
  have hx : xiInd σ (X ω) z = 0 ∨ xiInd σ (X ω) z = 1 := by
    unfold xiInd
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact lob_absorb hx (lob_LambdaO_nonneg hσ (X ω) z) (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hNpos.le _) hω₁ hω₂
    (lob_sqrt_split (by linarith) hΦ (lob_LambdaO_nonneg hσ (X ω) z))
    (lob_phi_small (by omega) hz he heτ hτ4) (lob_four (by omega) h4 heε)

/-! ## (Lambda_o_Z_bound_initial): families of entries and their independence from a minor -/

section Families

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Entries of `X` along an injective index map form a row family. -/
private theorem lob_rowAssumption {C : ℕ → ℝ} {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) {ι : Type*} (g : ι → Fin M × Fin N) (hg : Function.Injective g) :
    RowAssumption C N (fun k ω => X ω (g k).1 (g k).2) where
  measurable k := hX.measurable (g k).1 (g k).2
  indep := hX.all.indep.precomp hg
  mean k := hX.mean (g k).1 (g k).2
  var k := hX.var (g k).1 (g k).2
  integrable_moment p k := hX.integrable_moment p (g k).1 (g k).2
  moment p k := hX.moment p (g k).1 (g k).2

/-- The entries of `G^{(T)}`, as one random variable. -/
private def lob_Y {N : ℕ} (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (ω : Ω) : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) → ℂ :=
  fun st => Gm (diagonal σ) (X ω) z T st.1 st.2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private theorem lob_measurable_Y {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) : Measurable (lob_Y σ X z T) :=
  Measurable.of_eval fun st => measurable_Gm_apply σ hX.measurable z T st.1 st.2

/-- Entries of `X` in rows or columns of `T` are independent of `G^{(T)}`. -/
private theorem lob_indep {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) {ι : Type*} (g : ι → Fin M × Fin N)
    (hg : ∀ k, Sum.inl (g k).1 ∈ T ∨ Sum.inr (g k).2 ∈ T) :
    IndepFun (fun ω (k : ι) => X ω (g k).1 (g k).2) (lob_Y σ X z T) ℙ := by
  set P : Finset (Fin M × Fin N) :=
    Finset.univ.filter (fun p => Sum.inl p.1 ∈ T ∨ Sum.inr p.2 ∈ T) with hPdef
  have hP : ∀ p ∈ P, Sum.inl p.1 ∈ T ∨ Sum.inr p.2 ∈ T := by
    intro p hp
    simpa [hPdef] using hp
  have hgP : ∀ k, g k ∈ P := fun k => by simpa [hPdef] using hg k
  have hind := indep_entries_minor hσ hX z T P hP
  have hφ : Measurable fun (f : P → ℝ) (k : ι) => f ⟨g k, hgP k⟩ :=
    Measurable.of_eval fun k => measurable_pi_apply _
  exact hind.comp hφ measurable_id

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- A union of three events of probability `≤ N^{-(D+2)}` has probability `≤ N^{-D}`. -/
private theorem lob_prob3 {N : ℕ} (hN : 2 ≤ N) {D : ℝ} {S A₁ A₂ A₃ : Set Ω}
    (hS : S ⊆ A₁ ∪ A₂ ∪ A₃) (h₁ : ℙ A₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₂ : ℙ A₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₃ : ℙ A₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2)))) :
    ℙ S ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hp : 0 ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hpos.le _
  calc ℙ S ≤ ℙ (A₁ ∪ A₂ ∪ A₃) := measure_mono hS
    _ ≤ ℙ A₁ + ℙ A₂ + ℙ A₃ := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2)))
          + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by gcongr
    _ = ENNReal.ofReal (3 * (N : ℝ) ^ (-(D + 2))) := by
        rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 2)) * (N : ℝ) ^ (2 : ℝ) := by
          rw [← Real.rpow_add hpos]
          ring_nf
        rw [e, Real.rpow_two]
        have : (3 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        nlinarith


omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `DomAt` of a variable bounded by a combination of two dominated variables on a
high-probability event. -/
private theorem lob_dom {N : ℕ} (hN : 2 ≤ N) {e D : ℝ} {ξ ζ q₁ q₂ b₁ b₂ : Ω → ℝ}
    (E : Set Ω) (hE : ℙ Eᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₁ : DomAt N e (D + 2) q₁ b₁) (h₂ : DomAt N e (D + 2) q₂ b₂)
    (hdet : ∀ ω ∈ E, q₁ ω ≤ (N : ℝ) ^ e * b₁ ω → q₂ ω ≤ (N : ℝ) ^ e * b₂ ω →
      ξ ω ≤ (N : ℝ) ^ e * ζ ω) :
    DomAt N e D ξ ζ := by
  unfold DomAt at *
  refine lob_prob3 hN ?_ hE h₁ h₂
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hc
  exact absurd (hdet ω hc.1.1 hc.1.2 hc.2) (not_le.2 hω)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The trivial domination `0 ≺ 0`. -/
private theorem lob_dom_zero {N : ℕ} {e D : ℝ} :
    DomAt (Ω := Ω) N e D (fun _ => 0) (fun _ => 0) := by
  unfold DomAt
  simp

end Families

/-! ## Ward sums for minors -/

section Ward

/-- A sum over `ι` of a function vanishing off `p` is the sum over the subtype `p`. -/
private theorem lob_sum_sub {R ι : Type*} [AddCommMonoid R] [Fintype ι] (p : ι → Prop)
    [Fintype (Subtype p)] (f : ι → R) (hf : ∀ x, ¬ p x → f x = 0) :
    ∑ x, f x = ∑ x : Subtype p, f x := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases hx : p x
    · simp [hx]
    · simp [hx, hf x hx]

/-- `‖(1 : Matrix b b ℝ).submatrix f id‖ ≤ 1` for injective `f`. -/
private theorem lob_norm_sel {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (f : a → b) (hf : Function.Injective f) : ‖(1 : Matrix b b ℝ).submatrix f id‖ ≤ 1 := by
  classical
  set P := (1 : Matrix b b ℝ).submatrix f id with hP
  have h1 : P * Pᴴ = 1 := by
    ext x y
    simp only [hP, mul_apply, submatrix_apply, conjTranspose_apply, star_trivial, one_apply, id]
    rw [Finset.sum_eq_single (f x)]
    · by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy, hf.ne hxy, eq_comm]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have h2 : ‖Pᴴ‖ * ‖Pᴴ‖ ≤ 1 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose, h1]
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  rw [l2_opNorm_conjTranspose] at h2
  nlinarith [norm_nonneg P]

/-- `‖A|‖ ≤ ‖A‖` for a submatrix along injective maps. -/
private theorem lob_norm_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b] [Fintype m']
    [Fintype n'] [DecidableEq b] [DecidableEq n'] (A : Matrix m' n' ℝ) (f : a → m') (g : b → n')
    (hf : Function.Injective f) (hg : Function.Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have e : A.submatrix f g
      = (1 : Matrix m' m' ℝ).submatrix f id * A * ((1 : Matrix n' n' ℝ).submatrix g id)ᴴ := by
    ext x y
    simp only [mul_apply, submatrix_apply, conjTranspose_apply, star_trivial, one_apply, id,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_ite, mul_one,
      mul_zero]
  rw [e]
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]
  refine (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)).trans ?_
  have h1 := lob_norm_sel f hf
  have h2 := lob_norm_sel g hg
  calc ‖(1 : Matrix m' m' ℝ).submatrix f id‖ * ‖A‖ * ‖(1 : Matrix n' n' ℝ).submatrix g id‖
      ≤ 1 * ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := by ring

/-- `‖A|ᵀ A|‖ ≤ ‖Aᵀ A‖` for a submatrix along injective maps. -/
private theorem lob_norm_XtX_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b]
    [Fintype m'] [Fintype n'] [DecidableEq b] [DecidableEq n'] (A : Matrix m' n' ℝ) (f : a → m')
    (g : b → n') (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖(A.submatrix f g)ᵀ * A.submatrix f g‖ ≤ ‖Aᵀ * A‖ := by
  classical
  rw [← conjTranspose_eq_transpose_of_trivial, ← conjTranspose_eq_transpose_of_trivial,
    l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose_mul_self]
  have h := lob_norm_submatrix A f g hf hg
  exact mul_self_le_mul_self (norm_nonneg _) h

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `Im G^{(T)}_{uu} ≥ 0`. -/
private theorem lob_im_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (T : Finset (Fin M ⊕ Fin N)) (u : Fin M ⊕ Fin N) :
    0 ≤ (Gm (diagonal σ) Xm z T u u).im := by
  have h := GMaa4_minor (posDef_diagonal_iff.2 hσ) Xm hz T (eI u)
  rw [ent_eI_eI] at h
  have h0 : 0 ≤ (Gm (diagonal σ) Xm z T u u).im / z.im := by
    rw [← h]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have := mul_nonneg h0 hz.le
  rwa [div_mul_cancel₀ _ hz.ne'] at this

/-- `Σ_ν |G^{(T)}_{μν}|² = Im G^{(T)}_{μμ} / η` ((GMaa4) for minors). -/
private theorem lob_ward_row (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (T : Finset (Fin M ⊕ Fin N)) (u : Fin M ⊕ Fin N) :
    ∑ ν, ‖Gm (diagonal σ) Xm z T u (Sum.inr ν)‖ ^ 2 = (Gm (diagonal σ) Xm z T u u).im / z.im := by
  have h := GMaa4_minor (posDef_diagonal_iff.2 hσ) Xm hz T (eI u)
  simpa only [ent_eI_eI] using h

/-- Entries of `G^{(T)}` in a removed row or column vanish. -/
private theorem lob_Gm_mem_left (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {T : Finset (Fin M ⊕ Fin N)} {s : Fin M ⊕ Fin N}
    (hs : s ∈ T) (t : Fin M ⊕ Fin N) : Gm Sig Xm z T s t = 0 := by
  simp [Gm, hs]

private theorem lob_Gm_mem_right (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {T : Finset (Fin M ⊕ Fin N)} (s : Fin M ⊕ Fin N)
    {t : Fin M ⊕ Fin N} (ht : t ∈ T) : Gm Sig Xm z T s t = 0 := by
  unfold Gm
  split_ifs <;> rfl

/-- The restricted model: `G^{(T)}_{st} = G(Σ|, X|)_{st}` for `s, t ∉ T`. -/
private theorem lob_Gm_eq (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) {s t : Fin M ⊕ Fin N} (hs : s ∉ T) (ht : t ∉ T) :
    Gm (diagonal σ) Xm z T s t
      = G ((diagonal σ).submatrix (Subtype.val : idxM T → Fin M) Subtype.val)
          (Xm.submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxN T → Fin N)) z
          (toSub T s hs) (toSub T t ht) := by
  rw [Gm_eq_extend_G_of_diagonal σ (fun i => (hσ i).ne') Xm z T]
  simp [extend, hs, ht]

/-- `‖Σ|‖ ≤ τ⁻¹`. -/
private theorem lob_norm_sig {τ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (T : Finset (Fin M ⊕ Fin N)) :
    ‖(diagonal σ).submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxM T → Fin M)‖
      ≤ τ⁻¹ := by
  rw [submatrix_diagonal _ _ Subtype.val_injective, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (inv_pos.2 h.pos).le).2 fun i => ?_
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (hσ _)]
  exact h.bound_Sigma _

/-- (GMaa) for one row of a minor: `Σ_j |G^{(T)}_{ij}|² ≤ 2τ⁻²C₀ η⁻¹ Im G^{(T)}_{ii} + 2σ_i²`. -/
private theorem lob_ward_MM {τ C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) (i : Fin M) :
    ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * (Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im
        + 2 * (σ i * σ i) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hτ := h.pos
  by_cases hi : Sum.inl i ∈ T
  · simp only [lob_Gm_mem_left _ Xm z hi, norm_zero, Complex.zero_im, mul_zero,
      zero_add]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    nlinarith [hσ i]
  set Sig' := (diagonal σ).submatrix (Subtype.val : idxM T → Fin M) Subtype.val with hSig'
  set X' := Xm.submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxN T → Fin N)
    with hX'
  have hSigd : Sig' = diagonal (σ ∘ Subtype.val) := submatrix_diagonal _ _ Subtype.val_injective
  have hP : Sig'.PosDef := by
    rw [hSigd]
    exact posDef_diagonal_iff.2 fun j => hσ _
  have hW := GMaa_unified hP X' hz (eI (Sum.inl (⟨i, hi⟩ : idxM T)))
  simp only [ent_eI_eI] at hW
  have hlhs : ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      = ∑ j' : idxM T, ‖G Sig' X' z (Sum.inl ⟨i, hi⟩) (Sum.inl j')‖ ^ 2 := by
    rw [lob_sum_sub (fun j => Sum.inl j ∉ T)]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [lob_Gm_eq hσ Xm z T hi j'.2]
      rfl
    · intro j hj
      rw [not_not] at hj
      simp [lob_Gm_mem_right _ Xm z _ hj]
  have hdiag : Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)
      = G Sig' X' z (Sum.inl ⟨i, hi⟩) (Sum.inl ⟨i, hi⟩) := lob_Gm_eq hσ Xm z T hi hi
  have hlast : ((eI (Sum.inl (⟨i, hi⟩ : idxM T) : idxM T ⊕ idxN T)) ∘ Sum.inl)
      ⬝ᵥ (Sig' * Sig') *ᵥ ((eI (Sum.inl (⟨i, hi⟩ : idxM T) : idxM T ⊕ idxN T)) ∘ Sum.inl)
      = σ i * σ i := by
    have e1 : ((eI (Sum.inl (⟨i, hi⟩ : idxM T) : idxM T ⊕ idxN T)) ∘ Sum.inl)
        = Pi.single (⟨i, hi⟩ : idxM T) 1 := by
      funext j
      simp [eI, Pi.single_apply]
    rw [e1, hSigd, diagonal_mul_diagonal]
    simp [dotProduct, mulVec, Pi.single_apply, diagonal_apply]
  rw [hlast, ← hdiag] at hW
  rw [hlhs]
  refine hW.trans ?_
  have him := lob_im_nonneg hσ Xm hz T (Sum.inl i)
  have hs := lob_norm_sig h hσ T
  have hx := (lob_norm_XtX_submatrix Xm (Subtype.val : idxM T → Fin M)
    (Subtype.val : idxN T → Fin N) Subtype.val_injective Subtype.val_injective).trans hC₀
  have h1 : 2 * ‖Sig'‖ ^ 2 * ‖X'ᵀ * X'‖ / z.im ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im := by
    gcongr
  gcongr

/-- (GMaa3) for one row of a minor: `Σ_j |G^{(T)}_{νj}|² ≤ τ⁻²C₀ Σ_ρ |G^{(T)}_{νρ}|²`. -/
private theorem lob_ward_NM {τ C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) (ν : Fin N) :
    ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inl j)‖ ^ 2
      ≤ τ⁻¹ ^ 2 * C₀ * ∑ ρ, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inr ρ)‖ ^ 2 := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hτ := h.pos
  by_cases hν : Sum.inr ν ∈ T
  · simp [lob_Gm_mem_left _ Xm z hν]
  set Sig' := (diagonal σ).submatrix (Subtype.val : idxM T → Fin M) Subtype.val with hSig'
  set X' := Xm.submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxN T → Fin N)
    with hX'
  have hSigd : Sig' = diagonal (σ ∘ Subtype.val) := submatrix_diagonal _ _ Subtype.val_injective
  have hP : Sig'.PosDef := by
    rw [hSigd]
    exact posDef_diagonal_iff.2 fun j => hσ _
  have hW := GMaa3 hP X' hz (eI (⟨ν, hν⟩ : idxN T))
  have he : (embN (eI (⟨ν, hν⟩ : idxN T)) : idxM T ⊕ idxN T → ℝ)
      = eI (Sum.inr (⟨ν, hν⟩ : idxN T)) := by
    funext x
    cases x <;> simp [embN, eI, Pi.single_apply]
  rw [he] at hW
  simp only [ent_eI_eI] at hW
  have hlhs : ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inl j)‖ ^ 2
      = ∑ j' : idxM T, ‖G Sig' X' z (Sum.inr ⟨ν, hν⟩) (Sum.inl j')‖ ^ 2 := by
    rw [lob_sum_sub (fun j => Sum.inl j ∉ T)]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [lob_Gm_eq hσ Xm z T hν j'.2]
      rfl
    · intro j hj
      rw [not_not] at hj
      simp [lob_Gm_mem_right _ Xm z _ hj]
  have hrhs : ∑ ρ, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inr ρ)‖ ^ 2
      = ∑ ρ' : idxN T, ‖G Sig' X' z (Sum.inr ⟨ν, hν⟩) (Sum.inr ρ')‖ ^ 2 := by
    rw [lob_sum_sub (fun ρ => Sum.inr ρ ∉ T)]
    · refine Finset.sum_congr rfl fun ρ' _ => ?_
      rw [lob_Gm_eq hσ Xm z T hν ρ'.2]
      rfl
    · intro ρ hρ
      rw [not_not] at hρ
      simp [lob_Gm_mem_right _ Xm z _ hρ]
  rw [hlhs, hrhs]
  refine hW.trans ?_
  have hs := lob_norm_sig h hσ T
  have hx := (lob_norm_XtX_submatrix Xm (Subtype.val : idxM T → Fin M)
    (Subtype.val : idxN T → Fin N) Subtype.val_injective Subtype.val_injective).trans hC₀
  gcongr


end Ward

/-! ## Entries of minors for `η ≥ 1` -/

section Init

/-- `N > 0` under the density assumptions. -/
private theorem lob_N_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `M > 0` under the density assumptions. -/
private theorem lob_M_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < M := by
  rcases Nat.eq_zero_or_pos M with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `M ≤ τ⁻¹ N` under the density assumptions. -/
private theorem lob_M_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : (M : ℝ) ≤ τ⁻¹ * N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lob_N_pos h
  have := h.phi_upper
  rw [phiRatio, div_le_iff₀ hN] at this
  exact this

/-- `K_op = 1 + 10 τ⁻¹`. -/
private def lob_Kop (τ : ℝ) : ℝ := 1 + 10 * τ⁻¹

private theorem lob_Kop_ge {τ : ℝ} (hτ : 0 < τ) : 1 ≤ lob_Kop τ := by
  unfold lob_Kop
  have := (inv_pos.2 hτ).le
  linarith

/-- `(1 + 5|z|)/η ≤ K_op` for `z ∈ 𝐃(τ, N)` with `η ≥ 1`. -/
private theorem lob_Kz {τ : ℝ} {N : ℕ} {z : ℂ} (hτ : 0 < τ) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) : (1 + 5 * ‖z‖) / z.im ≤ lob_Kop τ := by
  obtain ⟨h0, -, hre, -, him⟩ := hz
  have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos h0] at h1
  rw [div_le_iff₀ h0]
  unfold lob_Kop
  have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  nlinarith [mul_nonneg hτi (sub_nonneg.2 hη)]

/-- `e_s ⬝ A e_s = A_{ss}`. -/
private theorem lob_quad_eI {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℝ) (s : p) :
    eI s ⬝ᵥ A *ᵥ eI s = A s s := by
  simp [eI, dotProduct, mulVec, Pi.single_apply]

/-- `σ̲_s > 0`. -/
private theorem lob_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- For `η ≥ 1`: `|G^{(T)}_{uu}| ≤ K_op σ̲_u`, by (opbound) for the restricted model. -/
private theorem lob_diag_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im)
    (T : Finset (Fin M ⊕ Fin N)) (u : Fin M ⊕ Fin N) :
    ‖Gm (diagonal σ) Xm z T u u‖ ≤ lob_Kop τ * sigS σ u := by
  have hsu := lob_sigS_pos (N := N) hσ u
  have hK := (zero_le_one.trans (lob_Kop_ge hτ))
  by_cases hu : u ∈ T
  · rw [lob_Gm_mem_left _ Xm z hu, norm_zero]
    positivity
  set Sig' := (diagonal σ).submatrix (Subtype.val : idxM T → Fin M) Subtype.val with hSig'
  set X' := Xm.submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxN T → Fin N)
    with hX'
  have hSigd : Sig' = diagonal (σ ∘ Subtype.val) := submatrix_diagonal _ _ Subtype.val_injective
  have hP : Sig'.PosDef := by
    rw [hSigd]
    exact posDef_diagonal_iff.2 fun j => hσ _
  rw [lob_Gm_eq hσ Xm z T hu hu, ← ent_eI_eI (G Sig' X' z) (toSub T u hu) (toSub T u hu)]
  have hb := opbound hP X' hz.1 (eI (toSub T u hu)) (eI (toSub T u hu))
  have hq : eI (toSub T u hu) ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI (toSub T u hu) = sigS σ u := by
    rw [lob_quad_eI]
    cases u with
    | inl i => simp [toSub, SigU, hSigd, sigS]
    | inr μ => simp [toSub, SigU, sigS]
  rw [hq, mul_assoc, Real.mul_self_sqrt hsu.le] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (lob_Kz hτ hz hη) hsu.le)

variable {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- For `η ≥ 1`: `Im G^{(T)}_{uu} / η ≤ K_op σ̲_u`. -/
private theorem lob_im_div_le (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) (T : Finset (Fin M ⊕ Fin N)) (u : Fin M ⊕ Fin N) :
    (Gm (diagonal σ) Xm z T u u).im / z.im ≤ lob_Kop τ * sigS σ u := by
  have h0 := lob_im_nonneg hσ Xm hz.1 T u
  calc (Gm (diagonal σ) Xm z T u u).im / z.im ≤ (Gm (diagonal σ) Xm z T u u).im :=
        div_le_self h0 hη
    _ ≤ ‖Gm (diagonal σ) Xm z T u u‖ := Complex.im_le_norm _
    _ ≤ _ := lob_diag_le hτ hσ Xm hz hη T u

/-- For `η ≥ 1`, (GMaa4) summed over `μ`: `Σ_{μν} |G^{(T)}_{μν}|² ≤ K_op N`. -/
private theorem lob_isum_NN (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) (T : Finset (Fin M ⊕ Fin N)) :
    ∑ μ, ∑ ν, ‖Gm (diagonal σ) Xm z T (Sum.inr μ) (Sum.inr ν)‖ ^ 2 ≤ lob_Kop τ * N := by
  simp_rw [lob_ward_row hσ Xm hz.1 T]
  refine (Finset.sum_le_sum fun μ _ => lob_im_div_le hτ hσ hz hη T (Sum.inr μ)).trans
    (le_of_eq ?_)
  simp only [sigS, Sum.elim_inr, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- For `η ≥ 1`, (GMaa) summed over `i`, on `{‖XᵀX‖ ≤ C₀}`:
`Σ_{ij} |G^{(T)}_{ij}|² ≤ τ⁻¹ (2τ⁻²C₀ K_op τ⁻¹ + 2τ⁻²) N`. -/
private theorem lob_isum_MM {C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) :
    ∑ i, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ τ⁻¹ * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2) * N := by
  have hτ := h.pos
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hK := (zero_le_one.trans (lob_Kop_ge hτ))
  have hN : (0 : ℝ) < N := by exact_mod_cast lob_N_pos h
  have hMle := lob_M_le h
  have hrow : ∀ i : Fin M, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ 2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2 := by
    intro i
    refine (lob_ward_MM h hσ Xm hz.1 hC₀ T i).trans ?_
    have h1 := lob_im_div_le (Xm := Xm) hτ hσ hz hη T (Sum.inl i)
    simp only [sigS, Sum.elim_inl] at h1
    have h2 : lob_Kop τ * σ i ≤ lob_Kop τ * τ⁻¹ :=
      mul_le_mul_of_nonneg_left (h.bound_Sigma i) hK
    have hσσ : σ i * σ i ≤ τ⁻¹ ^ 2 := by
      rw [sq]
      exact mul_le_mul (h.bound_Sigma i) (h.bound_Sigma i) (hσ i).le (inv_pos.2 hτ).le
    have hA : 0 ≤ 2 * τ⁻¹ ^ 2 * C₀ := by positivity
    have e : 2 * τ⁻¹ ^ 2 * C₀ / z.im * (Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im
        = 2 * τ⁻¹ ^ 2 * C₀ * ((Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im / z.im) := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hA
    linarith
  refine (Finset.sum_le_sum fun i _ => hrow i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ 2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2 := by positivity
  calc (M : ℝ) * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2)
      ≤ τ⁻¹ * N * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hMle hB
    _ = _ := by ring

/-- For `η ≥ 1`, (GMaa3) summed over `ν`, on `{‖XᵀX‖ ≤ C₀}`:
`Σ_{νj} |G^{(T)}_{νj}|² ≤ τ⁻²C₀ K_op N`. -/
private theorem lob_isum_NM {C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) :
    ∑ ν, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inl j)‖ ^ 2
      ≤ τ⁻¹ ^ 2 * C₀ * lob_Kop τ * N := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  refine (Finset.sum_le_sum fun ν _ => lob_ward_NM h hσ Xm hz.1 hC₀ T ν).trans ?_
  rw [← Finset.mul_sum, mul_assoc _ (lob_Kop τ)]
  gcongr
  exact lob_isum_NN h.pos hσ hz hη T

/-- For `η ≥ 1`: `Σ_μ |G^{(r)}_{μμ}|² ≤ K_op² N`. -/
private theorem lob_idiag_N (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) (r : Fin M ⊕ Fin N) :
    ∑ μ, ‖Gm (diagonal σ) Xm z {r} (Sum.inr μ) (Sum.inr μ)‖ ^ 2 ≤ lob_Kop τ ^ 2 * N := by
  have hb : ∀ μ : Fin N, ‖Gm (diagonal σ) Xm z {r} (Sum.inr μ) (Sum.inr μ)‖ ^ 2
      ≤ lob_Kop τ ^ 2 := by
    intro μ
    have := lob_diag_le hτ hσ Xm hz hη {r} (Sum.inr μ)
    simp only [sigS, Sum.elim_inr, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  refine (Finset.sum_le_sum fun μ _ => hb μ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- For `η ≥ 1`: `Σ_i |G^{(r)}_{ii}|² ≤ K_op² τ⁻³ N`. -/
private theorem lob_idiag_M (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (r : Fin M ⊕ Fin N) :
    ∑ i, ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
      ≤ lob_Kop τ ^ 2 * τ⁻¹ ^ 3 * N := by
  have hτ := h.pos
  have hK := (zero_le_one.trans (lob_Kop_ge hτ))
  have hMle := lob_M_le h
  have hb : ∀ i : Fin M, ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
      ≤ lob_Kop τ ^ 2 * τ⁻¹ ^ 2 := by
    intro i
    have h1 := lob_diag_le hτ hσ Xm hz hη {r} (Sum.inl i)
    simp only [sigS, Sum.elim_inl] at h1
    have h2 : ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ≤ lob_Kop τ * τ⁻¹ :=
      h1.trans (mul_le_mul_of_nonneg_left (h.bound_Sigma i) hK)
    calc ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
        ≤ (lob_Kop τ * τ⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = _ := by ring
  refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (M : ℝ) * (lob_Kop τ ^ 2 * τ⁻¹ ^ 2) ≤ τ⁻¹ * N * (lob_Kop τ ^ 2 * τ⁻¹ ^ 2) := by gcongr
    _ = _ := by ring

end Init

/-! ## The five cases for `η ≥ 1` -/

section ICases

/-- `(X A Xᵀ)_{ij} = Σ_{μν} X_{iμ} A_{μν} X_{jν}`. -/
private theorem lob_exp_MM {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i j : Fin M) :
    (Xhat Xm * A * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl j)
      = ∑ μ, ∑ ν, (Xm i μ : ℂ) * A (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, fromBlocks_apply₁₂,
    map_apply, zero_add,
    transpose_apply, Finset.sum_mul, mul_zero]
  rw [Finset.sum_comm]

/-- `(Xᵀ A X)_{μν} = Σ_{ij} X_{iμ} A_{ij} X_{jν}`. -/
private theorem lob_exp_NN {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (μ ν : Fin N) :
    ((Xhat Xm)ᵀ * A * Xhat Xm) (Sum.inr μ) (Sum.inr ν)
      = ∑ i, ∑ j, (Xm i μ : ℂ) * A (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, transpose_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₂, map_apply, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Finset.sum_mul, mul_zero]
  rw [Finset.sum_comm]

/-- `(X A X)_{iμ} = Σ_{νj} X_{iν} A_{νj} X_{jμ}`. -/
private theorem lob_exp_MN {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M) (μ : Fin N) :
    (Xhat Xm * A * Xhat Xm) (Sum.inl i) (Sum.inr μ)
      = ∑ ν, ∑ j, (Xm i ν : ℂ) * A (Sum.inr ν) (Sum.inl j) * (Xm j μ : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, fromBlocks_apply₁₂,
    map_apply, zero_add,
    Finset.sum_mul, fromBlocks_apply₂₂, mul_zero, add_zero]
  rw [Finset.sum_comm]

/-- Splitting a quadratic form into its off-diagonal and diagonal parts. -/
private theorem lob_quad_split {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (A : ι → ι → ℂ) (N : ℕ) :
    ∑ a, ∑ b, (x a : ℂ) * A a b * (x b : ℂ) - (N : ℂ)⁻¹ * ∑ a, A a a
      = ∑ a, ∑ b ∈ Finset.univ.erase a, (x a : ℂ) * A a b * (x b : ℂ)
        + ∑ a, A a a * ((x a : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ)) := by
  have e : ∀ a, ∑ b, (x a : ℂ) * A a b * (x b : ℂ)
      = ∑ b ∈ Finset.univ.erase a, (x a : ℂ) * A a b * (x b : ℂ) + (x a : ℂ) * A a a * (x a : ℂ) :=
    fun a => (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm
  simp only [e, Finset.sum_add_distrib, Finset.mul_sum, Complex.ofReal_natCast]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

variable {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- Case `G_{ij}`, `i ≠ j`, `η ≥ 1`: (Gab) and (opbound). -/
private theorem lob_det_ij (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) {i j : Fin M} (hij : i ≠ j) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl j)‖
      ≤ σ i * σ j * lob_Kop τ ^ 2 * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inl j} (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖ := by
  rw [(Gab hσ Xm hz.1 i j hij).2.2, lob_exp_MM]
  have h1 := lob_diag_le hτ hσ Xm hz hη ∅ (Sum.inl i)
  rw [Gm_empty] at h1
  have h2 := lob_diag_le hτ hσ Xm hz hη {Sum.inl i} (Sum.inl j)
  simp only [sigS, Sum.elim_inl] at h1 h2
  rw [norm_mul, norm_mul]
  have hK := lob_Kop_ge hτ
  calc ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ * ‖G1 (diagonal σ) Xm z (Sum.inl i)
        (Sum.inl j) (Sum.inl j)‖ * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inl j) (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖
      ≤ lob_Kop τ * σ i * (lob_Kop τ * σ j) * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inl j) (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖ := by
        have : 0 ≤ lob_Kop τ * σ i := mul_nonneg (by linarith) (hσ i).le
        gcongr
    _ = _ := by ring

/-- Case `G_{μν}`, `μ ≠ ν`, `η ≥ 1`: (Gij) and (opbound). -/
private theorem lob_det_munu (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) {μ ν : Fin N} (hμν : μ ≠ ν) :
    ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr ν)‖
      ≤ 1 * 1 * lob_Kop τ ^ 2 * ‖∑ i, ∑ j, (Xm i μ : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inr μ, Sum.inr ν} (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ)‖ := by
  rw [(Gij (posDef_diagonal_iff.2 hσ) Xm hz.1 μ ν hμν).2.2, lob_exp_NN]
  have h1 := lob_diag_le hτ hσ Xm hz hη ∅ (Sum.inr μ)
  rw [Gm_empty] at h1
  have h2 := lob_diag_le hτ hσ Xm hz hη {Sum.inr μ} (Sum.inr ν)
  simp only [sigS, Sum.elim_inr, mul_one] at h1 h2
  rw [norm_mul, norm_mul]
  have hK : 0 ≤ lob_Kop τ := zero_le_one.trans (lob_Kop_ge hτ)
  calc _ ≤ lob_Kop τ * lob_Kop τ * ‖∑ i, ∑ j, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inr μ) (Sum.inr ν) (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ)‖ := by
        gcongr
    _ = _ := by ring

/-- Case `G_{iμ}`, `η ≥ 1`: (Gia2) and (opbound), with the sum over `ν ≠ μ`, `j ≠ i`. -/
private theorem lob_det_imu (hτ : 0 < τ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
    (hη : 1 ≤ z.im) (i : Fin M) (μ : Fin N) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖
      ≤ σ i * 1 * lob_Kop τ ^ 2 * (‖∑ ν : {ν : Fin N // ν ≠ μ},
        ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖) := by
  rw [(Gia2 hσ Xm hz.1 i μ).2, lob_exp_MN]
  have hsub : ∑ ν, ∑ j, (Xm i ν : ℂ)
      * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr ν) (Sum.inl j) * (Xm j μ : ℂ)
      = ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)
        * (Xm j.1 μ : ℂ) := by
    rw [show G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
      = Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} from rfl]
    rw [lob_sum_sub (fun ν => ν ≠ μ)]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [lob_sum_sub (fun j => j ≠ i)]
      intro j hj
      rw [not_not] at hj
      rw [hj, lob_Gm_mem_right _ Xm z _ (by simp)]
      ring
    · intro ν hν
      rw [not_not] at hν
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hν, lob_Gm_mem_left _ Xm z (by simp)]
      ring
  rw [hsub]
  have h1 := lob_diag_le hτ hσ Xm hz hη ∅ (Sum.inl i)
  rw [Gm_empty] at h1
  have h2 := lob_diag_le hτ hσ Xm hz hη {Sum.inl i} (Sum.inr μ)
  simp only [sigS, Sum.elim_inl, Sum.elim_inr, mul_one] at h1 h2
  rw [norm_mul, norm_mul]
  have hK := lob_Kop_ge hτ
  have h3 : ‖-(Xm i μ : ℂ) + ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
      (Xm i ν.1 : ℂ) * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)
        * (Xm j.1 μ : ℂ)‖
      ≤ ‖∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp only [norm_neg, Finset.univ_unique, Finset.sum_singleton, one_mul]
    ring
  calc _ ≤ lob_Kop τ * σ i * lob_Kop τ * (‖∑ ν : {ν : Fin N // ν ≠ μ},
        ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖) := by
        have : 0 ≤ lob_Kop τ * σ i := mul_nonneg (by linarith) (hσ i).le
        gcongr
    _ = _ := by ring

/-- Case `Z_i`: off-diagonal and diagonal parts of the quadratic form in row `i`. -/
private theorem lob_det_Zi (i : Fin M) :
    ‖Zi σ Xm z i‖
      ≤ 1 * (‖∑ μ, ∑ ν ∈ Finset.univ.erase μ, (Xm i μ : ℂ)
          * Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν) * (Xm i ν : ℂ)‖
        + ‖∑ μ, Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr μ)
          * ((Xm i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖) := by
  rw [one_mul, Zi, lob_exp_MM]
  rw [lob_quad_split (fun μ => Xm i μ)
    (fun μ ν => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν)) N]
  exact norm_add_le _ _

/-- Case `Z_μ`: off-diagonal and diagonal parts of the quadratic form in column `μ`. -/
private theorem lob_det_Zmu (μ : Fin N) :
    ‖Zmu σ Xm z μ‖
      ≤ 1 * (‖∑ i, ∑ j ∈ Finset.univ.erase i, (Xm i μ : ℂ)
          * Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j) * (Xm j μ : ℂ)‖
        + ‖∑ i, Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl i)
          * ((Xm i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖) := by
  rw [one_mul, Zmu, lob_exp_NN]
  rw [lob_quad_split (fun i => Xm i μ)
    (fun i j => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j)) N]
  exact norm_add_le _ _

end ICases

/-! ## The coefficient bounds for `η ≥ 1` -/

section IBounds

/-- The constant `k` with every coefficient sum `≤ k N`. -/
private def lob_k (τ C₀ : ℝ) : ℝ :=
  lob_Kop τ + τ⁻¹ * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2)
    + τ⁻¹ ^ 2 * C₀ * lob_Kop τ + lob_Kop τ ^ 2 + lob_Kop τ ^ 2 * τ⁻¹ ^ 3 + 1

/-- `L = 2 K_op² k^{1/2}`. -/
private def lob_L (τ C₀ : ℝ) : ℝ := 2 * lob_Kop τ ^ 2 * √(lob_k τ C₀)

private theorem lob_k_parts {τ C₀ : ℝ} (hτ : 0 < τ) (hC0 : 0 ≤ C₀) :
    0 ≤ lob_Kop τ ∧ 0 ≤ τ⁻¹ * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2) ∧
      0 ≤ τ⁻¹ ^ 2 * C₀ * lob_Kop τ ∧ 0 ≤ lob_Kop τ ^ 2 ∧ 0 ≤ lob_Kop τ ^ 2 * τ⁻¹ ^ 3 := by
  have hK := (zero_le_one.trans (lob_Kop_ge hτ))
  refine ⟨hK, by positivity, by positivity, by positivity, by positivity⟩

private theorem lob_le_k {τ C₀ : ℝ} (hτ : 0 < τ) (hC0 : 0 ≤ C₀) :
    lob_Kop τ ≤ lob_k τ C₀ ∧
      τ⁻¹ * (2 * τ⁻¹ ^ 2 * C₀ * (lob_Kop τ * τ⁻¹) + 2 * τ⁻¹ ^ 2) ≤ lob_k τ C₀ ∧
      τ⁻¹ ^ 2 * C₀ * lob_Kop τ ≤ lob_k τ C₀ ∧ lob_Kop τ ^ 2 ≤ lob_k τ C₀ ∧
      lob_Kop τ ^ 2 * τ⁻¹ ^ 3 ≤ lob_k τ C₀ ∧ 1 ≤ lob_k τ C₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lob_k_parts hτ hC0
  unfold lob_k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `S ≤ k' N` with `0 ≤ k' ≤ k` gives `√S / N ≤ √k √(N⁻¹)`. -/
private theorem lob_isqrt {S k' k : ℝ} {N : ℕ} (hN : 0 < N) (hk' : 0 ≤ k') (hkk : k' ≤ k)
    (hS : S ≤ k' * N) : √S / N ≤ √k * √((N : ℝ)⁻¹) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : 0 ≤ k := hk'.trans hkk
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN'
  have e : √k * √((N : ℝ)⁻¹) * N = √(k * N) := by
    calc √k * √((N : ℝ)⁻¹) * N = √k * ((√(N : ℝ))⁻¹ * (√(N : ℝ) * √(N : ℝ))) := by
          rw [Real.sqrt_inv, Real.mul_self_sqrt hN'.le]; ring
      _ = √k * √(N : ℝ) := by field_simp
      _ = √(k * N) := (Real.sqrt_mul hk _).symm
  rw [div_le_iff₀ hN', e]
  exact Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_right hkk hN'.le))

/-- The off-diagonal bound is at most the full Hilbert–Schmidt bound. -/
private theorem lob_off_le {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℂ) :
    ldeOffBound N A ≤ √(∑ a, ∑ b, ‖A a b‖ ^ 2) / N := by
  unfold ldeOffBound
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun _ _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

variable {τ C₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

section OnInit

variable (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N)
  (hη : 1 ≤ z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
include h hσ hz hη hC₀

private theorem lob_coef_ij (T : Finset (Fin M ⊕ Fin N)) :
    √(∑ μ, ∑ ν, ‖Gm (diagonal σ) Xm z T (Sum.inr μ) (Sum.inr ν)‖ ^ 2) / N
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lob_isqrt (lob_N_pos h) (lob_k_parts h.pos hC0).1 (lob_le_k h.pos hC0).1
    (lob_isum_NN h.pos hσ hz hη T)

private theorem lob_coef_munu (T : Finset (Fin M ⊕ Fin N)) :
    √(∑ i, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2) / N
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lob_isqrt (lob_N_pos h) (lob_k_parts h.pos hC0).2.1 (lob_le_k h.pos hC0).2.1
    (lob_isum_MM h hσ hz hη hC₀ T)

private theorem lob_coef_imu (i : Fin M) (μ : Fin N) :
    √(∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
      ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)‖ ^ 2) / N
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have e : ∑ ν, ∑ j, ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν) (Sum.inl j)‖ ^ 2
      = ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
        ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)‖ ^ 2 := by
    rw [lob_sum_sub (fun ν => ν ≠ μ)]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [lob_sum_sub (fun j => j ≠ i)]
      intro j hj
      rw [not_not] at hj
      rw [hj, lob_Gm_mem_right _ Xm z _ (by simp)]
      simp
    · intro ν hν
      rw [not_not] at hν
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hν, lob_Gm_mem_left _ Xm z (by simp)]
      simp
  rw [← e]
  exact lob_isqrt (lob_N_pos h) (lob_k_parts h.pos hC0).2.2.1 (lob_le_k h.pos hC0).2.2.1
    (lob_isum_NM h hσ hz hη hC₀ _)

omit hσ hz hη in
private theorem lob_coef_lin :
    ldeLinBound N (fun _ : Unit => (1 : ℂ)) ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hk := (lob_le_k h.pos hC0).2.2.2.2.2
  unfold ldeLinBound
  simp only [Finset.univ_unique, Finset.sum_singleton, norm_one, one_pow, one_div]
  calc √((N : ℝ)⁻¹) = 1 * √((N : ℝ)⁻¹) := (one_mul _).symm
    _ ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
        gcongr
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hk

private theorem lob_coef_Zi_off (i : Fin M) :
    ldeOffBound N (fun μ ν => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν))
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) :=
  (lob_off_le _).trans (lob_coef_ij h hσ hz hη hC₀ _)

private theorem lob_coef_Zi_diag (i : Fin M) :
    ldeDiagBound N (fun μ => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr μ))
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lob_isqrt (lob_N_pos h) (lob_k_parts h.pos hC0).2.2.2.1 (lob_le_k h.pos hC0).2.2.2.1
    (lob_idiag_N h.pos hσ hz hη _)

private theorem lob_coef_Zmu_off (μ : Fin N) :
    ldeOffBound N (fun i j => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j))
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) :=
  (lob_off_le _).trans (lob_coef_munu h hσ hz hη hC₀ _)

private theorem lob_coef_Zmu_diag (μ : Fin N) :
    ldeDiagBound N (fun i => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl i))
      ≤ √(lob_k τ C₀) * √((N : ℝ)⁻¹) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lob_isqrt (lob_N_pos h) (lob_k_parts h.pos hC0).2.2.2.2 (lob_le_k h.pos hC0).2.2.2.2.1
    (lob_idiag_M h hσ hz hη _)

end OnInit

/-- The final step for `η ≥ 1`: `g ≤ N^e P (2 K s W)` from `g ≤ P K (q₁ + q₂)`,
`q_a ≤ N^e b_a` and `b_a ≤ s W`. -/
private theorem lob_ifinish {N : ℕ} {e g P K s W q₁ q₂ b₁ b₂ : ℝ} (hN : 0 < N) (hP : 0 ≤ P)
    (hK : 0 ≤ K) (hg : g ≤ P * K * (q₁ + q₂)) (hb₁ : b₁ ≤ s * W) (hb₂ : b₂ ≤ s * W)
    (h₁ : q₁ ≤ (N : ℝ) ^ e * b₁) (h₂ : q₂ ≤ (N : ℝ) ^ e * b₂) :
    g ≤ (N : ℝ) ^ e * (P * (2 * K * s * W)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have he : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hN'.le _
  have hq : q₁ + q₂ ≤ (N : ℝ) ^ e * (2 * s * W) := by
    have := add_le_add (h₁.trans (mul_le_mul_of_nonneg_left hb₁ he))
      (h₂.trans (mul_le_mul_of_nonneg_left hb₂ he))
    linarith
  calc g ≤ P * K * (q₁ + q₂) := hg
    _ ≤ P * K * ((N : ℝ) ^ e * (2 * s * W)) := mul_le_mul_of_nonneg_left hq (mul_nonneg hP hK)
    _ = _ := by ring

end IBounds

/-! ## The probabilistic step for each case, `η ≥ 1` -/

section IProb

/-- The bilinear large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lob_BilAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι κ β : Type} [Fintype ι] [Fintype κ] [MeasurableSpace β] (x : ι → Ω → ℝ)
    (x' : κ → Ω → ℝ) (Y : Ω → β) (B : β → ι → κ → ℂ),
    RowAssumption C N (Sum.elim x x') → Measurable Y → (∀ i j, Measurable fun b => B b i j) →
    IndepFun (fun ω (s : ι ⊕ κ) => Sum.elim x x' s ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, ∑ j, (x i ω : ℂ) * B (Y ω) i j * (x' j ω : ℂ)‖)
      (fun ω => √(∑ i, ∑ j, ‖B (Y ω) i j‖ ^ 2) / N)

/-- The off-diagonal large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lob_OffAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (A : β → ι → ι → ℂ), RowAssumption C N x → Measurable Y →
    (∀ i j, Measurable fun b => A b i j) → IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i, (x i ω : ℂ) * A (Y ω) i j * (x j ω : ℂ)‖)
      (fun ω => ldeOffBound N (A (Y ω)))

/-- The diagonal large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lob_DiagAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (a : β → ι → ℂ), RowAssumption C N x → Measurable Y → (∀ i, Measurable fun b => a b i) →
    IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * ((x i ω : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖)
      (fun ω => ldeDiagBound N (a (Y ω)))

/-- The linear large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lob_LinAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (a : β → ι → ℂ), RowAssumption C N x → Measurable Y → (∀ i, Measurable fun b => a b i) →
    IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * (x i ω : ℂ)‖) (fun ω => ldeLinBound N (a (Y ω)))

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {τ c C₀ ε D : ℝ}
  {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- `0 ≤ √k √Q`. -/
private theorem lob_zero_le (k Q : ℝ) : (0 : ℝ) ≤ √k * √Q :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem lob_L_eq : 2 * lob_Kop τ ^ 2 * √(lob_k τ C₀) = lob_L τ C₀ := rfl

private theorem lob_icase_ij (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lob_BilAt C N ε (D + 2) Ω) {i j : Fin M} (hij : i ≠ j) :
    DomAt N ε D (fun ω => ‖G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inl j)‖)
      (fun _ => sigS (N := N) σ (Sum.inl i) * sigS (N := N) σ (Sum.inl j)
        * (lob_L τ C₀ * √((N : ℝ)⁻¹))) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inl i, Sum.inl j} with hT
  let g : Fin N ⊕ Fin N → Fin M × Fin N := Sum.elim (fun μ => (i, μ)) (fun ν => (j, ν))
  have hginj : Function.Injective g := by
    rintro (a | a) (b | b) hab <;>
      simp only [g, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
    · rw [hab.2]
    · exact absurd hab.1 hij
    · exact absurd hab.1 (Ne.symm hij)
    · rw [hab.2]
  have hfam : (Sum.elim (fun μ ω => X ω i μ) (fun ν ω => X ω j ν) : Fin N ⊕ Fin N → Ω → ℝ)
      = fun k ω => X ω (g k).1 (g k).2 := by
    funext k ω
    cases k <;> rfl
  have hind := lob_indep hσ hX z T g (by rintro (μ | ν) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : Fin N ⊕ Fin N) =>
      Sum.elim (fun μ ω => X ω i μ) (fun ν ω => X ω j ν) s ω) (lob_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun μ ω => X ω i μ) (fun ν ω => X ω j ν) (lob_Y σ X z T)
    (fun b μ ν => b (Sum.inr μ, Sum.inr ν)) (hfam ▸ lob_rowAssumption hX g hginj)
    (lob_measurable_Y hX z T) (fun μ ν => measurable_pi_apply _) hind'
  refine lob_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom lob_dom_zero ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hK := lob_Kop_ge hτ
  rw [← lob_L_eq]
  refine lob_ifinish (by omega) (mul_pos (hσ i) (hσ j)).le (by positivity) ?_
    (lob_coef_ij h hσ hz hη hω T) (lob_zero_le _ _) h1 h2
  refine (lob_det_ij hτ hσ hz hη hij).trans (le_of_eq ?_)
  simp only [sigS, Sum.elim_inl, add_zero]
  rfl

private theorem lob_icase_munu (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lob_BilAt C N ε (D + 2) Ω) {μ ν : Fin N} (hμν : μ ≠ ν) :
    DomAt N ε D (fun ω => ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr ν)‖)
      (fun _ => sigS (M := M) σ (Sum.inr μ) * sigS (M := M) σ (Sum.inr ν)
        * (lob_L τ C₀ * √((N : ℝ)⁻¹))) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inr μ, Sum.inr ν} with hT
  let g : Fin M ⊕ Fin M → Fin M × Fin N := Sum.elim (fun i => (i, μ)) (fun j => (j, ν))
  have hginj : Function.Injective g := by
    rintro (a | a) (b | b) hab <;>
      simp only [g, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
    · rw [hab.1]
    · exact absurd hab.2 hμν
    · exact absurd hab.2 (Ne.symm hμν)
    · rw [hab.1]
  have hfam : (Sum.elim (fun i ω => X ω i μ) (fun j ω => X ω j ν) : Fin M ⊕ Fin M → Ω → ℝ)
      = fun k ω => X ω (g k).1 (g k).2 := by
    funext k ω
    cases k <;> rfl
  have hind := lob_indep hσ hX z T g (by rintro (i | j) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : Fin M ⊕ Fin M) =>
      Sum.elim (fun i ω => X ω i μ) (fun j ω => X ω j ν) s ω) (lob_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun i ω => X ω i μ) (fun j ω => X ω j ν) (lob_Y σ X z T)
    (fun b i j => b (Sum.inl i, Sum.inl j)) (hfam ▸ lob_rowAssumption hX g hginj)
    (lob_measurable_Y hX z T) (fun i j => measurable_pi_apply _) hind'
  refine lob_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom lob_dom_zero ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hK := lob_Kop_ge hτ
  rw [← lob_L_eq]
  refine lob_ifinish (by omega) (by simp [sigS]) (by positivity) ?_
    (lob_coef_munu h hσ hz hη hω T) (lob_zero_le _ _) h1 h2
  refine (lob_det_munu hτ hσ hz hη hμν).trans (le_of_eq ?_)
  simp only [sigS, Sum.elim_inr, add_zero]
  rfl

private theorem lob_icase_imu (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lob_BilAt C N ε (D + 2) Ω) (hlin : lob_LinAt C N ε (D + 2) Ω)
    (i : Fin M) (μ : Fin N) :
    DomAt N ε D (fun ω => ‖G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inr μ)‖)
      (fun _ => sigS (N := N) σ (Sum.inl i) * sigS (M := M) σ (Sum.inr μ)
        * (lob_L τ C₀ * √((N : ℝ)⁻¹))) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inl i, Sum.inr μ} with hT
  let g : {ν : Fin N // ν ≠ μ} ⊕ {j : Fin M // j ≠ i} → Fin M × Fin N :=
    Sum.elim (fun ν => (i, ν.1)) (fun j => (j.1, μ))
  have hginj : Function.Injective g := by
    rintro (a | a) (b | b) hab
    · simp only [g, Sum.elim_inl, Prod.mk.injEq, true_and] at hab
      rw [Subtype.ext hab]
    · simp only [g, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
      exact absurd hab.2 a.2
    · simp only [g, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
      exact absurd hab.2.symm b.2
    · simp only [g, Sum.elim_inr, Prod.mk.injEq, and_true] at hab
      rw [Subtype.ext hab]
  have hfam : (Sum.elim (fun (ν : {ν : Fin N // ν ≠ μ}) ω => X ω i ν.1)
      (fun (j : {j : Fin M // j ≠ i}) ω => X ω j.1 μ)
      : {ν : Fin N // ν ≠ μ} ⊕ {j : Fin M // j ≠ i} → Ω → ℝ)
      = fun k ω => X ω (g k).1 (g k).2 := by
    funext k ω
    cases k <;> rfl
  have hind := lob_indep hσ hX z T g (by rintro (ν | j) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : {ν : Fin N // ν ≠ μ} ⊕ {j : Fin M // j ≠ i}) =>
      Sum.elim (fun (ν : {ν : Fin N // ν ≠ μ}) ω => X ω i ν.1)
        (fun (j : {j : Fin M // j ≠ i}) ω => X ω j.1 μ) s ω) (lob_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun (ν : {ν : Fin N // ν ≠ μ}) ω => X ω i ν.1)
    (fun (j : {j : Fin M // j ≠ i}) ω => X ω j.1 μ) (lob_Y σ X z T)
    (fun b ν j => b (Sum.inr ν.1, Sum.inl j.1)) (hfam ▸ lob_rowAssumption hX g hginj)
    (lob_measurable_Y hX z T) (fun ν j => measurable_pi_apply _) hind'
  let g₂ : Unit → Fin M × Fin N := fun _ => (i, μ)
  have hdom₂ := hlin (fun (_ : Unit) ω => X ω i μ) (lob_Y σ X z T) (fun _ _ => (1 : ℂ))
    (lob_rowAssumption hX g₂ fun a b _ => Subsingleton.elim a b)
    (lob_measurable_Y hX z T) (fun _ => measurable_const)
    (lob_indep hσ hX z T g₂ fun _ => Or.inl (by simp [hT, g₂]))
  refine lob_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hK := lob_Kop_ge hτ
  rw [← lob_L_eq]
  refine lob_ifinish (by omega) (by simpa [sigS] using (hσ i).le) (by positivity) ?_
    (lob_coef_imu h hσ hz hη hω i μ) (lob_coef_lin h hω) h1 h2
  refine (lob_det_imu hτ hσ hz hη i μ).trans (le_of_eq ?_)
  simp only [sigS, Sum.elim_inl, Sum.elim_inr]
  rfl

private theorem lob_icase_mui (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lob_BilAt C N ε (D + 2) Ω) (hlin : lob_LinAt C N ε (D + 2) Ω)
    (μ : Fin N) (i : Fin M) :
    DomAt N ε D (fun ω => ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inl i)‖)
      (fun _ => sigS (M := M) σ (Sum.inr μ) * sigS (N := N) σ (Sum.inl i)
        * (lob_L τ C₀ * √((N : ℝ)⁻¹))) := by
  have hσ := hD.pos
  have key := lob_icase_imu hτ hD hz hη hN hE hbil hlin i μ
  have e : ∀ ω, G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inl i)
      = G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inr μ) := fun ω => by
    have := congrFun (congrFun (G_transpose (posDef_diagonal_iff.2 hσ) (X ω) hz.1) (Sum.inl i))
      (Sum.inr μ)
    rwa [transpose_apply] at this
  unfold DomAt at key ⊢
  simp only [e, mul_comm (sigS (M := M) σ (Sum.inr μ))]
  exact key

private theorem lob_icase_Zi (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hoff : lob_OffAt C N ε (D + 2) Ω) (hdiag : lob_DiagAt C N ε (D + 2) Ω) (i : Fin M) :
    DomAt N ε D (fun ω => ‖ZS σ (X ω) z (Sum.inl i)‖)
      (fun _ => lob_L τ C₀ * √((N : ℝ)⁻¹)) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inl i} with hT
  have hind := lob_indep hσ hX z T (fun μ => (i, μ)) (fun _ => Or.inl (by simp [hT]))
  have hdom₁ := hoff (fun μ ω => X ω i μ) (lob_Y σ X z T)
    (fun b μ ν => b (Sum.inr μ, Sum.inr ν)) (hX.row i) (lob_measurable_Y hX z T)
    (fun μ ν => measurable_pi_apply _) hind
  have hdom₂ := hdiag (fun μ ω => X ω i μ) (lob_Y σ X z T)
    (fun b μ => b (Sum.inr μ, Sum.inr μ)) (hX.row i) (lob_measurable_Y hX z T)
    (fun μ => measurable_pi_apply _) hind
  refine lob_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom₁ hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hK := lob_Kop_ge hτ
  rw [← lob_L_eq]
  refine le_of_le_of_eq (lob_ifinish (P := 1) (K := lob_Kop τ ^ 2) (by omega) zero_le_one
    (by positivity) ?_ (lob_coef_Zi_off h hσ hz hη hω i) (lob_coef_Zi_diag h hσ hz hη hω i)
    h1 h2) (by ring)
  refine (lob_det_Zi i).trans ?_
  rw [one_mul, one_mul]
  have h0 : 0 ≤ ‖∑ μ, ∑ ν ∈ Finset.univ.erase μ, (X ω i μ : ℂ)
        * Gm (diagonal σ) (X ω) z {Sum.inl i} (Sum.inr μ) (Sum.inr ν) * (X ω i ν : ℂ)‖
      + ‖∑ μ, Gm (diagonal σ) (X ω) z {Sum.inl i} (Sum.inr μ) (Sum.inr μ)
        * ((X ω i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ := by positivity
  exact le_mul_of_one_le_left h0 (one_le_pow₀ hK)

private theorem lob_icase_Zmu (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hη : 1 ≤ z.im) (hN : 2 ≤ N)
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hoff : lob_OffAt C N ε (D + 2) Ω) (hdiag : lob_DiagAt C N ε (D + 2) Ω) (μ : Fin N) :
    DomAt N ε D (fun ω => ‖ZS σ (X ω) z (Sum.inr μ)‖)
      (fun _ => lob_L τ C₀ * √((N : ℝ)⁻¹)) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inr μ} with hT
  have hind := lob_indep hσ hX z T (fun i => (i, μ)) (fun _ => Or.inr (by simp [hT]))
  have hdom₁ := hoff (fun i ω => X ω i μ) (lob_Y σ X z T)
    (fun b i j => b (Sum.inl i, Sum.inl j)) (hX.col μ) (lob_measurable_Y hX z T)
    (fun i j => measurable_pi_apply _) hind
  have hdom₂ := hdiag (fun i ω => X ω i μ) (lob_Y σ X z T)
    (fun b i => b (Sum.inl i, Sum.inl i)) (hX.col μ) (lob_measurable_Y hX z T)
    (fun i => measurable_pi_apply _) hind
  refine lob_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom₁ hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hK := lob_Kop_ge hτ
  rw [← lob_L_eq]
  refine le_of_le_of_eq (lob_ifinish (P := 1) (K := lob_Kop τ ^ 2) (by omega) zero_le_one
    (by positivity) ?_ (lob_coef_Zmu_off h hσ hz hη hω μ) (lob_coef_Zmu_diag h hσ hz hη hω μ)
    h1 h2) (by ring)
  refine (lob_det_Zmu μ).trans ?_
  rw [one_mul, one_mul]
  have h0 : 0 ≤ ‖∑ i, ∑ j ∈ Finset.univ.erase i, (X ω i μ : ℂ)
        * Gm (diagonal σ) (X ω) z {Sum.inr μ} (Sum.inl i) (Sum.inl j) * (X ω j μ : ℂ)‖
      + ‖∑ i, Gm (diagonal σ) (X ω) z {Sum.inr μ} (Sum.inl i) (Sum.inl i)
        * ((X ω i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ := by positivity
  exact le_mul_of_one_le_left h0 (one_le_pow₀ hK)

end IProb

/-- `N^{-1/2} ≤ C_m^{1/2} Ψ_Θ` on `𝐃(τ, N)`, by (Im_m_geq_c). -/
private theorem lob_W_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N) :
    √((N : ℝ)⁻¹) ≤ √(mBoundConst τ) * PsiTheta σ Xm z := by
  have hτ := h.pos
  have hC := lob_Cm_pos hτ
  have hN : (0 : ℝ) < N := by exact_mod_cast lob_N_pos h
  have hη := hz.1
  obtain ⟨-, -, him⟩ := gen_prop_m_specDomain h hz
  have hΘ : 0 ≤ Theta σ Xm z := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΦ : 0 < PhiN N z := by unfold PhiN; positivity
  unfold PsiTheta
  rw [← Real.sqrt_mul hC.le]
  refine Real.sqrt_le_sqrt ?_
  have e : (N : ℝ)⁻¹ = z.im * PhiN N z := by
    unfold PhiN
    field_simp
  rw [e]
  have h1 : z.im ≤ mBoundConst τ * (mFun N σ z).im := by
    rw [inv_mul_le_iff₀ hC] at him
    exact him
  calc z.im * PhiN N z ≤ mBoundConst τ * (mFun N σ z).im * PhiN N z :=
        mul_le_mul_of_nonneg_right h1 hΦ.le
    _ ≤ mBoundConst τ * (((mFun N σ z).im + Theta σ Xm z) * PhiN N z) := by
        rw [mul_assoc]
        gcongr
        linarith

/-- For `τ, ε > 0` and every `K`: eventually `N ≥ 2`, `(1 + τ⁻¹)² ≤ N` and `K ≤ N^{ε/2}`. -/
private theorem lob_threshold2 {τ ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 2 ≤ N ∧ (1 + τ⁻¹) ^ 2 ≤ (N : ℝ) ∧ K ≤ (N : ℝ) ^ (ε / 2) := by
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  have ev := ((eventually_ge_atTop 2).and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ((1 + τ⁻¹) ^ 2))).and
    (t2.eventually_ge_atTop K)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ev
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1.1, (hN₁ N hN).1.2, (hN₁ N hN).2⟩⟩

/-- Lemma 5.2, (Lambda_o_Z_bound_initial). -/
theorem lambdaO_Z_bound_initial (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, 1 ≤ z.im → ∀ s : Fin M ⊕ Fin N,
      DomAt N ε D (fun ω => ‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z)
        (fun ω => PsiTheta σ (X ω) z) := by
  obtain ⟨N₁, h₁⟩ := lde_bilinear_cond C (half_pos hε) (D + 1 + 3 + 2)
  obtain ⟨N₂, h₂⟩ := lde_offdiag_cond C (half_pos hε) (D + 1 + 3 + 2)
  obtain ⟨N₃, h₃⟩ := lde_diag_cond C (half_pos hε) (D + 1 + 3 + 2)
  obtain ⟨N₄, h₄⟩ := lde_linear_cond C (half_pos hε) (D + 1 + 3 + 2)
  by_cases hτ1 : τ ≤ 1
  swap
  · refine ⟨0, fun N _ Ω _ _ M σ X hD => ?_⟩
    exfalso
    have h1 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (not_le.1 hτ1)
    linarith [hD.ratio_ge.trans hD.ratio_le]
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₅, h₅⟩ := hC₀ C (D + 1 + 3 + 2)
  set C₀' := max C₀ 0 with hC₀'
  obtain ⟨N₆, h₆⟩ := lob_threshold2 (τ := τ) hε (2 * lob_L τ C₀' * √(mBoundConst τ))
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ N₆),
    fun N hN Ω _ _ M σ X hD z hz hη s => ?_⟩
  have hN₁ : N ≥ N₁ := le_trans (by omega) hN
  have hN₂ : N ≥ N₂ := le_trans (by omega) hN
  have hN₃ : N ≥ N₃ := le_trans (by omega) hN
  have hN₄ : N ≥ N₄ := le_trans (by omega) hN
  have hN₅ : N ≥ N₅ := le_trans (by omega) hN
  have hN₆ : N ≥ N₆ := le_trans (by omega) hN
  obtain ⟨hN2, hN3, hK⟩ := h₆ N hN₆
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hM := lob_M_le h
  have hM0 := lob_M_pos h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lob_N_pos h
  have hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀'}ᶜ
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1 + 3 + 2))) := by
    refine le_trans (measure_mono ?_) (h₅ N hN₅ M X hD.entries hM)
    exact Set.compl_subset_compl.2 fun ω hω => (show ‖(X ω)ᵀ * X ω‖ ≤ C₀' from
      le_max_of_le_left hω)
  have hbil : lob_BilAt C N (ε / 2) (D + 1 + 3 + 2) Ω := fun x x' Y B => h₁ N hN₁ x x' Y B
  have hoff : lob_OffAt C N (ε / 2) (D + 1 + 3 + 2) Ω := fun x Y A => h₂ N hN₂ x Y A
  have hdiag : lob_DiagAt C N (ε / 2) (D + 1 + 3 + 2) Ω := fun x Y a => h₃ N hN₃ x Y a
  have hlin : lob_LinAt C N (ε / 2) (D + 1 + 3 + 2) Ω := fun x Y a => h₄ N hN₄ x Y a
  have hpair : ∀ s t : Fin M ⊕ Fin N, s ≠ t →
      DomAt N (ε / 2) (D + 1 + 3) (fun ω => (fun _ => (1 : ℝ)) ω * ‖G (diagonal σ) (X ω) z s t‖)
        (fun ω => sigS σ s * sigS σ t * (fun _ => lob_L τ C₀' * √((N : ℝ)⁻¹)) ω) := by
    simp only [one_mul]
    rintro (i | μ) (j | ν) hst
    · exact lob_icase_ij hτ hD hz hη hN2 hE hbil (fun e => hst (by rw [e]))
    · exact lob_icase_imu hτ hD hz hη hN2 hE hbil hlin i ν
    · exact lob_icase_mui hτ hD hz hη hN2 hE hbil hlin μ j
    · exact lob_icase_munu hτ hD hz hη hN2 hE hbil (fun e => hst (by rw [e]))
  have hΛ := lob_max (e := ε / 2) (D := D + 1) hσ hM0 (by omega) hM hN3 _ _ hpair
  have hZ4 : DomAt N (ε / 2) (D + 1 + 3) (fun ω => ‖ZS σ (X ω) z s‖)
      (fun _ => lob_L τ C₀' * √((N : ℝ)⁻¹)) := by
    rcases s with i | μ
    · exact lob_icase_Zi hτ hD hz hη hN2 hE hoff hdiag i
    · exact lob_icase_Zmu hτ hD hz hη hN2 hE hoff hdiag μ
  have hC0' : 0 ≤ C₀' := le_max_right _ _
  have hL : 0 ≤ lob_L τ C₀' := by
    unfold lob_L
    have := lob_Kop_ge hτ
    positivity
  have hZ : DomAt N (ε / 2) (D + 1) (fun ω => ‖ZS σ (X ω) z s‖)
      (fun _ => lob_L τ C₀' * √((N : ℝ)⁻¹)) :=
    DomAt.mono (by omega) (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => mul_nonneg hL (Real.sqrt_nonneg _)) le_rfl (by linarith) hZ4
  refine lob_union2 hN2 hΛ hZ fun ω hω₁ hω₂ => ?_
  simp only [one_mul] at hω₁
  have hW := lob_W_le h (X ω) hz
  have ha : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hNpos.le _
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos, add_halves]
  have hP : 0 ≤ PsiTheta σ (X ω) z := Real.sqrt_nonneg _
  have hsC : 0 ≤ √(mBoundConst τ) := Real.sqrt_nonneg _
  rw [hsplit]
  calc ‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z
      ≤ (N : ℝ) ^ (ε / 2) * (lob_L τ C₀' * √((N : ℝ)⁻¹))
        + (N : ℝ) ^ (ε / 2) * (lob_L τ C₀' * √((N : ℝ)⁻¹)) := add_le_add hω₂ hω₁
    _ = (N : ℝ) ^ (ε / 2) * (2 * lob_L τ C₀' * √((N : ℝ)⁻¹)) := by ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (2 * lob_L τ C₀' * (√(mBoundConst τ) * PsiTheta σ (X ω) z)) := by
        gcongr
    _ = (N : ℝ) ^ (ε / 2) * ((2 * lob_L τ C₀' * √(mBoundConst τ)) * PsiTheta σ (X ω) z) := by
        ring
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * PsiTheta σ (X ω) z) := by gcongr
    _ = _ := by ring

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` for every `N ≥ 1` -/

section Checks

/-- (Lambda_o_Z_bound) at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ s : Fin M ⊕ Fin N,
    DomAt N 1 1 (fun ω => xiInd σ (X ω) z * (‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z))
      (fun ω => PsiTheta σ (X ω) z) :=
  lambdaO_Z_bound (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- (Lambda_o_Z_bound_initial) at `τ = 1/2`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, 1 ≤ z.im → ∀ s : Fin M ⊕ Fin N,
    DomAt N 1 1 (fun ω => ‖ZS σ (X ω) z s‖ + LambdaO σ (X ω) z)
      (fun ω => PsiTheta σ (X ω) z) :=
  lambdaO_Z_bound_initial (1 / 2) (fun _ => 2) 1 1 (by norm_num) one_pos

end Checks

end Anisotropic

#print axioms Anisotropic.lambdaO_Z_bound
#print axioms Anisotropic.lambdaO_Z_bound_initial
