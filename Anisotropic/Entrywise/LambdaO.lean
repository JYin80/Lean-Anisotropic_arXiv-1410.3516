import Anisotropic.Entrywise.Control
import Anisotropic.Entrywise.Indep
import Anisotropic.Probability.LDE.Conditional
import Anisotropic.Probability.NormBound.Main
import Anisotropic.LinAlg.Ward
import Anisotropic.LinAlg.OpBound

/-! # Lemma 5.2: the entrywise large deviation steps for `Σ = diag(σ)`

(Gst_step1) and the `Z_s` part of (Lambda_o_Z_bound) on the event `Ξ` of Section 5.1, at fixed
`N`, pointwise in `z ∈ 𝐃` with (1+xm) at `z`. Each off-diagonal entry `G_{st}` is written by
(Gab), (Gij) or (Gia2) of Lemma 4.4 as a bilinear form in a row or column of `X` with
coefficients from a minor `G^{(T)}`, `|T| = 2`; `Z_s` is a quadratic form in row or column `s`
with coefficients from `G^{(s)}`. The large deviation estimates apply since these rows and
columns are independent of `G^{(T)}`. The coefficient sums are bounded on `Ξ` by the Ward
identities (GMaa4), (GMaa), (GMaa3) of Lemma 4.6 for the minors, (Gstu), (Gtt_bound), the bound
`Im m_i ≤ c⁻² σ_i² Im m` from (def_m_i), (Im_m_geq_c), and Lemma 4.8 for `‖XᵀX‖`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Families of entries and their independence from a minor -/

section Families

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Entries of `X` along an injective index map form a row family. -/
private theorem lambdaO_rowAssumption {C : ℕ → ℝ} {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) {ι : Type*} (g : ι → Fin M × Fin N) (hg : Function.Injective g) :
    RowAssumption C N (fun k ω => X ω (g k).1 (g k).2) where
  measurable k := hX.measurable (g k).1 (g k).2
  indep := hX.all.indep.precomp hg
  mean k := hX.mean (g k).1 (g k).2
  var k := hX.var (g k).1 (g k).2
  integrable_moment p k := hX.integrable_moment p (g k).1 (g k).2
  moment p k := hX.moment p (g k).1 (g k).2

/-- The entries of `G^{(T)}`, as one random variable. -/
private def lambdaO_Y {N : ℕ} (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (ω : Ω) : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) → ℂ :=
  fun st => Gm (diagonal σ) (X ω) z T st.1 st.2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private theorem lambdaO_measurable_Y {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) : Measurable (lambdaO_Y σ X z T) :=
  Measurable.of_eval fun st => measurable_Gm_apply σ hX.measurable z T st.1 st.2

/-- Entries of `X` in rows or columns of `T` are independent of `G^{(T)}`. -/
private theorem lambdaO_indep {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) {ι : Type*} (g : ι → Fin M × Fin N)
    (hg : ∀ k, Sum.inl (g k).1 ∈ T ∨ Sum.inr (g k).2 ∈ T) :
    IndepFun (fun ω (k : ι) => X ω (g k).1 (g k).2) (lambdaO_Y σ X z T) ℙ := by
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
private theorem lambdaO_prob3 {N : ℕ} (hN : 2 ≤ N) {D : ℝ} {S A₁ A₂ A₃ : Set Ω}
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
private theorem lambdaO_dom {N : ℕ} (hN : 2 ≤ N) {ε D : ℝ} {ξ ζ q₁ q₂ b₁ b₂ : Ω → ℝ}
    (E : Set Ω) (hE : ℙ Eᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₁ : DomAt N (ε / 2) (D + 2) q₁ b₁) (h₂ : DomAt N (ε / 2) (D + 2) q₂ b₂)
    (hdet : ∀ ω ∈ E, q₁ ω ≤ (N : ℝ) ^ (ε / 2) * b₁ ω → q₂ ω ≤ (N : ℝ) ^ (ε / 2) * b₂ ω →
      ξ ω ≤ (N : ℝ) ^ ε * ζ ω) :
    DomAt N ε D ξ ζ := by
  unfold DomAt at *
  refine lambdaO_prob3 hN ?_ hE h₁ h₂
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hc
  exact absurd (hdet ω hc.1.1 hc.1.2 hc.2) (not_le.2 hω)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The trivial domination `0 ≺ 0`. -/
private theorem lambdaO_dom_zero {N : ℕ} {ε D : ℝ} :
    DomAt (Ω := Ω) N ε D (fun _ => 0) (fun _ => 0) := by
  unfold DomAt
  simp

end Families

/-! ## Deterministic bounds on `Ξ` -/

section Det

/-- `τ ≤ 1` under the density assumptions. -/
private theorem lambdaO_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  rw [not_le] at hc
  linarith [inv_lt_one_of_one_lt₀ hc]

/-- `N > 0` under the density assumptions. -/
private theorem lambdaO_N_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `M > 0` under the density assumptions. -/
private theorem lambdaO_M_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 0 < M := by
  rcases Nat.eq_zero_or_pos M with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `M ≤ τ⁻¹ N` under the density assumptions. -/
private theorem lambdaO_M_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : (M : ℝ) ≤ τ⁻¹ * N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have := h.phi_upper
  rw [phiRatio, div_le_iff₀ hN] at this
  exact this

/-- `C_m > 0`. -/
private theorem lambdaO_mBoundConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)

/-- `0 < c_as ≤ 1`. -/
private theorem lambdaO_cas {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < mAsympLower τ ∧ mAsympLower τ ≤ 1 := by
  have hC := lambdaO_mBoundConst_pos hτ
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hD : 0 < 1 + mBoundConst τ * τ⁻¹ := by positivity
  exact ⟨inv_pos.2 hD, inv_le_one_of_one_le₀ (by nlinarith)⟩

/-- `σ̲_s > 0`. -/
private theorem lambdaO_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `σ̲_s ≤ τ⁻¹`. -/
private theorem lambdaO_sigS_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (s : Fin M ⊕ Fin N) : sigS σ s ≤ τ⁻¹ := by
  cases s with
  | inl i => exact h.bound_Sigma i
  | inr μ => exact (one_le_inv₀ h.pos).2 (lambdaO_tau_le_one h)

/-- `Λ ≥ 0`. -/
private theorem lambdaO_Lambda_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ Lambda σ Xm z :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun t =>
    div_nonneg (norm_nonneg _) (mul_pos (lambdaO_sigS_pos hσ s) (lambdaO_sigS_pos hσ t)).le

/-- `Λ_o ≥ 0`. -/
private theorem lambdaO_LambdaO_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (lambdaO_sigS_pos hσ _) (lambdaO_sigS_pos hσ _)).le

/-- `|G_{st}| ≤ σ̲_s σ̲_t Λ_o` for `s ≠ t`. -/
private theorem lambdaO_offdiag_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (lambdaO_sigS_pos hσ s) (lambdaO_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
    unfold LambdaO
    exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `Λ_o ≤ Λ`. -/
private theorem lambdaO_LambdaO_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : LambdaO σ Xm z ≤ Lambda σ Xm z := by
  refine Real.iSup_le (fun p => ?_) (lambdaO_Lambda_nonneg hσ Xm z)
  unfold Lambda
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove p.1.1)
  refine le_trans (le_of_eq ?_) (le_ciSup (f := fun t =>
    ‖G (diagonal σ) Xm z p.1.1 t - (if p.1.1 = t then mS N σ z p.1.1 else 0)‖
      / (sigS σ p.1.1 * sigS σ t)) (Set.finite_range _).bddAbove p.1.2)
  simp [p.2]

/-- On `Ξ`: `σ̲_s Λ_o ≤ c_as/4`. -/
private theorem lambdaO_small {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (s : Fin M ⊕ Fin N) : sigS σ s * LambdaO σ Xm z ≤ mAsympLower τ / 4 := by
  have hτ := h.pos
  have hL : LambdaO σ Xm z ≤ mAsympLower τ * τ / 4 :=
    ((lambdaO_LambdaO_le hσ Xm z).trans (hΞ.trans hlog)).trans (min_le_left _ _)
  have h0 := lambdaO_LambdaO_nonneg hσ Xm z
  calc sigS σ s * LambdaO σ Xm z ≤ τ⁻¹ * (mAsympLower τ * τ / 4) :=
        mul_le_mul (lambdaO_sigS_le h s) hL h0 (inv_pos.2 hτ).le
    _ = mAsympLower τ / 4 := by field_simp

/-- `‖x y / w‖ ≤ a b / l` from `‖x‖ ≤ a`, `‖y‖ ≤ b`, `0 < l ≤ ‖w‖`. -/
private theorem lambdaO_norm_div_le {x y w : ℂ} {a b l : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b)
    (hl : 0 < l) (hw : l ≤ ‖w‖) : ‖x * y / w‖ ≤ a * b / l := by
  rw [norm_div, norm_mul]
  have ha : 0 ≤ a := (norm_nonneg _).trans hx
  calc ‖x‖ * ‖y‖ / ‖w‖ ≤ a * b / ‖w‖ :=
        div_le_div_of_nonneg_right (mul_le_mul hx hy (norm_nonneg _) ha) (norm_nonneg _)
    _ ≤ a * b / l := div_le_div_of_nonneg_left (mul_nonneg ha ((norm_nonneg _).trans hy)) hl hw

/-- `C_T = 10 τ⁻¹ / c_as`. -/
private def lambdaO_CT (τ : ℝ) : ℝ := 10 * τ⁻¹ / mAsympLower τ

section OnXi

variable {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- One-index minor, off-diagonal: `|G^{(b)}_{ua}| ≤ (3/2) σ̲_u σ̲_a Λ_o`. -/
private theorem lambdaO_G1_off (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {b u a : Fin M ⊕ Fin N} (hub : u ≠ b) (hab : a ≠ b) (hua : u ≠ a) :
    ‖G1 (diagonal σ) Xm z b u a‖ ≤ 3 / 2 * (sigS σ u * sigS σ a * LambdaO σ Xm z) := by
  have hτ := h.pos
  obtain ⟨hca, -⟩ := lambdaO_cas hτ (lambdaO_tau_le_one h)
  rw [Gstu (posDef_diagonal_iff.2 hσ) Xm hz.1 b u a hub hab]
  have hbb := (Gtt_bound hc h hσ Xm hz hx hlog hΞ ∅ (by simp) b (by simp)).1
  rw [Gm_empty] at hbb
  have hsb := lambdaO_sigS_pos (N := N) hσ b
  have hsu := lambdaO_sigS_pos (N := N) hσ u
  have hsa := lambdaO_sigS_pos (N := N) hσ a
  have hL0 := lambdaO_LambdaO_nonneg hσ Xm z
  have hsm := lambdaO_small h hσ Xm z hlog hΞ b
  have hl : 0 < mAsympLower τ / 2 * sigS σ b := by positivity
  have hq := lambdaO_norm_div_le (lambdaO_offdiag_le hσ Xm z hub)
    (lambdaO_offdiag_le hσ Xm z hab.symm) hl hbb
  have e : sigS σ u * sigS σ b * LambdaO σ Xm z * (sigS σ b * sigS σ a * LambdaO σ Xm z)
      / (mAsympLower τ / 2 * sigS σ b)
      = (sigS σ u * sigS σ a * LambdaO σ Xm z) * (2 * (sigS σ b * LambdaO σ Xm z)
        / mAsympLower τ) := by
    field_simp
  rw [e] at hq
  have hr : 2 * (sigS σ b * LambdaO σ Xm z) / mAsympLower τ ≤ 1 / 2 := by
    rw [div_le_iff₀ hca]
    linarith
  have hw : 0 ≤ sigS σ u * sigS σ a * LambdaO σ Xm z := by positivity
  calc ‖G (diagonal σ) Xm z u a - G (diagonal σ) Xm z u b * G (diagonal σ) Xm z b a
        / G (diagonal σ) Xm z b b‖
      ≤ ‖G (diagonal σ) Xm z u a‖ + ‖G (diagonal σ) Xm z u b * G (diagonal σ) Xm z b a
        / G (diagonal σ) Xm z b b‖ := norm_sub_le _ _
    _ ≤ sigS σ u * sigS σ a * LambdaO σ Xm z + (sigS σ u * sigS σ a * LambdaO σ Xm z) * (1 / 2) :=
        add_le_add (lambdaO_offdiag_le hσ Xm z hua)
          (hq.trans (mul_le_mul_of_nonneg_left hr hw))
    _ = 3 / 2 * (sigS σ u * sigS σ a * LambdaO σ Xm z) := by ring

/-- One-index minor, diagonal: `|G^{(b)}_{uu} − G_{uu}| ≤ (2τ⁻¹/c_as) σ̲_u² Λ_o²`. -/
private theorem lambdaO_G1_diag (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {b u : Fin M ⊕ Fin N} (hub : u ≠ b) :
    ‖G1 (diagonal σ) Xm z b u u - G (diagonal σ) Xm z u u‖
      ≤ 2 * τ⁻¹ / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
  have hτ := h.pos
  obtain ⟨hca, -⟩ := lambdaO_cas hτ (lambdaO_tau_le_one h)
  rw [Gstu (posDef_diagonal_iff.2 hσ) Xm hz.1 b u u hub hub]
  have hbb := (Gtt_bound hc h hσ Xm hz hx hlog hΞ ∅ (by simp) b (by simp)).1
  rw [Gm_empty] at hbb
  have hsb := lambdaO_sigS_pos (N := N) hσ b
  have hsb' := lambdaO_sigS_le h b
  have hsu := lambdaO_sigS_pos (N := N) hσ u
  have hL0 := lambdaO_LambdaO_nonneg hσ Xm z
  have hl : 0 < mAsympLower τ / 2 * sigS σ b := by positivity
  have hq := lambdaO_norm_div_le (lambdaO_offdiag_le hσ Xm z hub)
    (lambdaO_offdiag_le hσ Xm z hub.symm) hl hbb
  have e : sigS σ u * sigS σ b * LambdaO σ Xm z * (sigS σ b * sigS σ u * LambdaO σ Xm z)
      / (mAsympLower τ / 2 * sigS σ b)
      = 2 * sigS σ b / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
    field_simp
  rw [e] at hq
  have hr : 2 * sigS σ b / mAsympLower τ ≤ 2 * τ⁻¹ / mAsympLower τ := by
    gcongr
  rw [show G (diagonal σ) Xm z u u - G (diagonal σ) Xm z u b * G (diagonal σ) Xm z b u
      / G (diagonal σ) Xm z b b - G (diagonal σ) Xm z u u
      = -(G (diagonal σ) Xm z u b * G (diagonal σ) Xm z b u / G (diagonal σ) Xm z b b) by ring,
    norm_neg]
  refine hq.trans ?_
  gcongr

/-- Two-index minor, diagonal: `|G^{(ab)}_{uu} − G_{uu}| ≤ C_T σ̲_u² Λ_o²`. -/
private theorem lambdaO_G2_diag (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {a b u : Fin M ⊕ Fin N} (hab : a ≠ b) (hua : u ≠ a) (hub : u ≠ b) :
    ‖Gm (diagonal σ) Xm z {a, b} u u - G (diagonal σ) Xm z u u‖
      ≤ lambdaO_CT τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
  have hτ := h.pos
  obtain ⟨hca, -⟩ := lambdaO_cas hτ (lambdaO_tau_le_one h)
  have hS : (insert a {b} : Finset (Fin M ⊕ Fin N)) = {a, b} := rfl
  have hstu := Gstu_minor (posDef_diagonal_iff.2 hσ) Xm hz.1 {b} a u u (by simpa using hab)
    (by simp [hua, hub]) (by simp [hua, hub])
  rw [hS] at hstu
  rw [hstu]
  have haa := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {b} (by simp) a (by simpa using hab)).1
  have hsa := lambdaO_sigS_pos (N := N) hσ a
  have hsa' := lambdaO_sigS_le h a
  have hsu := lambdaO_sigS_pos (N := N) hσ u
  have hL0 := lambdaO_LambdaO_nonneg hσ Xm z
  have hl : 0 < mAsympLower τ / 2 * sigS σ a := by positivity
  have hq := lambdaO_norm_div_le (lambdaO_G1_off hc h hσ hz hx hlog hΞ hub hab hua)
    (lambdaO_G1_off hc h hσ hz hx hlog hΞ hab hub hua.symm) hl haa
  have e : 3 / 2 * (sigS σ u * sigS σ a * LambdaO σ Xm z)
      * (3 / 2 * (sigS σ a * sigS σ u * LambdaO σ Xm z)) / (mAsympLower τ / 2 * sigS σ a)
      = 9 / 2 * sigS σ a / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
    field_simp
    ring
  rw [e] at hq
  have h1 := lambdaO_G1_diag hc h hσ hz hx hlog hΞ hub
  have hw : 0 ≤ (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by positivity
  have hti : 0 ≤ τ⁻¹ / mAsympLower τ := by positivity
  calc ‖Gm (diagonal σ) Xm z {b} u u
        - Gm (diagonal σ) Xm z {b} u a * Gm (diagonal σ) Xm z {b} a u
          / Gm (diagonal σ) Xm z {b} a a - G (diagonal σ) Xm z u u‖
      = ‖(G1 (diagonal σ) Xm z b u u - G (diagonal σ) Xm z u u)
        - Gm (diagonal σ) Xm z {b} u a * Gm (diagonal σ) Xm z {b} a u
          / Gm (diagonal σ) Xm z {b} a a‖ := by ring_nf
    _ ≤ ‖G1 (diagonal σ) Xm z b u u - G (diagonal σ) Xm z u u‖
        + ‖Gm (diagonal σ) Xm z {b} u a * Gm (diagonal σ) Xm z {b} a u
          / Gm (diagonal σ) Xm z {b} a a‖ := norm_sub_le _ _
    _ ≤ 2 * τ⁻¹ / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2
        + 9 / 2 * τ⁻¹ / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
        refine add_le_add h1 (hq.trans ?_)
        gcongr
    _ ≤ lambdaO_CT τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
        unfold lambdaO_CT
        have : 2 * τ⁻¹ / mAsympLower τ + 9 / 2 * τ⁻¹ / mAsympLower τ
            ≤ 10 * τ⁻¹ / mAsympLower τ := by
          rw [← add_div]
          gcongr
          nlinarith [(inv_pos.2 hτ).le]
        nlinarith

end OnXi

end Det

/-! ## Ward sums for minors with at most two removed indices -/

section Ward

/-- A sum over `ι` of a function vanishing off `p` is the sum over the subtype `p`. -/
private theorem lambdaO_sum_sub {R ι : Type*} [AddCommMonoid R] [Fintype ι] (p : ι → Prop)
    [Fintype (Subtype p)] (f : ι → R) (hf : ∀ x, ¬ p x → f x = 0) :
    ∑ x, f x = ∑ x : Subtype p, f x := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases hx : p x
    · simp [hx]
    · simp [hx, hf x hx]

/-- `‖(1 : Matrix b b ℝ).submatrix f id‖ ≤ 1` for injective `f`. -/
private theorem lambdaO_norm_sel {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
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
private theorem lambdaO_norm_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b] [Fintype m']
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
  have h1 := lambdaO_norm_sel f hf
  have h2 := lambdaO_norm_sel g hg
  calc ‖(1 : Matrix m' m' ℝ).submatrix f id‖ * ‖A‖ * ‖(1 : Matrix n' n' ℝ).submatrix g id‖
      ≤ 1 * ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := by ring

/-- `‖A|ᵀ A|‖ ≤ ‖Aᵀ A‖` for a submatrix along injective maps. -/
private theorem lambdaO_norm_XtX_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b]
    [Fintype m'] [Fintype n'] [DecidableEq b] [DecidableEq n'] (A : Matrix m' n' ℝ) (f : a → m')
    (g : b → n') (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖(A.submatrix f g)ᵀ * A.submatrix f g‖ ≤ ‖Aᵀ * A‖ := by
  classical
  rw [← conjTranspose_eq_transpose_of_trivial, ← conjTranspose_eq_transpose_of_trivial,
    l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose_mul_self]
  have h := lambdaO_norm_submatrix A f g hf hg
  exact mul_self_le_mul_self (norm_nonneg _) h

variable {N : ℕ} {σ : Fin M → ℝ}

/-- `Im G^{(T)}_{uu} ≥ 0`. -/
private theorem lambdaO_im_nonneg (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
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
private theorem lambdaO_ward_row (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (T : Finset (Fin M ⊕ Fin N)) (u : Fin M ⊕ Fin N) :
    ∑ ν, ‖Gm (diagonal σ) Xm z T u (Sum.inr ν)‖ ^ 2 = (Gm (diagonal σ) Xm z T u u).im / z.im := by
  have h := GMaa4_minor (posDef_diagonal_iff.2 hσ) Xm hz T (eI u)
  simpa only [ent_eI_eI] using h

/-- Entries of `G^{(T)}` in a removed row or column vanish. -/
private theorem lambdaO_Gm_mem_left (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {T : Finset (Fin M ⊕ Fin N)} {s : Fin M ⊕ Fin N}
    (hs : s ∈ T) (t : Fin M ⊕ Fin N) : Gm Sig Xm z T s t = 0 := by
  simp [Gm, hs]

private theorem lambdaO_Gm_mem_right (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {T : Finset (Fin M ⊕ Fin N)} (s : Fin M ⊕ Fin N)
    {t : Fin M ⊕ Fin N} (ht : t ∈ T) : Gm Sig Xm z T s t = 0 := by
  unfold Gm
  split_ifs <;> rfl

/-- The restricted model: `G^{(T)}_{st} = G(Σ|, X|)_{st}` for `s, t ∉ T`. -/
private theorem lambdaO_Gm_eq (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) {s t : Fin M ⊕ Fin N} (hs : s ∉ T) (ht : t ∉ T) :
    Gm (diagonal σ) Xm z T s t
      = G ((diagonal σ).submatrix (Subtype.val : idxM T → Fin M) Subtype.val)
          (Xm.submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxN T → Fin N)) z
          (toSub T s hs) (toSub T t ht) := by
  rw [Gm_eq_extend_G_of_diagonal σ (fun i => (hσ i).ne') Xm z T]
  simp [extend, hs, ht]

/-- `‖Σ|‖ ≤ τ⁻¹`. -/
private theorem lambdaO_norm_sig {τ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (T : Finset (Fin M ⊕ Fin N)) :
    ‖(diagonal σ).submatrix (Subtype.val : idxM T → Fin M) (Subtype.val : idxM T → Fin M)‖
      ≤ τ⁻¹ := by
  rw [submatrix_diagonal _ _ Subtype.val_injective, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (inv_pos.2 h.pos).le).2 fun i => ?_
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (hσ _)]
  exact h.bound_Sigma _

/-- (GMaa) for one row of a minor: `Σ_j |G^{(T)}_{ij}|² ≤ 2τ⁻²C₀ η⁻¹ Im G^{(T)}_{ii} + 2σ_i²`. -/
private theorem lambdaO_ward_MM {τ C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) (i : Fin M) :
    ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * (Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im
        + 2 * (σ i * σ i) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hτ := h.pos
  by_cases hi : Sum.inl i ∈ T
  · simp only [lambdaO_Gm_mem_left _ Xm z hi, norm_zero, Complex.zero_im, mul_zero,
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
    rw [lambdaO_sum_sub (fun j => Sum.inl j ∉ T)]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [lambdaO_Gm_eq hσ Xm z T hi j'.2]
      rfl
    · intro j hj
      rw [not_not] at hj
      simp [lambdaO_Gm_mem_right _ Xm z _ hj]
  have hdiag : Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)
      = G Sig' X' z (Sum.inl ⟨i, hi⟩) (Sum.inl ⟨i, hi⟩) := lambdaO_Gm_eq hσ Xm z T hi hi
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
  have him := lambdaO_im_nonneg hσ Xm hz T (Sum.inl i)
  have hs := lambdaO_norm_sig h hσ T
  have hx := (lambdaO_norm_XtX_submatrix Xm (Subtype.val : idxM T → Fin M)
    (Subtype.val : idxN T → Fin N) Subtype.val_injective Subtype.val_injective).trans hC₀
  have h1 : 2 * ‖Sig'‖ ^ 2 * ‖X'ᵀ * X'‖ / z.im ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im := by
    gcongr
  gcongr

/-- (GMaa3) for one row of a minor: `Σ_j |G^{(T)}_{νj}|² ≤ τ⁻²C₀ Σ_ρ |G^{(T)}_{νρ}|²`. -/
private theorem lambdaO_ward_NM {τ C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
    (T : Finset (Fin M ⊕ Fin N)) (ν : Fin N) :
    ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inl j)‖ ^ 2
      ≤ τ⁻¹ ^ 2 * C₀ * ∑ ρ, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inr ρ)‖ ^ 2 := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hτ := h.pos
  by_cases hν : Sum.inr ν ∈ T
  · simp [lambdaO_Gm_mem_left _ Xm z hν]
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
    rw [lambdaO_sum_sub (fun j => Sum.inl j ∉ T)]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [lambdaO_Gm_eq hσ Xm z T hν j'.2]
      rfl
    · intro j hj
      rw [not_not] at hj
      simp [lambdaO_Gm_mem_right _ Xm z _ hj]
  have hrhs : ∑ ρ, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inr ρ)‖ ^ 2
      = ∑ ρ' : idxN T, ‖G Sig' X' z (Sum.inr ⟨ν, hν⟩) (Sum.inr ρ')‖ ^ 2 := by
    rw [lambdaO_sum_sub (fun ρ => Sum.inr ρ ∉ T)]
    · refine Finset.sum_congr rfl fun ρ' _ => ?_
      rw [lambdaO_Gm_eq hσ Xm z T hν ρ'.2]
      rfl
    · intro ρ hρ
      rw [not_not] at hρ
      simp [lambdaO_Gm_mem_right _ Xm z _ hρ]
  rw [hlhs, hrhs]
  refine hW.trans ?_
  have hs := lambdaO_norm_sig h hσ T
  have hx := (lambdaO_norm_XtX_submatrix Xm (Subtype.val : idxM T → Fin M)
    (Subtype.val : idxN T → Fin N) Subtype.val_injective Subtype.val_injective).trans hC₀
  gcongr

end Ward

/-! ## Coefficient sums in terms of `(Im m + Θ + Λ_o²) Φ` -/

section Coeff

variable {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- `Q = (Im m + Θ + Λ_o²) Φ`, the square of the bound in (Gst_step1). -/
private def lambdaO_Q (N : ℕ) (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ((mFun N σ z).im + Theta σ Xm z + LambdaO σ Xm z ^ 2) * PhiN N z

/-- The predicate `Im G^{(T)}_{uu} ≤ Im G_{uu} + C_T σ̲_u² Λ_o²` for all `u`. -/
private def lambdaO_Good (τ : ℝ) (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) : Prop :=
  ∀ u, (Gm (diagonal σ) Xm z T u u).im
    ≤ (G (diagonal σ) Xm z u u).im + lambdaO_CT τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2

private theorem lambdaO_CT_nonneg (h : DensityAssumptions τ N σ) : 0 ≤ lambdaO_CT τ := by
  obtain ⟨hca, -⟩ := lambdaO_cas h.pos (lambdaO_tau_le_one h)
  unfold lambdaO_CT
  have := h.pos
  exact div_nonneg (by positivity) hca.le

/-- `Im G^{(T)}_{uu} ≤ Im G_{uu} + C_T σ̲_u² Λ_o²` for `u ∉ T`, from a deviation bound. -/
private theorem lambdaO_good_of (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (T : Finset (Fin M ⊕ Fin N))
    (hdev : ∀ u, u ∉ T → ‖Gm (diagonal σ) Xm z T u u - G (diagonal σ) Xm z u u‖
      ≤ lambdaO_CT τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2) :
    lambdaO_Good τ σ Xm z T := by
  intro u
  have hw : 0 ≤ lambdaO_CT τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
    exact mul_nonneg (mul_nonneg (lambdaO_CT_nonneg h) (mul_self_nonneg _)) (sq_nonneg _)
  by_cases hu : u ∈ T
  · rw [lambdaO_Gm_mem_left _ Xm z hu, Complex.zero_im]
    have h0 := lambdaO_im_nonneg hσ Xm hz.1 ∅ u
    rw [Gm_empty] at h0
    linarith
  · have h1 := (Complex.abs_im_le_norm _).trans (hdev u hu)
    rw [Complex.sub_im] at h1
    linarith [(abs_le.1 h1).2]

private theorem lambdaO_good_one (hc : 0 < c) (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (b : Fin M ⊕ Fin N) : lambdaO_Good τ σ Xm z {b} := by
  refine lambdaO_good_of h hσ hz {b} fun u hu => ?_
  have hub : u ≠ b := by simpa using hu
  refine (lambdaO_G1_diag hc h hσ hz hx hlog hΞ hub).trans ?_
  have hτ := h.pos
  obtain ⟨hca, -⟩ := lambdaO_cas hτ (lambdaO_tau_le_one h)
  have hw : 0 ≤ (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2 := by
    have := lambdaO_sigS_pos (N := N) hσ u
    positivity
  have : 2 * τ⁻¹ / mAsympLower τ ≤ lambdaO_CT τ := by
    unfold lambdaO_CT
    gcongr
    norm_num
  calc 2 * τ⁻¹ / mAsympLower τ * (sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2
      = 2 * τ⁻¹ / mAsympLower τ * ((sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2) := by ring
    _ ≤ lambdaO_CT τ * ((sigS σ u * sigS σ u) * LambdaO σ Xm z ^ 2) := by gcongr
    _ = _ := by ring

private theorem lambdaO_good_two (hc : 0 < c) (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {a b : Fin M ⊕ Fin N} (hab : a ≠ b) : lambdaO_Good τ σ Xm z {a, b} := by
  refine lambdaO_good_of h hσ hz {a, b} fun u hu => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  exact lambdaO_G2_diag hc h hσ hz hx hlog hΞ hab hu.1 hu.2

/-- Basic facts: `Im m > 0`, `Θ ≥ 0`, `Φ > 0`, `N⁻¹ ≤ C_m Q`. -/
private theorem lambdaO_basic (h : DensityAssumptions τ N σ) (hz : z ∈ specDomain τ N) :
    0 < (mFun N σ z).im ∧ 0 ≤ Theta σ Xm z ∧ 0 < PhiN N z ∧ 0 ≤ lambdaO_Q N σ Xm z ∧
      (N : ℝ)⁻¹ ≤ mBoundConst τ * lambdaO_Q N σ Xm z := by
  have hτ := h.pos
  have hC := lambdaO_mBoundConst_pos hτ
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have hη := hz.1
  obtain ⟨-, -, him⟩ := gen_prop_m_specDomain h hz
  have hm : 0 < (mFun N σ z).im := lt_of_lt_of_le (by positivity) him
  have hΘ : 0 ≤ Theta σ Xm z := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΦ : 0 < PhiN N z := by unfold PhiN; positivity
  have hL := sq_nonneg (LambdaO σ Xm z)
  refine ⟨hm, hΘ, hΦ, by unfold lambdaO_Q; positivity, ?_⟩
  have e : (N : ℝ)⁻¹ = z.im * PhiN N z := by
    unfold PhiN
    field_simp
  rw [e]
  have h1 : z.im ≤ mBoundConst τ * (mFun N σ z).im := by
    rw [inv_mul_le_iff₀ hC] at him
    exact him
  unfold lambdaO_Q
  calc z.im * PhiN N z ≤ mBoundConst τ * (mFun N σ z).im * PhiN N z :=
        mul_le_mul_of_nonneg_right h1 hΦ.le
    _ ≤ mBoundConst τ * (((mFun N σ z).im + Theta σ Xm z + LambdaO σ Xm z ^ 2) * PhiN N z) := by
        rw [mul_assoc]
        gcongr
        linarith

/-- `Σ_μ Im G_{μμ} ≤ N (Im m + Θ)`. -/
private theorem lambdaO_sum_im_N (h : DensityAssumptions τ N σ) :
    ∑ μ : Fin N, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)).im
      ≤ N * ((mFun N σ z).im + Theta σ Xm z) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∑ μ : Fin N, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)).im
      = N * (mN (diagonal σ) Xm z).im := by
    rw [← Complex.im_sum, mN, Complex.mul_im]
    simp only [Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast, Complex.inv_im,
      Complex.natCast_im, neg_zero, zero_div, zero_mul, add_zero]
    field_simp
  rw [e]
  have h1 : (mN (diagonal σ) Xm z).im ≤ (mFun N σ z).im + ThetaN σ Xm z := by
    have := (Complex.abs_im_le_norm (mN (diagonal σ) Xm z - mFun N σ z))
    rw [Complex.sub_im] at this
    unfold ThetaN
    linarith [(abs_le.1 this).2]
  have h2 : ThetaN σ Xm z ≤ Theta σ Xm z := le_add_of_nonneg_left (norm_nonneg _)
  gcongr
  linarith

/-- `Σ_i Im G_{ii} ≤ M (τ⁻² c⁻² Im m + Θ)`. -/
private theorem lambdaO_sum_im_M (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) :
    ∑ i : Fin M, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)).im
      ≤ M * (τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im + Theta σ Xm z) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast lambdaO_M_pos h
  have hτ := h.pos
  have hm := (lambdaO_basic (Xm := Xm) h hz).1
  have e : ∑ i : Fin M, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)).im
      = ∑ i, (mI N σ z i).im
        + (∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)).im := by
    rw [← Complex.im_sum, ← Complex.im_sum, ← Complex.add_im, ← Finset.sum_add_distrib]
    simp
  rw [e]
  have h1 : ∀ i, (mI N σ z i).im ≤ τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im := by
    intro i
    rw [im_mI]
    have hw : c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖ := hx i
    have hw0 : 0 < ‖1 + (σ i : ℂ) * mFun N σ z‖ := hc.trans_le hw
    rw [div_le_iff₀ (by positivity)]
    have hs : σ i ^ 2 ≤ τ⁻¹ ^ 2 := pow_le_pow_left₀ (hσ i).le (h.bound_Sigma i) 2
    have hc2 : c ^ 2 ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖ ^ 2 := pow_le_pow_left₀ hc.le hw 2
    have hcc : c⁻¹ ^ 2 * c ^ 2 = 1 := by field_simp
    calc σ i ^ 2 * (mFun N σ z).im ≤ τ⁻¹ ^ 2 * (mFun N σ z).im := by gcongr
      _ = τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im * c ^ 2 := by field_simp
      _ ≤ τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im * ‖1 + (σ i : ℂ) * mFun N σ z‖ ^ 2 := by
          gcongr
  have h2 : (∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)).im
      ≤ M * Theta σ Xm z := by
    refine (Complex.im_le_norm _).trans ?_
    have hT : ThetaM σ Xm z = (M : ℝ)⁻¹
        * ‖∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)‖ := by
      unfold ThetaM
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hT2 : ThetaM σ Xm z ≤ Theta σ Xm z := le_add_of_nonneg_right (norm_nonneg _)
    have : ‖∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)‖
        = M * ThetaM σ Xm z := by
      rw [hT]
      field_simp
    rw [this]
    gcongr
  calc ∑ i, (mI N σ z i).im
        + (∑ i, (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i) - mI N σ z i)).im
      ≤ ∑ _i : Fin M, τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im + M * Theta σ Xm z :=
        add_le_add (Finset.sum_le_sum fun i _ => h1 i) h2
    _ = M * (τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im + Theta σ Xm z) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Coeff

/-! ## The Ward sums of Lemma 5.2 -/

section Sums

variable {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- `N/η = N² Φ`. -/
private theorem lambdaO_N_div (h : DensityAssumptions τ N σ) (hz : z ∈ specDomain τ N) :
    (N : ℝ) / z.im = N ^ 2 * PhiN N z := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have := hz.1
  unfold PhiN
  field_simp

/-- `(k₁ Im m + k₂ Θ + k₃ Λ_o²) Φ ≤ (k₁ + k₂ + k₃) Q` for `k₁, k₂, k₃ ≥ 0`. -/
private theorem lambdaO_lin_le (h : DensityAssumptions τ N σ) (hz : z ∈ specDomain τ N)
    {k₁ k₂ k₃ : ℝ} (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂) (h₃ : 0 ≤ k₃) :
    (k₁ * (mFun N σ z).im + k₂ * Theta σ Xm z + k₃ * LambdaO σ Xm z ^ 2) * PhiN N z
      ≤ (k₁ + k₂ + k₃) * lambdaO_Q N σ Xm z := by
  obtain ⟨hm, hΘ, hΦ, -, -⟩ := lambdaO_basic (Xm := Xm) h hz
  have hL := sq_nonneg (LambdaO σ Xm z)
  unfold lambdaO_Q
  have e : (k₁ + k₂ + k₃) * (((mFun N σ z).im + Theta σ Xm z + LambdaO σ Xm z ^ 2) * PhiN N z)
      - (k₁ * (mFun N σ z).im + k₂ * Theta σ Xm z + k₃ * LambdaO σ Xm z ^ 2) * PhiN N z
      = PhiN N z * ((k₂ + k₃) * (mFun N σ z).im + (k₁ + k₃) * Theta σ Xm z
        + (k₁ + k₂) * LambdaO σ Xm z ^ 2) := by ring
  have : 0 ≤ PhiN N z * ((k₂ + k₃) * (mFun N σ z).im + (k₁ + k₃) * Theta σ Xm z
      + (k₁ + k₂) * LambdaO σ Xm z ^ 2) := by positivity
  linarith

/-- (GMaa4) summed over `μ`, with (Gstu): `Σ_{μν} |G^{(T)}_{μν}|² ≤ (2 + C_T) Q N²`. -/
private theorem lambdaO_sum_NN (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) {T : Finset (Fin M ⊕ Fin N)} (hT : lambdaO_Good τ σ Xm z T) :
    ∑ μ, ∑ ν, ‖Gm (diagonal σ) Xm z T (Sum.inr μ) (Sum.inr ν)‖ ^ 2
      ≤ (2 + lambdaO_CT τ) * lambdaO_Q N σ Xm z * N ^ 2 := by
  have hη := hz.1
  have hCT := lambdaO_CT_nonneg h
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  obtain ⟨hm, hΘ, hΦ, hQ, -⟩ := lambdaO_basic (Xm := Xm) h hz
  simp_rw [lambdaO_ward_row hσ Xm hη T]
  have h1 : ∀ μ : Fin N, (Gm (diagonal σ) Xm z T (Sum.inr μ) (Sum.inr μ)).im / z.im
      ≤ ((G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)).im
        + lambdaO_CT τ * LambdaO σ Xm z ^ 2) / z.im := by
    intro μ
    have := hT (Sum.inr μ)
    simp only [sigS, Sum.elim_inr, mul_one] at this
    gcongr
  refine (Finset.sum_le_sum fun μ _ => h1 μ).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h2 := lambdaO_sum_im_N (Xm := Xm) (z := z) h
  calc (∑ μ : Fin N, (G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr μ)).im
        + N * (lambdaO_CT τ * LambdaO σ Xm z ^ 2)) / z.im
      ≤ (N * ((mFun N σ z).im + Theta σ Xm z) + N * (lambdaO_CT τ * LambdaO σ Xm z ^ 2))
        / z.im := by gcongr
    _ = N / z.im * (1 * (mFun N σ z).im + 1 * Theta σ Xm z
        + lambdaO_CT τ * LambdaO σ Xm z ^ 2) := by ring
    _ = N ^ 2 * ((1 * (mFun N σ z).im + 1 * Theta σ Xm z
        + lambdaO_CT τ * LambdaO σ Xm z ^ 2) * PhiN N z) := by
        rw [lambdaO_N_div h hz]; ring
    _ ≤ N ^ 2 * ((1 + 1 + lambdaO_CT τ) * lambdaO_Q N σ Xm z) :=
        mul_le_mul_of_nonneg_left (lambdaO_lin_le h hz zero_le_one zero_le_one hCT)
          (by positivity)
    _ = (2 + lambdaO_CT τ) * lambdaO_Q N σ Xm z * N ^ 2 := by ring

/-- The constant of the bound on the `𝓘_M × 𝓘_M` block of a minor. -/
private def lambdaO_kMM (τ c C₀ : ℝ) : ℝ :=
  2 * τ⁻¹ ^ 3 * C₀ * (τ⁻¹ ^ 2 * c⁻¹ ^ 2 + 1 + τ⁻¹ ^ 2 * lambdaO_CT τ)
    + 2 * τ⁻¹ ^ 3 * mBoundConst τ

/-- (GMaa) summed over `i`, with (Gstu), (def_m_i) and (Im_m_geq_c):
`Σ_{ij} |G^{(T)}_{ij}|² ≤ k Q N²` on `{‖XᵀX‖ ≤ C₀}`. -/
private theorem lambdaO_sum_MM {C₀ : ℝ} (hc : 0 < c) (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀) {T : Finset (Fin M ⊕ Fin N)} (hT : lambdaO_Good τ σ Xm z T) :
    ∑ i, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ lambdaO_kMM τ c C₀ * lambdaO_Q N σ Xm z * N ^ 2 := by
  have hη := hz.1
  have hτ := h.pos
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have hCT := lambdaO_CT_nonneg h
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have hMle := lambdaO_M_le h
  obtain ⟨hm, hΘ, hΦ, hQ, hNQ⟩ := lambdaO_basic (Xm := Xm) h hz
  have hL := sq_nonneg (LambdaO σ Xm z)
  set Sim := ∑ i : Fin M, (Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im with hSim
  set Ss := ∑ i : Fin M, σ i * σ i with hSs
  have h1 : ∑ i, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl j)‖ ^ 2
      ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * Sim + 2 * Ss := by
    refine (Finset.sum_le_sum fun i _ => lambdaO_ward_MM h hσ Xm hη hC₀ T i).trans
      (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hSim0 : 0 ≤ Sim := Finset.sum_nonneg fun i _ => lambdaO_im_nonneg hσ Xm hη T _
  have hσσ : ∀ i, σ i * σ i ≤ τ⁻¹ ^ 2 := fun i => by
    rw [sq]; exact mul_le_mul (h.bound_Sigma i) (h.bound_Sigma i) (hσ i).le (inv_pos.2 hτ).le
  have h2 : Sim ≤ M * (τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im + 1 * Theta σ Xm z
      + τ⁻¹ ^ 2 * lambdaO_CT τ * LambdaO σ Xm z ^ 2) := by
    have hg : ∀ i : Fin M, (Gm (diagonal σ) Xm z T (Sum.inl i) (Sum.inl i)).im
        ≤ (G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)).im
          + τ⁻¹ ^ 2 * lambdaO_CT τ * LambdaO σ Xm z ^ 2 := by
      intro i
      have := hT (Sum.inl i)
      simp only [sigS, Sum.elim_inl] at this
      have hh : lambdaO_CT τ * (σ i * σ i) * LambdaO σ Xm z ^ 2
          ≤ τ⁻¹ ^ 2 * lambdaO_CT τ * LambdaO σ Xm z ^ 2 := by
        have := hσσ i
        have := mul_le_mul_of_nonneg_left this hCT
        nlinarith
      linarith
    refine (Finset.sum_le_sum fun i _ => hg i).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have := lambdaO_sum_im_M (Xm := Xm) hc h hσ hz hx
    nlinarith
  have h3 : Ss ≤ M * τ⁻¹ ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hσσ i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set X := τ⁻¹ ^ 2 * c⁻¹ ^ 2 * (mFun N σ z).im + 1 * Theta σ Xm z
      + τ⁻¹ ^ 2 * lambdaO_CT τ * LambdaO σ Xm z ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hXQ : X * PhiN N z ≤ (τ⁻¹ ^ 2 * c⁻¹ ^ 2 + 1 + τ⁻¹ ^ 2 * lambdaO_CT τ)
      * lambdaO_Q N σ Xm z := lambdaO_lin_le h hz (by positivity) zero_le_one (by positivity)
  have h4 : 2 * τ⁻¹ ^ 2 * C₀ / z.im * Sim
      ≤ 2 * τ⁻¹ ^ 3 * C₀ * (τ⁻¹ ^ 2 * c⁻¹ ^ 2 + 1 + τ⁻¹ ^ 2 * lambdaO_CT τ)
        * lambdaO_Q N σ Xm z * N ^ 2 := by
    have hA : 0 ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im := by positivity
    calc 2 * τ⁻¹ ^ 2 * C₀ / z.im * Sim ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * (M * X) := by gcongr
      _ ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * (τ⁻¹ * N * X) := by gcongr
      _ = 2 * τ⁻¹ ^ 3 * C₀ * (N / z.im) * X := by ring
      _ = 2 * τ⁻¹ ^ 3 * C₀ * N ^ 2 * (X * PhiN N z) := by rw [lambdaO_N_div h hz]; ring
      _ ≤ 2 * τ⁻¹ ^ 3 * C₀ * N ^ 2 * ((τ⁻¹ ^ 2 * c⁻¹ ^ 2 + 1 + τ⁻¹ ^ 2 * lambdaO_CT τ)
          * lambdaO_Q N σ Xm z) := by gcongr
      _ = _ := by ring
  have h5 : 2 * Ss ≤ 2 * τ⁻¹ ^ 3 * mBoundConst τ * lambdaO_Q N σ Xm z * N ^ 2 := by
    calc 2 * Ss ≤ 2 * (M * τ⁻¹ ^ 2) := by gcongr
      _ ≤ 2 * (τ⁻¹ * N * τ⁻¹ ^ 2) := by gcongr
      _ = 2 * τ⁻¹ ^ 3 * N ^ 2 * (N : ℝ)⁻¹ := by field_simp
      _ ≤ 2 * τ⁻¹ ^ 3 * N ^ 2 * (mBoundConst τ * lambdaO_Q N σ Xm z) := by gcongr
      _ = _ := by ring
  calc _ ≤ 2 * τ⁻¹ ^ 2 * C₀ / z.im * Sim + 2 * Ss := h1
    _ ≤ _ := add_le_add h4 h5
    _ = lambdaO_kMM τ c C₀ * lambdaO_Q N σ Xm z * N ^ 2 := by unfold lambdaO_kMM; ring

/-- (GMaa3) summed over `ν`: `Σ_{νj} |G^{(T)}_{νj}|² ≤ τ⁻²C₀(2 + C_T) Q N²` on
`{‖XᵀX‖ ≤ C₀}`. -/
private theorem lambdaO_sum_NM {C₀ : ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀) {T : Finset (Fin M ⊕ Fin N)}
    (hT : lambdaO_Good τ σ Xm z T) :
    ∑ ν, ∑ j, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inl j)‖ ^ 2
      ≤ τ⁻¹ ^ 2 * C₀ * (2 + lambdaO_CT τ) * lambdaO_Q N σ Xm z * N ^ 2 := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  refine (Finset.sum_le_sum fun ν _ => lambdaO_ward_NM h hσ Xm hz.1 hC₀ T ν).trans ?_
  rw [← Finset.mul_sum]
  calc τ⁻¹ ^ 2 * C₀ * ∑ ν, ∑ ρ, ‖Gm (diagonal σ) Xm z T (Sum.inr ν) (Sum.inr ρ)‖ ^ 2
      ≤ τ⁻¹ ^ 2 * C₀ * ((2 + lambdaO_CT τ) * lambdaO_Q N σ Xm z * N ^ 2) := by
        gcongr
        exact lambdaO_sum_NN h hσ hz hT
    _ = _ := by ring

/-- Diagonal sum over `𝓘_N` for a one-index minor: `Σ_μ |G^{(r)}_{μμ}|² ≤ C_G² C_m Q N²`. -/
private theorem lambdaO_diag_N (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (r : Fin M ⊕ Fin N) :
    ∑ μ, ‖Gm (diagonal σ) Xm z {r} (Sum.inr μ) (Sum.inr μ)‖ ^ 2
      ≤ (mAsympUpper c τ + 1) ^ 2 * mBoundConst τ * lambdaO_Q N σ Xm z * N ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  obtain ⟨-, -, -, hQ, hNQ⟩ := lambdaO_basic (Xm := Xm) h hz
  have hCG : 0 ≤ mAsympUpper c τ + 1 := by
    have : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
    linarith
  have hb : ∀ μ : Fin N, ‖Gm (diagonal σ) Xm z {r} (Sum.inr μ) (Sum.inr μ)‖ ^ 2
      ≤ (mAsympUpper c τ + 1) ^ 2 := by
    intro μ
    by_cases hμ : Sum.inr μ ∈ ({r} : Finset (Fin M ⊕ Fin N))
    · rw [lambdaO_Gm_mem_left _ Xm z hμ, norm_zero, zero_pow two_ne_zero]
      positivity
    · have := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {r} (by simp) _ hμ).2
      simp only [sigS, Sum.elim_inr, mul_one] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
  refine (Finset.sum_le_sum fun μ _ => hb μ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (N : ℝ) * (mAsympUpper c τ + 1) ^ 2
      = (mAsympUpper c τ + 1) ^ 2 * N ^ 2 * (N : ℝ)⁻¹ := by field_simp
    _ ≤ (mAsympUpper c τ + 1) ^ 2 * N ^ 2 * (mBoundConst τ * lambdaO_Q N σ Xm z) := by gcongr
    _ = _ := by ring

/-- Diagonal sum over `𝓘_M` for a one-index minor:
`Σ_i |G^{(r)}_{ii}|² ≤ C_G² τ⁻³ C_m Q N²`. -/
private theorem lambdaO_diag_M (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (r : Fin M ⊕ Fin N) :
    ∑ i, ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
      ≤ (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * mBoundConst τ * lambdaO_Q N σ Xm z * N ^ 2 := by
  have hτ := h.pos
  have hN : (0 : ℝ) < N := by exact_mod_cast lambdaO_N_pos h
  have hMle := lambdaO_M_le h
  obtain ⟨-, -, -, hQ, hNQ⟩ := lambdaO_basic (Xm := Xm) h hz
  have hCG : 0 ≤ mAsympUpper c τ + 1 := by
    have : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
    linarith
  have hb : ∀ i : Fin M, ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
      ≤ (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 2 := by
    intro i
    by_cases hi : Sum.inl i ∈ ({r} : Finset (Fin M ⊕ Fin N))
    · rw [lambdaO_Gm_mem_left _ Xm z hi, norm_zero, zero_pow two_ne_zero]
      positivity
    · have := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {r} (by simp) _ hi).2
      simp only [sigS, Sum.elim_inl] at this
      have h2 : ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖
          ≤ (mAsympUpper c τ + 1) * τ⁻¹ :=
        this.trans (mul_le_mul_of_nonneg_left (h.bound_Sigma i) hCG)
      calc ‖Gm (diagonal σ) Xm z {r} (Sum.inl i) (Sum.inl i)‖ ^ 2
          ≤ ((mAsympUpper c τ + 1) * τ⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = _ := by ring
  refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (M : ℝ) * ((mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 2)
      ≤ τ⁻¹ * N * ((mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 2) := by gcongr
    _ = (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * N ^ 2 * (N : ℝ)⁻¹ := by field_simp
    _ ≤ (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * N ^ 2 * (mBoundConst τ * lambdaO_Q N σ Xm z) := by
        gcongr
    _ = _ := by ring

/-- `S ≤ k Q N²` gives `√S / N ≤ √k √Q`. -/
private theorem lambdaO_sqrt_le {S k Q : ℝ} {N : ℕ} (hN : 0 < N) (hk : 0 ≤ k) (hQ : 0 ≤ Q)
    (hS : S ≤ k * Q * N ^ 2) : √S / N ≤ √k * √Q := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN', ← Real.sqrt_mul hk, ← Real.sqrt_sq hN'.le, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hS

end Sums

/-! ## The five cases of Lemma 5.2 on `Ξ` -/

section Cases

/-- `(X A Xᵀ)_{ij} = Σ_{μν} X_{iμ} A_{μν} X_{jν}`. -/
private theorem lambdaO_exp_MM {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i j : Fin M) :
    (Xhat Xm * A * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl j)
      = ∑ μ, ∑ ν, (Xm i μ : ℂ) * A (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, fromBlocks_apply₁₂,
    map_apply, zero_add,
    transpose_apply, Finset.sum_mul, mul_zero]
  rw [Finset.sum_comm]

/-- `(Xᵀ A X)_{μν} = Σ_{ij} X_{iμ} A_{ij} X_{jν}`. -/
private theorem lambdaO_exp_NN {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (μ ν : Fin N) :
    ((Xhat Xm)ᵀ * A * Xhat Xm) (Sum.inr μ) (Sum.inr ν)
      = ∑ i, ∑ j, (Xm i μ : ℂ) * A (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, transpose_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₂, map_apply, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Finset.sum_mul, mul_zero]
  rw [Finset.sum_comm]

/-- `(X A X)_{iμ} = Σ_{νj} X_{iν} A_{νj} X_{jμ}`. -/
private theorem lambdaO_exp_MN {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M) (μ : Fin N) :
    (Xhat Xm * A * Xhat Xm) (Sum.inl i) (Sum.inr μ)
      = ∑ ν, ∑ j, (Xm i ν : ℂ) * A (Sum.inr ν) (Sum.inl j) * (Xm j μ : ℂ) := by
  simp only [Xhat, cplx, Complex.coe_algebraMap, mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, fromBlocks_apply₁₂,
    map_apply, zero_add,
    Finset.sum_mul, fromBlocks_apply₂₂, mul_zero, add_zero]
  rw [Finset.sum_comm]

/-- Splitting a quadratic form into its off-diagonal and diagonal parts. -/
private theorem lambdaO_quad_split {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
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

variable {τ c : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- `C_G = C_as + 1 ≥ 1`. -/
private theorem lambdaO_CG_ge (hc : 0 < c) : 1 ≤ mAsympUpper c τ + 1 := by
  have : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  linarith

/-- Case `G_{ij}`, `i ≠ j`: (Gab) and (Gtt_bound). -/
private theorem lambdaO_det_ij (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {i j : Fin M} (hij : i ≠ j) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl j)‖
      ≤ σ i * σ j * (mAsympUpper c τ + 1) ^ 2 * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inl j} (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖ := by
  rw [(Gab hσ Xm hz.1 i j hij).2.2, lambdaO_exp_MM]
  have h1 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ ∅ (by simp) (Sum.inl i) (by simp)).2
  rw [Gm_empty] at h1
  have h2 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {Sum.inl i} (by simp) (Sum.inl j)
    (by simpa using hij.symm)).2
  simp only [sigS, Sum.elim_inl] at h1 h2
  rw [norm_mul, norm_mul]
  have hCG := lambdaO_CG_ge (τ := τ) hc
  calc ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inl i)‖ * ‖G1 (diagonal σ) Xm z (Sum.inl i)
        (Sum.inl j) (Sum.inl j)‖ * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inl j) (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖
      ≤ (mAsympUpper c τ + 1) * σ i * ((mAsympUpper c τ + 1) * σ j) * ‖∑ μ, ∑ ν, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inl j) (Sum.inr μ) (Sum.inr ν) * (Xm j ν : ℂ)‖ := by
        have : 0 ≤ (mAsympUpper c τ + 1) * σ i := mul_nonneg (by linarith) (hσ i).le
        gcongr
    _ = _ := by ring

/-- Case `G_{μν}`, `μ ≠ ν`: (Gij) and (Gtt_bound). -/
private theorem lambdaO_det_munu (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    {μ ν : Fin N} (hμν : μ ≠ ν) :
    ‖G (diagonal σ) Xm z (Sum.inr μ) (Sum.inr ν)‖
      ≤ 1 * 1 * (mAsympUpper c τ + 1) ^ 2 * ‖∑ i, ∑ j, (Xm i μ : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inr μ, Sum.inr ν} (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ)‖ := by
  rw [(Gij (posDef_diagonal_iff.2 hσ) Xm hz.1 μ ν hμν).2.2, lambdaO_exp_NN]
  have h1 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ ∅ (by simp) (Sum.inr μ) (by simp)).2
  rw [Gm_empty] at h1
  have h2 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {Sum.inr μ} (by simp) (Sum.inr ν)
    (by simpa using hμν.symm)).2
  simp only [sigS, Sum.elim_inr, mul_one] at h1 h2
  rw [norm_mul, norm_mul]
  have hCG := lambdaO_CG_ge (τ := τ) hc
  calc _ ≤ (mAsympUpper c τ + 1) * (mAsympUpper c τ + 1) * ‖∑ i, ∑ j, (Xm i μ : ℂ)
        * G2 (diagonal σ) Xm z (Sum.inr μ) (Sum.inr ν) (Sum.inl i) (Sum.inl j) * (Xm j ν : ℂ)‖ := by
        gcongr
    _ = _ := by ring

/-- Case `G_{iμ}`: (Gia2) and (Gtt_bound), with the sum over `ν ≠ μ`, `j ≠ i`. -/
private theorem lambdaO_det_imu (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
    (i : Fin M) (μ : Fin N) :
    ‖G (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)‖
      ≤ σ i * 1 * (mAsympUpper c τ + 1) ^ 2 * (‖∑ ν : {ν : Fin N // ν ≠ μ},
        ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖) := by
  rw [(Gia2 hσ Xm hz.1 i μ).2, lambdaO_exp_MN]
  have hsub : ∑ ν, ∑ j, (Xm i ν : ℂ)
      * G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ) (Sum.inr ν) (Sum.inl j) * (Xm j μ : ℂ)
      = ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)
        * (Xm j.1 μ : ℂ) := by
    rw [show G2 (diagonal σ) Xm z (Sum.inl i) (Sum.inr μ)
      = Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} from rfl]
    rw [lambdaO_sum_sub (fun ν => ν ≠ μ)]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [lambdaO_sum_sub (fun j => j ≠ i)]
      intro j hj
      rw [not_not] at hj
      rw [hj, lambdaO_Gm_mem_right _ Xm z _ (by simp)]
      ring
    · intro ν hν
      rw [not_not] at hν
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hν, lambdaO_Gm_mem_left _ Xm z (by simp)]
      ring
  rw [hsub]
  have h1 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ ∅ (by simp) (Sum.inl i) (by simp)).2
  rw [Gm_empty] at h1
  have h2 := (Gtt_bound hc h hσ Xm hz hx hlog hΞ {Sum.inl i} (by simp) (Sum.inr μ) (by simp)).2
  simp only [sigS, Sum.elim_inl, Sum.elim_inr, mul_one] at h1 h2
  rw [norm_mul, norm_mul]
  have hCG := lambdaO_CG_ge (τ := τ) hc
  have h3 : ‖-(Xm i μ : ℂ) + ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
      (Xm i ν.1 : ℂ) * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)
        * (Xm j.1 μ : ℂ)‖
      ≤ ‖∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp only [norm_neg, Finset.univ_unique, Finset.sum_singleton, one_mul]
    ring
  calc _ ≤ (mAsympUpper c τ + 1) * σ i * (mAsympUpper c τ + 1) * (‖∑ ν : {ν : Fin N // ν ≠ μ},
        ∑ j : {j : Fin M // j ≠ i}, (Xm i ν.1 : ℂ)
        * Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1) * (Xm j.1 μ : ℂ)‖
        + ‖∑ _u : Unit, (1 : ℂ) * (Xm i μ : ℂ)‖) := by
        have : 0 ≤ (mAsympUpper c τ + 1) * σ i := mul_nonneg (by linarith) (hσ i).le
        gcongr
    _ = _ := by ring

/-- Case `Z_i`: off-diagonal and diagonal parts of the quadratic form in row `i`. -/
private theorem lambdaO_det_Zi (i : Fin M) :
    ‖Zi σ Xm z i‖
      ≤ 1 * (‖∑ μ, ∑ ν ∈ Finset.univ.erase μ, (Xm i μ : ℂ)
          * Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν) * (Xm i ν : ℂ)‖
        + ‖∑ μ, Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr μ)
          * ((Xm i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖) := by
  rw [one_mul, Zi, lambdaO_exp_MM]
  rw [lambdaO_quad_split (fun μ => Xm i μ)
    (fun μ ν => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν)) N]
  exact norm_add_le _ _

/-- Case `Z_μ`: off-diagonal and diagonal parts of the quadratic form in column `μ`. -/
private theorem lambdaO_det_Zmu (μ : Fin N) :
    ‖Zmu σ Xm z μ‖
      ≤ 1 * (‖∑ i, ∑ j ∈ Finset.univ.erase i, (Xm i μ : ℂ)
          * Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j) * (Xm j μ : ℂ)‖
        + ‖∑ i, Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl i)
          * ((Xm i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖) := by
  rw [one_mul, Zmu, lambdaO_exp_NN]
  rw [lambdaO_quad_split (fun i => Xm i μ)
    (fun i j => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j)) N]
  exact norm_add_le _ _

end Cases

/-! ## The coefficient bounds of the large deviation estimates -/

section Bounds

/-- The constant `k` with every coefficient sum `≤ k Q N²`. -/
private def lambdaO_k (τ c C₀ : ℝ) : ℝ :=
  (2 + lambdaO_CT τ) + lambdaO_kMM τ c C₀ + τ⁻¹ ^ 2 * C₀ * (2 + lambdaO_CT τ)
    + (mAsympUpper c τ + 1) ^ 2 * mBoundConst τ
    + (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * mBoundConst τ + mBoundConst τ

variable {τ c C₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- The six summands of `k` are nonnegative. -/
private theorem lambdaO_k_parts (hc : 0 < c) (h : DensityAssumptions τ N σ) (hC0 : 0 ≤ C₀) :
    0 ≤ 2 + lambdaO_CT τ ∧ 0 ≤ lambdaO_kMM τ c C₀ ∧ 0 ≤ τ⁻¹ ^ 2 * C₀ * (2 + lambdaO_CT τ) ∧
      0 ≤ (mAsympUpper c τ + 1) ^ 2 * mBoundConst τ ∧
      0 ≤ (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * mBoundConst τ ∧ 0 ≤ mBoundConst τ := by
  have hτ := h.pos
  have hCT := lambdaO_CT_nonneg h
  have hCm := (lambdaO_mBoundConst_pos hτ).le
  have h2 : 0 ≤ 2 + lambdaO_CT τ := by linarith
  refine ⟨h2, ?_, by positivity, by positivity, by positivity, hCm⟩
  unfold lambdaO_kMM
  positivity

private theorem lambdaO_le_k (hc : 0 < c) (h : DensityAssumptions τ N σ) (hC0 : 0 ≤ C₀) :
    2 + lambdaO_CT τ ≤ lambdaO_k τ c C₀ ∧ lambdaO_kMM τ c C₀ ≤ lambdaO_k τ c C₀ ∧
      τ⁻¹ ^ 2 * C₀ * (2 + lambdaO_CT τ) ≤ lambdaO_k τ c C₀ ∧
      (mAsympUpper c τ + 1) ^ 2 * mBoundConst τ ≤ lambdaO_k τ c C₀ ∧
      (mAsympUpper c τ + 1) ^ 2 * τ⁻¹ ^ 3 * mBoundConst τ ≤ lambdaO_k τ c C₀ ∧
      mBoundConst τ ≤ lambdaO_k τ c C₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lambdaO_k_parts hc h hC0
  unfold lambdaO_k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- From `S ≤ k' Q N²` with `k' ≤ k`: `√S / N ≤ √k √Q`. -/
private theorem lambdaO_coef (hc : 0 < c) (h : DensityAssumptions τ N σ) (hz : z ∈ specDomain τ N)
    (hC0 : 0 ≤ C₀) {S k' : ℝ} (hk' : k' ≤ lambdaO_k τ c C₀)
    (hS : S ≤ k' * lambdaO_Q N σ Xm z * N ^ 2) :
    √S / N ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  obtain ⟨-, -, -, hQ, -⟩ := lambdaO_basic (Xm := Xm) h hz
  have hk := (lambdaO_k_parts hc h hC0).2.2.2.2.2.trans (lambdaO_le_k hc h hC0).2.2.2.2.2
  refine lambdaO_sqrt_le (lambdaO_N_pos h) hk hQ (hS.trans ?_)
  gcongr

/-- The off-diagonal bound is at most the full Hilbert–Schmidt bound. -/
private theorem lambdaO_off_le {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℂ) :
    ldeOffBound N A ≤ √(∑ a, ∑ b, ‖A a b‖ ^ 2) / N := by
  unfold ldeOffBound
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun _ _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

section OnXi

variable (hc : 0 < c) (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
  (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
  (hlog : (Real.log N)⁻¹ ≤ xiThr c τ) (hΞ : Lambda σ Xm z ≤ (Real.log N)⁻¹)
  (hC₀ : ‖Xmᵀ * Xm‖ ≤ C₀)
include hc h hσ hz hx hlog hΞ hC₀

private theorem lambdaO_coef_ij {i j : Fin M} (hij : i ≠ j) :
    √(∑ μ, ∑ ν, ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inl j} (Sum.inr μ) (Sum.inr ν)‖ ^ 2) / N
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).1
    (lambdaO_sum_NN h hσ hz (lambdaO_good_two hc h hσ hz hx hlog hΞ (by simpa using hij)))

private theorem lambdaO_coef_munu {μ ν : Fin N} (hμν : μ ≠ ν) :
    √(∑ i, ∑ j, ‖Gm (diagonal σ) Xm z {Sum.inr μ, Sum.inr ν} (Sum.inl i) (Sum.inl j)‖ ^ 2) / N
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).2.1
    (lambdaO_sum_MM hc h hσ hz hx hC₀ (lambdaO_good_two hc h hσ hz hx hlog hΞ (by simpa using hμν)))

private theorem lambdaO_coef_imu (i : Fin M) (μ : Fin N) :
    √(∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
      ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)‖ ^ 2) / N
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  have e : ∑ ν, ∑ j, ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν) (Sum.inl j)‖ ^ 2
      = ∑ ν : {ν : Fin N // ν ≠ μ}, ∑ j : {j : Fin M // j ≠ i},
        ‖Gm (diagonal σ) Xm z {Sum.inl i, Sum.inr μ} (Sum.inr ν.1) (Sum.inl j.1)‖ ^ 2 := by
    rw [lambdaO_sum_sub (fun ν => ν ≠ μ)]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [lambdaO_sum_sub (fun j => j ≠ i)]
      intro j hj
      rw [not_not] at hj
      rw [hj, lambdaO_Gm_mem_right _ Xm z _ (by simp)]
      simp
    · intro ν hν
      rw [not_not] at hν
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hν, lambdaO_Gm_mem_left _ Xm z (by simp)]
      simp
  rw [← e]
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).2.2.1
    (lambdaO_sum_NM h hσ hz hC₀ (lambdaO_good_two hc h hσ hz hx hlog hΞ (by simp)))

omit hσ hx hlog hΞ in
private theorem lambdaO_coef_lin :
    ldeLinBound N (fun _ : Unit => (1 : ℂ)) ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  obtain ⟨-, -, -, hQ, hNQ⟩ := lambdaO_basic (Xm := Xm) h hz
  have hk := (lambdaO_le_k hc h hC0).2.2.2.2.2
  unfold ldeLinBound
  rw [← Real.sqrt_mul ((lambdaO_k_parts hc h hC0).2.2.2.2.2.trans hk)]
  refine Real.sqrt_le_sqrt ?_
  simp only [Finset.univ_unique, Finset.sum_singleton, norm_one, one_pow, one_div]
  exact hNQ.trans (by gcongr)

private theorem lambdaO_coef_Zi_off (i : Fin M) :
    ldeOffBound N (fun μ ν => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr ν))
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  refine (lambdaO_off_le _).trans ?_
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).1
    (lambdaO_sum_NN h hσ hz (lambdaO_good_one hc h hσ hz hx hlog hΞ _))

private theorem lambdaO_coef_Zi_diag (i : Fin M) :
    ldeDiagBound N (fun μ => Gm (diagonal σ) Xm z {Sum.inl i} (Sum.inr μ) (Sum.inr μ))
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).2.2.2.1
    (lambdaO_diag_N hc h hσ hz hx hlog hΞ _)

private theorem lambdaO_coef_Zmu_off (μ : Fin N) :
    ldeOffBound N (fun i j => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl j))
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  refine (lambdaO_off_le _).trans ?_
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).2.1
    (lambdaO_sum_MM hc h hσ hz hx hC₀ (lambdaO_good_one hc h hσ hz hx hlog hΞ _))

private theorem lambdaO_coef_Zmu_diag (μ : Fin N) :
    ldeDiagBound N (fun i => Gm (diagonal σ) Xm z {Sum.inr μ} (Sum.inl i) (Sum.inl i))
      ≤ √(lambdaO_k τ c C₀) * √(lambdaO_Q N σ Xm z) := by
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hC₀
  exact lambdaO_coef hc h hz hC0 (lambdaO_le_k hc h hC0).2.2.2.2.1
    (lambdaO_diag_M hc h hσ hz hx hlog hΞ _)

end OnXi

/-- The final step on `Ξ`: `1_Ξ g ≤ N^ε W √Q` from `g ≤ W C (q₁ + q₂)`, `q_a ≤ N^{ε/2} b_a`,
`b_a ≤ s √Q` and `2 C s ≤ N^{ε/2}`. -/
private theorem lambdaO_xi_finish {N : ℕ} (hN : 0 < N) {ε : ℝ} {σ : Fin M → ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {g W K s q₁ q₂ b₁ b₂ : ℝ} (hW : 0 ≤ W) (hK0 : 0 ≤ K)
    (hK : 2 * K * s ≤ (N : ℝ) ^ (ε / 2))
    (hdet : Lambda σ Xm z ≤ (Real.log N)⁻¹ →
      g ≤ W * K * (q₁ + q₂) ∧ b₁ ≤ s * √(lambdaO_Q N σ Xm z) ∧ b₂ ≤ s * √(lambdaO_Q N σ Xm z))
    (h₁ : q₁ ≤ (N : ℝ) ^ (ε / 2) * b₁) (h₂ : q₂ ≤ (N : ℝ) ^ (ε / 2) * b₂) :
    xiInd σ Xm z * g ≤ (N : ℝ) ^ ε * (W * √(lambdaO_Q N σ Xm z)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have he : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hN'.le _
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN', add_halves]
  set B := √(lambdaO_Q N σ Xm z)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  unfold xiInd
  split_ifs with hΞ
  · obtain ⟨hg, hb₁, hb₂⟩ := hdet hΞ
    set e := (N : ℝ) ^ (ε / 2)
    rw [one_mul, hsplit]
    have hq : q₁ + q₂ ≤ e * (2 * s * B) := by
      have := add_le_add (h₁.trans (mul_le_mul_of_nonneg_left hb₁ he))
        (h₂.trans (mul_le_mul_of_nonneg_left hb₂ he))
      linarith
    have hWK : 0 ≤ W * K := mul_nonneg hW hK0
    calc g ≤ W * K * (q₁ + q₂) := hg
      _ ≤ W * K * (e * (2 * s * B)) := mul_le_mul_of_nonneg_left hq hWK
      _ = W * e * B * (2 * K * s) := by ring
      _ ≤ W * e * B * e := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = e * e * (W * B) := by ring
  · rw [zero_mul]
    exact mul_nonneg (Real.rpow_nonneg hN'.le _) (mul_nonneg hW hB)

end Bounds

/-! ## The probabilistic step for each case -/

section Prob

/-- The bilinear large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lambdaO_BilAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι κ β : Type} [Fintype ι] [Fintype κ] [MeasurableSpace β] (x : ι → Ω → ℝ)
    (x' : κ → Ω → ℝ) (Y : Ω → β) (B : β → ι → κ → ℂ),
    RowAssumption C N (Sum.elim x x') → Measurable Y → (∀ i j, Measurable fun b => B b i j) →
    IndepFun (fun ω (s : ι ⊕ κ) => Sum.elim x x' s ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, ∑ j, (x i ω : ℂ) * B (Y ω) i j * (x' j ω : ℂ)‖)
      (fun ω => √(∑ i, ∑ j, ‖B (Y ω) i j‖ ^ 2) / N)

/-- The off-diagonal large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lambdaO_OffAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (A : β → ι → ι → ℂ), RowAssumption C N x → Measurable Y →
    (∀ i j, Measurable fun b => A b i j) → IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i, (x i ω : ℂ) * A (Y ω) i j * (x j ω : ℂ)‖)
      (fun ω => ldeOffBound N (A (Y ω)))

/-- The diagonal large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lambdaO_DiagAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (a : β → ι → ℂ), RowAssumption C N x → Measurable Y → (∀ i, Measurable fun b => a b i) →
    IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * ((x i ω : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖)
      (fun ω => ldeDiagBound N (a (Y ω)))

/-- The linear large deviation estimate at fixed `N`, `ε`, `D`. -/
private def lambdaO_LinAt (C : ℕ → ℝ) (N : ℕ) (ε D : ℝ) (Ω : Type) [MeasureSpace Ω] : Prop :=
  ∀ {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
    (a : β → ι → ℂ), RowAssumption C N x → Measurable Y → (∀ i, Measurable fun b => a b i) →
    IndepFun (fun ω i => x i ω) Y ℙ →
    DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * (x i ω : ℂ)‖) (fun ω => ldeLinBound N (a (Y ω)))

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {τ c C₀ ε D : ℝ}
  {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {z : ℂ}

/-- `0 ≤ √k √Q`. -/
private theorem lambdaO_zero_le (k Q : ℝ) : (0 : ℝ) ≤ √k * √Q :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem lambdaO_case_ij (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lambdaO_BilAt C N (ε / 2) (D + 2) Ω) {i j : Fin M} (hij : i ≠ j) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inl j)‖)
      (fun ω => sigS (N := N) σ (Sum.inl i) * sigS (N := N) σ (Sum.inl j)
        * √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
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
  have hind := lambdaO_indep hσ hX z T g (by rintro (μ | ν) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : Fin N ⊕ Fin N) =>
      Sum.elim (fun μ ω => X ω i μ) (fun ν ω => X ω j ν) s ω) (lambdaO_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun μ ω => X ω i μ) (fun ν ω => X ω j ν) (lambdaO_Y σ X z T)
    (fun b μ ν => b (Sum.inr μ, Sum.inr ν)) (hfam ▸ lambdaO_rowAssumption hX g hginj)
    (lambdaO_measurable_Y hX z T) (fun μ ν => measurable_pi_apply _) hind'
  refine lambdaO_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom lambdaO_dom_zero ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  refine lambdaO_xi_finish (by omega) (mul_pos (hσ i) (hσ j)).le (by positivity) hK
    (fun hΞ => ⟨?_, ?_, lambdaO_zero_le _ _⟩) h1 h2
  · refine (lambdaO_det_ij hc h hσ hz hx hlog hΞ hij).trans (le_of_eq ?_)
    simp only [sigS, Sum.elim_inl, add_zero]
    rfl
  · exact lambdaO_coef_ij hc h hσ hz hx hlog hΞ hω hij

private theorem lambdaO_case_munu (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lambdaO_BilAt C N (ε / 2) (D + 2) Ω) {μ ν : Fin N} (hμν : μ ≠ ν) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inr ν)‖)
      (fun ω => sigS (M := M) σ (Sum.inr μ) * sigS (M := M) σ (Sum.inr ν)
        * √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
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
  have hind := lambdaO_indep hσ hX z T g (by rintro (i | j) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : Fin M ⊕ Fin M) =>
      Sum.elim (fun i ω => X ω i μ) (fun j ω => X ω j ν) s ω) (lambdaO_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun i ω => X ω i μ) (fun j ω => X ω j ν) (lambdaO_Y σ X z T)
    (fun b i j => b (Sum.inl i, Sum.inl j)) (hfam ▸ lambdaO_rowAssumption hX g hginj)
    (lambdaO_measurable_Y hX z T) (fun i j => measurable_pi_apply _) hind'
  refine lambdaO_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom lambdaO_dom_zero ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  refine lambdaO_xi_finish (by omega) (by simp [sigS]) (by positivity) hK
    (fun hΞ => ⟨?_, ?_, lambdaO_zero_le _ _⟩) h1 h2
  · refine (lambdaO_det_munu hc h hσ hz hx hlog hΞ hμν).trans (le_of_eq ?_)
    simp only [sigS, Sum.elim_inr, add_zero]
    rfl
  · exact lambdaO_coef_munu hc h hσ hz hx hlog hΞ hω hμν

private theorem lambdaO_case_imu (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lambdaO_BilAt C N (ε / 2) (D + 2) Ω) (hlin : lambdaO_LinAt C N (ε / 2) (D + 2) Ω)
    (i : Fin M) (μ : Fin N) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inr μ)‖)
      (fun ω => sigS (N := N) σ (Sum.inl i) * sigS (M := M) σ (Sum.inr μ)
        * √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
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
  have hind := lambdaO_indep hσ hX z T g (by rintro (ν | j) <;> simp [g, hT])
  have hind' : IndepFun (fun ω (s : {ν : Fin N // ν ≠ μ} ⊕ {j : Fin M // j ≠ i}) =>
      Sum.elim (fun (ν : {ν : Fin N // ν ≠ μ}) ω => X ω i ν.1)
        (fun (j : {j : Fin M // j ≠ i}) ω => X ω j.1 μ) s ω) (lambdaO_Y σ X z T) ℙ := by
    rw [hfam]
    exact hind
  have hdom := hbil (fun (ν : {ν : Fin N // ν ≠ μ}) ω => X ω i ν.1)
    (fun (j : {j : Fin M // j ≠ i}) ω => X ω j.1 μ) (lambdaO_Y σ X z T)
    (fun b ν j => b (Sum.inr ν.1, Sum.inl j.1)) (hfam ▸ lambdaO_rowAssumption hX g hginj)
    (lambdaO_measurable_Y hX z T) (fun ν j => measurable_pi_apply _) hind'
  let g₂ : Unit → Fin M × Fin N := fun _ => (i, μ)
  have hdom₂ := hlin (fun (_ : Unit) ω => X ω i μ) (lambdaO_Y σ X z T) (fun _ _ => (1 : ℂ))
    (lambdaO_rowAssumption hX g₂ fun a b _ => Subsingleton.elim a b)
    (lambdaO_measurable_Y hX z T) (fun _ => measurable_const)
    (lambdaO_indep hσ hX z T g₂ fun _ => Or.inl (by simp [hT, g₂]))
  refine lambdaO_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  refine lambdaO_xi_finish (by omega) (by simpa [sigS] using (hσ i).le) (by positivity) hK
    (fun hΞ => ⟨?_, ?_, ?_⟩) h1 h2
  · refine (lambdaO_det_imu hc h hσ hz hx hlog hΞ i μ).trans (le_of_eq ?_)
    simp only [sigS, Sum.elim_inl, Sum.elim_inr]
    rfl
  · exact lambdaO_coef_imu hc h hσ hz hx hlog hΞ hω i μ
  · exact lambdaO_coef_lin hc h hz hω

private theorem lambdaO_case_mui (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hbil : lambdaO_BilAt C N (ε / 2) (D + 2) Ω) (hlin : lambdaO_LinAt C N (ε / 2) (D + 2) Ω)
    (μ : Fin N) (i : Fin M) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inl i)‖)
      (fun ω => sigS (M := M) σ (Sum.inr μ) * sigS (N := N) σ (Sum.inl i)
        * √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
  have hσ := hD.pos
  have key := lambdaO_case_imu hc hτ hD hz hx hN hlog hK hE hbil hlin i μ
  have e : ∀ ω, G (diagonal σ) (X ω) z (Sum.inr μ) (Sum.inl i)
      = G (diagonal σ) (X ω) z (Sum.inl i) (Sum.inr μ) := fun ω => by
    have := congrFun (congrFun (G_transpose (posDef_diagonal_iff.2 hσ) (X ω) hz.1) (Sum.inl i))
      (Sum.inr μ)
    rwa [transpose_apply] at this
  unfold DomAt at key ⊢
  simp only [e, mul_comm (sigS (M := M) σ (Sum.inr μ))]
  exact key

private theorem lambdaO_case_Zi (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hoff : lambdaO_OffAt C N (ε / 2) (D + 2) Ω) (hdiag : lambdaO_DiagAt C N (ε / 2) (D + 2) Ω)
    (i : Fin M) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖ZS σ (X ω) z (Sum.inl i)‖)
      (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inl i} with hT
  have hind := lambdaO_indep hσ hX z T (fun μ => (i, μ)) (fun _ => Or.inl (by simp [hT]))
  have hdom₁ := hoff (fun μ ω => X ω i μ) (lambdaO_Y σ X z T)
    (fun b μ ν => b (Sum.inr μ, Sum.inr ν)) (hX.row i) (lambdaO_measurable_Y hX z T)
    (fun μ ν => measurable_pi_apply _) hind
  have hdom₂ := hdiag (fun μ ω => X ω i μ) (lambdaO_Y σ X z T)
    (fun b μ => b (Sum.inr μ, Sum.inr μ)) (hX.row i) (lambdaO_measurable_Y hX z T)
    (fun μ => measurable_pi_apply _) hind
  refine lambdaO_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom₁ hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hCG := lambdaO_CG_ge (τ := τ) hc
  refine le_of_le_of_eq (lambdaO_xi_finish (σ := σ) (Xm := X ω) (z := z)
    (g := ‖ZS σ (X ω) z (Sum.inl i)‖) (by omega) zero_le_one (by positivity) hK
    (fun hΞ => ⟨?_, ?_, ?_⟩) h1 h2) (by rw [one_mul]; rfl)
  · refine (lambdaO_det_Zi i).trans ?_
    rw [one_mul, one_mul]
    have h0 : 0 ≤ ‖∑ μ, ∑ ν ∈ Finset.univ.erase μ, (X ω i μ : ℂ)
          * Gm (diagonal σ) (X ω) z {Sum.inl i} (Sum.inr μ) (Sum.inr ν) * (X ω i ν : ℂ)‖
        + ‖∑ μ, Gm (diagonal σ) (X ω) z {Sum.inl i} (Sum.inr μ) (Sum.inr μ)
          * ((X ω i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ := by positivity
    have : 1 ≤ (mAsympUpper c τ + 1) ^ 2 := one_le_pow₀ hCG
    exact le_mul_of_one_le_left h0 this
  · exact lambdaO_coef_Zi_off hc h hσ hz hx hlog hΞ hω i
  · exact lambdaO_coef_Zi_diag hc h hσ hz hx hlog hΞ hω i

private theorem lambdaO_case_Zmu (hc : 0 < c) (hτ : 0 < τ) (hD : DiagModel τ C M N σ X)
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 2 ≤ N)
    (hlog : (Real.log N)⁻¹ ≤ xiThr c τ)
    (hK : 2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀) ≤ (N : ℝ) ^ (ε / 2))
    (hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hoff : lambdaO_OffAt C N (ε / 2) (D + 2) Ω) (hdiag : lambdaO_DiagAt C N (ε / 2) (D + 2) Ω)
    (μ : Fin N) :
    DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖ZS σ (X ω) z (Sum.inr μ)‖)
      (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
  have h := hD.densityAssumptions hτ
  have hσ := hD.pos
  have hX := hD.entries
  set T : Finset (Fin M ⊕ Fin N) := {Sum.inr μ} with hT
  have hind := lambdaO_indep hσ hX z T (fun i => (i, μ)) (fun _ => Or.inr (by simp [hT]))
  have hdom₁ := hoff (fun i ω => X ω i μ) (lambdaO_Y σ X z T)
    (fun b i j => b (Sum.inl i, Sum.inl j)) (hX.col μ) (lambdaO_measurable_Y hX z T)
    (fun i j => measurable_pi_apply _) hind
  have hdom₂ := hdiag (fun i ω => X ω i μ) (lambdaO_Y σ X z T)
    (fun b i => b (Sum.inl i, Sum.inl i)) (hX.col μ) (lambdaO_measurable_Y hX z T)
    (fun i => measurable_pi_apply _) hind
  refine lambdaO_dom hN {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} hE hdom₁ hdom₂ ?_
  intro ω hω h1 h2
  beta_reduce at h1 h2
  have hCG := lambdaO_CG_ge (τ := τ) hc
  refine le_of_le_of_eq (lambdaO_xi_finish (σ := σ) (Xm := X ω) (z := z)
    (g := ‖ZS σ (X ω) z (Sum.inr μ)‖) (by omega) zero_le_one (by positivity) hK
    (fun hΞ => ⟨?_, ?_, ?_⟩) h1 h2) (by rw [one_mul]; rfl)
  · refine (lambdaO_det_Zmu μ).trans ?_
    rw [one_mul, one_mul]
    have h0 : 0 ≤ ‖∑ i, ∑ j ∈ Finset.univ.erase i, (X ω i μ : ℂ)
          * Gm (diagonal σ) (X ω) z {Sum.inr μ} (Sum.inl i) (Sum.inl j) * (X ω j μ : ℂ)‖
        + ‖∑ i, Gm (diagonal σ) (X ω) z {Sum.inr μ} (Sum.inl i) (Sum.inl i)
          * ((X ω i μ : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ := by positivity
    have : 1 ≤ (mAsympUpper c τ + 1) ^ 2 := one_le_pow₀ hCG
    exact le_mul_of_one_le_left h0 this
  · exact lambdaO_coef_Zmu_off hc h hσ hz hx hlog hΞ hω μ
  · exact lambdaO_coef_Zmu_diag hc h hσ hz hx hlog hΞ hω μ

end Prob

/-! ## Thresholds -/

/-- For `0 < τ ≤ 1`, `c > 0`, `ε > 0` and every `K`: eventually `N ≥ 2`, `(log N)⁻¹ ≤ xiThr c τ`
and `K ≤ N^{ε/2}`. -/
private theorem lambdaO_threshold {τ c ε : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c)
    (hε : 0 < ε) (K : ℝ) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 2 ≤ N ∧ (Real.log N)⁻¹ ≤ xiThr c τ ∧ K ≤ (N : ℝ) ^ (ε / 2) := by
  have hxi : 0 < xiThr c τ := by
    obtain ⟨hca, -⟩ := lambdaO_cas hτ hτ1
    have hC := lambdaO_mBoundConst_pos hτ
    have hT : 0 < ThetaConst τ := by unfold ThetaConst; positivity
    unfold xiThr
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have t1 : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  have ev := (eventually_ge_atTop 2).and
    (((tendsto_order.1 t1).2 _ hxi).and (t2.eventually_ge_atTop K))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ev
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1, (hN₁ N hN).2.1.le, (hN₁ N hN).2.2⟩⟩

/-- Both steps of Lemma 5.2 at once. -/
private theorem lambdaO_core (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      (∀ s t : Fin M ⊕ Fin N, s ≠ t →
        DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z s t‖)
          (fun ω => sigS σ s * sigS σ t *
            √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z))) ∧
      (∀ s : Fin M ⊕ Fin N,
        DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖ZS σ (X ω) z s‖)
          (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)))
      := by
  obtain ⟨N₁, h₁⟩ := lde_bilinear_cond C (half_pos hε) (D + 2)
  obtain ⟨N₂, h₂⟩ := lde_offdiag_cond C (half_pos hε) (D + 2)
  obtain ⟨N₃, h₃⟩ := lde_diag_cond C (half_pos hε) (D + 2)
  obtain ⟨N₄, h₄⟩ := lde_linear_cond C (half_pos hε) (D + 2)
  by_cases hτ1 : τ ≤ 1
  swap
  · refine ⟨0, fun N _ Ω _ _ M σ X hD => ?_⟩
    exfalso
    have h1 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (not_le.1 hτ1)
    linarith [hD.ratio_ge.trans hD.ratio_le]
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₅, h₅⟩ := hC₀ C (D + 2)
  set C₀' := max C₀ 0 with hC₀'
  obtain ⟨N₆, h₆⟩ := lambdaO_threshold hτ hτ1 hc hε
    (2 * (mAsympUpper c τ + 1) ^ 2 * √(lambdaO_k τ c C₀'))
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ N₆),
    fun N hN Ω _ _ M σ X hD z hz hx => ?_⟩
  have hN₁ : N ≥ N₁ := le_trans (by omega) hN
  have hN₂ : N ≥ N₂ := le_trans (by omega) hN
  have hN₃ : N ≥ N₃ := le_trans (by omega) hN
  have hN₄ : N ≥ N₄ := le_trans (by omega) hN
  have hN₅ : N ≥ N₅ := le_trans (by omega) hN
  have hN₆ : N ≥ N₆ := le_trans (by omega) hN
  obtain ⟨hN2, hlog, hK⟩ := h₆ N hN₆
  have hM := lambdaO_M_le (hD.densityAssumptions hτ)
  have hE : ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀'}ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    refine le_trans (measure_mono ?_) (h₅ N hN₅ M X hD.entries hM)
    exact Set.compl_subset_compl.2 fun ω hω => (show ‖(X ω)ᵀ * X ω‖ ≤ C₀' from
      le_max_of_le_left hω)
  have hbil : lambdaO_BilAt C N (ε / 2) (D + 2) Ω := fun x x' Y B => h₁ N hN₁ x x' Y B
  have hoff : lambdaO_OffAt C N (ε / 2) (D + 2) Ω := fun x Y A => h₂ N hN₂ x Y A
  have hdiag : lambdaO_DiagAt C N (ε / 2) (D + 2) Ω := fun x Y a => h₃ N hN₃ x Y a
  have hlin : lambdaO_LinAt C N (ε / 2) (D + 2) Ω := fun x Y a => h₄ N hN₄ x Y a
  refine ⟨?_, ?_⟩
  · rintro (i | μ) (j | ν) hst
    · exact lambdaO_case_ij hc hτ hD hz hx hN2 hlog hK hE hbil (fun e => hst (by rw [e]))
    · exact lambdaO_case_imu hc hτ hD hz hx hN2 hlog hK hE hbil hlin i ν
    · exact lambdaO_case_mui hc hτ hD hz hx hN2 hlog hK hE hbil hlin μ j
    · exact lambdaO_case_munu hc hτ hD hz hx hN2 hlog hK hE hbil (fun e => hst (by rw [e]))
  · rintro (i | μ)
    · exact lambdaO_case_Zi hc hτ hD hz hx hN2 hlog hK hE hoff hdiag i
    · exact lambdaO_case_Zmu hc hτ hD hz hx hN2 hlog hK hE hoff hdiag μ

/-! # Lemma 5.2 (`lem:Lambda_o_Z`): the entrywise steps -/

/-- (Gst_step1). -/
theorem Gst_step1 (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ s t : Fin M ⊕ Fin N, s ≠ t →
      DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z s t‖)
        (fun ω => sigS σ s * sigS σ t *
          √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) := by
  obtain ⟨N₀, h⟩ := lambdaO_core τ c C ε D hτ hc hε
  exact ⟨N₀, fun N hN Ω _ _ M σ X hD z hz hx => (h N hN M σ X hD z hz hx).1⟩

/-- The `Z_s` part of (Lambda_o_Z_bound), before the absorption of `Λ_o`. -/
theorem Z_step1 (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ s : Fin M ⊕ Fin N,
      DomAt N ε D (fun ω => xiInd σ (X ω) z * ‖ZS σ (X ω) z s‖)
        (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z))
      := by
  obtain ⟨N₀, h⟩ := lambdaO_core τ c C ε D hτ hc hε
  exact ⟨N₀, fun N hN Ω _ _ M σ X hD z hz hx => (h N hN M σ X hD z hz hx).2⟩

/-! ## Checks: the Rademacher model `M = N`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` for every `N ≥ 1` -/

section Checks

/-- `Gst_step1` at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ s t : Fin M ⊕ Fin N, s ≠ t →
    DomAt N 1 1 (fun ω => xiInd σ (X ω) z * ‖G (diagonal σ) (X ω) z s t‖)
      (fun ω => sigS σ s * sigS σ t *
        √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) :=
  Gst_step1 (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

/-- `Z_step1` at `τ = 1/2`, `c = 1`, `C_p = 2`, `ε = D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (σ : Fin M → ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, (1 : ℝ) ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ s : Fin M ⊕ Fin N,
    DomAt N 1 1 (fun ω => xiInd σ (X ω) z * ‖ZS σ (X ω) z s‖)
      (fun ω => √(((mFun N σ z).im + Theta σ (X ω) z + LambdaO σ (X ω) z ^ 2) * PhiN N z)) :=
  Z_step1 (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) one_pos one_pos

end Checks

end Anisotropic

#print axioms Anisotropic.Gst_step1
#print axioms Anisotropic.Z_step1
