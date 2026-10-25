import Anisotropic.Entrywise.FA.MinorExpand
import Anisotropic.Probability.LDE.Basic
import Anisotropic.LinAlg.OpBound

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Deterministic bounds on the good event: `|Z^{(S)}_s|`, minors with `|S| ≤ 2p`, the Möbius pieces, and the LDE control parameters -/

/-! ## Consequences of the density assumptions and of `z ∈ 𝐃(τ,N)` -/

/-- `0 < N` under the density assumptions. -/
private theorem bounds_N_pos {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · exfalso
    have := h.phi_lower
    simp [phiRatio, h0] at this
    linarith [h.pos]
  · exact h0

/-- `τ ≤ 1` under the density assumptions, since `τ ≤ M/N ≤ τ⁻¹`. -/
private theorem bounds_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  rw [not_le] at hc
  linarith [inv_lt_one_of_one_lt₀ hc]

/-- `1 ≤ τ⁻¹`. -/
private theorem bounds_one_le_inv {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : 1 ≤ τ⁻¹ :=
  (one_le_inv₀ h.pos).2 (bounds_tau_le_one h)

/-- `M ≤ τ⁻¹ N`. -/
private theorem bounds_M_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    (M : ℝ) ≤ τ⁻¹ * N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast bounds_N_pos h
  have := h.phi_upper
  rw [phiRatio, div_le_iff₀ hN] at this
  exact this

/-- `0 < σ̲_s`. -/
private theorem bounds_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `σ̲_s ≤ τ⁻¹`. -/
private theorem bounds_sigS_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (s : Fin M ⊕ Fin N) : sigS σ s ≤ τ⁻¹ := by
  cases s with
  | inl i => exact h.bound_Sigma i
  | inr μ => exact bounds_one_le_inv h

/-- `0 < c_as ≤ 1`. -/
private theorem bounds_cas {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < mAsympLower τ ∧ mAsympLower τ ≤ 1 := by
  have hτ := h.pos
  have hC : 0 < mBoundConst τ := by
    unfold mBoundConst genPropConst
    exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)
  have hD : 1 ≤ 1 + mBoundConst τ * τ⁻¹ := by
    have := mul_pos hC (inv_pos.2 hτ)
    linarith
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ hD⟩

/-- `1 ≤ C_as + 1`. -/
private theorem bounds_Cas {c τ : ℝ} (hc : 0 < c) : 1 ≤ mAsympUpper c τ + 1 := by
  have : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  linarith

/-- On `𝐃(τ,N)`: `|z| ≤ √2 τ⁻¹` and `η⁻¹ ≤ N`. -/
private theorem bounds_z {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {z : ℂ}
    (hz : z ∈ specDomain τ N) : ‖z‖ ≤ √2 * τ⁻¹ ∧ (z.im)⁻¹ ≤ N := by
  obtain ⟨h0, -, hre, hlow, him⟩ := hz
  have hτ := h.pos
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast bounds_N_pos h
  refine ⟨?_, ?_⟩
  · have hsq : ‖z‖ ^ 2 ≤ (√2 * τ⁻¹) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      have h1 : z.re * z.re ≤ τ⁻¹ ^ 2 := by
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hre 2
      have h2 : z.im * z.im ≤ τ⁻¹ ^ 2 := by
        rw [← sq]
        exact pow_le_pow_left₀ h0.le him 2
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  · have h1 : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have hNpos : (0 : ℝ) < N := by linarith
    calc (z.im)⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) (h1.trans hlow)
      _ = N := inv_inv _

/-! ## The bilinear form of a minor -/

/-- The inclusion `𝓘 ∖ S → 𝓘` of the remaining indices. -/
private def bndEmb {N : ℕ} (S : Finset (Fin M ⊕ Fin N)) : idxM S ⊕ idxN S → Fin M ⊕ Fin N :=
  Sum.elim (fun i => Sum.inl i.1) (fun μ => Sum.inr μ.1)

private theorem bndEmb_notMem {N : ℕ} (S : Finset (Fin M ⊕ Fin N)) (s : idxM S ⊕ idxN S) :
    bndEmb S s ∉ S := by
  cases s with
  | inl i => exact i.2
  | inr μ => exact μ.2

private theorem toSub_bndEmb {N : ℕ} (S : Finset (Fin M ⊕ Fin N)) (s : idxM S ⊕ idxN S)
    (hs : bndEmb S s ∉ S) : toSub S (bndEmb S s) hs = s := by
  cases s <;> rfl

/-- A sum over `𝓘` of a function vanishing on `S` is a sum over `𝓘 ∖ S`. -/
private theorem bounds_sum_restrict {N : ℕ} (S : Finset (Fin M ⊕ Fin N))
    (f : Fin M ⊕ Fin N → ℂ) (hf : ∀ s ∈ S, f s = 0) :
    ∑ s, f s = ∑ s' : idxM S ⊕ idxN S, f (bndEmb S s') := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin M => Sum.inl i ∈ S)
      (fun i => f (Sum.inl i))]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun i _ => hf _ i.2), zero_add]
    rfl
  · rw [← Fintype.sum_subtype_add_sum_subtype (fun μ : Fin N => Sum.inr μ ∈ S)
      (fun μ => f (Sum.inr μ))]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun i _ => hf _ i.2), zero_add]
    rfl

/-- The real version of `bounds_sum_restrict` for nonnegative summands: the sum over `𝓘 ∖ S` is
at most the sum over `𝓘`. -/
private theorem bounds_sum_restrict_le {N : ℕ} (S : Finset (Fin M ⊕ Fin N))
    (f : Fin M ⊕ Fin N → ℝ) (hf : ∀ s, 0 ≤ f s) :
    ∑ s' : idxM S ⊕ idxN S, f (bndEmb S s') ≤ ∑ s, f s := by
  have h := bounds_sum_restrict S (fun s => ((if s ∈ S then 0 else f s : ℝ) : ℂ))
    (fun s hs => by simp [hs])
  have h' : ∑ s, (if s ∈ S then 0 else f s) = ∑ s' : idxM S ⊕ idxN S, f (bndEmb S s') := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re] at this
    rw [this]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp [bndEmb_notMem S s']
  rw [← h']
  exact Finset.sum_le_sum fun s _ => by split_ifs <;> simp [hf s]

/-- (opbound) for the minor `G^{(S)}`, extended by zero: for real `a, b` on `𝓘`,
`|Σ_{st} a_s G^{(S)}_{st} b_t| ≤ (1+5|z|)η⁻¹ (Σ_s σ̲_s a_s²)^{1/2} (Σ_t σ̲_t b_t²)^{1/2}`. -/
private theorem bounds_opbound_minor {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (S : Finset (Fin M ⊕ Fin N))
    (a b : Fin M ⊕ Fin N → ℝ) :
    ‖∑ s, ∑ t, (a s : ℂ) * Gm (diagonal σ) Xm z S s t * (b t : ℂ)‖
      ≤ (1 + 5 * ‖z‖) / z.im * Real.sqrt (∑ s, sigS σ s * a s ^ 2)
        * Real.sqrt (∑ t, sigS σ t * b t ^ 2) := by
  set Sig' := (diagonal σ).submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxM S → Fin M)
  set X' := Xm.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)
  have hSig' : Sig'.PosDef := by
    simp only [Sig']
    rw [submatrix_diagonal _ _ Subtype.val_injective]
    exact posDef_diagonal_iff.2 fun i => hσ _
  have key := opbound hSig' X' hz (a ∘ bndEmb S) (b ∘ bndEmb S)
  have hG : ∀ s' t' : idxM S ⊕ idxN S,
      Gm (diagonal σ) Xm z S (bndEmb S s') (bndEmb S t') = G Sig' X' z s' t' := by
    intro s' t'
    rw [Gm_eq_extend_G_of_diagonal σ (fun i => (hσ i).ne') Xm z S]
    simp only [extend, bndEmb_notMem, dite_false, toSub_bndEmb]
    rfl
  have hent : ∑ s, ∑ t, (a s : ℂ) * Gm (diagonal σ) Xm z S s t * (b t : ℂ)
      = ent (G Sig' X' z) (a ∘ bndEmb S) (b ∘ bndEmb S) := by
    rw [bounds_sum_restrict S]
    · unfold ent
      simp only [dotProduct, mulVec, cvec, Function.comp_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [bounds_sum_restrict S]
      · refine Finset.sum_congr rfl fun t' _ => ?_
        rw [hG]
        ring
      · intro t ht
        simp [Gm, ht]
    · intro s hs
      simp [Gm, hs]
  have hq : ∀ c : Fin M ⊕ Fin N → ℝ,
      (c ∘ bndEmb S) ⬝ᵥ SigU (n := idxN S) Sig' *ᵥ (c ∘ bndEmb S) ≤ ∑ s, sigS σ s * c s ^ 2 := by
    intro c
    have e : (c ∘ bndEmb S) ⬝ᵥ SigU (n := idxN S) Sig' *ᵥ (c ∘ bndEmb S)
        = ∑ s' : idxM S ⊕ idxN S, sigS σ (bndEmb S s') * c (bndEmb S s') ^ 2 := by
      simp only [SigU, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, zero_mulVec, add_zero, zero_add, one_mulVec, Sig',
        submatrix_diagonal _ _ Subtype.val_injective, mulVec_diagonal, Function.comp_apply,
        bndEmb, sigS]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        ring
    rw [e]
    exact bounds_sum_restrict_le S (fun s => sigS σ s * c s ^ 2)
      fun s => mul_nonneg (bounds_sigS_pos hσ s).le (sq_nonneg _)
  rw [hent]
  refine key.trans ?_
  have hC : 0 ≤ (1 + 5 * ‖z‖) / z.im := by positivity
  gcongr
  · exact hq a
  · exact hq b

/-- `|G^{(S)}_{ss}| ≤ (1+5|z|)η⁻¹ σ̲_s`. -/
private theorem bounds_diag_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (S : Finset (Fin M ⊕ Fin N))
    (s : Fin M ⊕ Fin N) :
    ‖Gm (diagonal σ) Xm z S s s‖ ≤ (1 + 5 * ‖z‖) / z.im * sigS σ s := by
  set e : Fin M ⊕ Fin N → ℝ := Pi.single s 1 with he
  have h := bounds_opbound_minor hσ Xm hz S e e
  have e1 : ∑ s', ∑ t', ((e s' : ℝ) : ℂ) * Gm (diagonal σ) Xm z S s' t'
      * ((e t' : ℝ) : ℂ) = Gm (diagonal σ) Xm z S s s := by
    rw [Finset.sum_eq_single s (fun b _ hb => ?_) (by simp),
      Finset.sum_eq_single s (fun b _ hb => ?_) (by simp)]
    · simp [he]
    · simp [he, hb]
    · simp [he, hb]
  have e2 : ∑ t, sigS σ t * (e t) ^ 2 = sigS σ s := by
    rw [he]
    simp [Pi.single_apply]
  rw [e1, e2, mul_assoc, Real.mul_self_sqrt (bounds_sigS_pos hσ s).le] at h
  exact h

/-- `(X̂ᵀ B X̂)_{μμ} = Σ_{st} x_s B_{st} x_t` with `x = (X_{·μ}, 0)`. -/
private theorem bounds_quad_inr {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N)
    (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) :
    ((Xhat Xm)ᵀ * B * Xhat Xm) (Sum.inr μ) (Sum.inr μ)
      = ∑ s, ∑ t, ((Sum.elim (fun i => Xm i μ) 0 s : ℝ) : ℂ) * B s t
        * ((Sum.elim (fun i => Xm i μ) 0 t : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  cases s <;> cases t <;> simp [Xhat, cplx]

/-- `(X̂ B X̂ᵀ)_{ii} = Σ_{st} y_s B_{st} y_t` with `y = (0, X_{i·})`. -/
private theorem bounds_quad_inl {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) (i : Fin M)
    (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) :
    (Xhat Xm * B * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl i)
      = ∑ s, ∑ t, ((Sum.elim 0 (fun ν => Xm i ν) s : ℝ) : ℂ) * B s t
        * ((Sum.elim 0 (fun ν => Xm i ν) t : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  cases s <;> cases t <;> simp [Xhat, cplx]

/-! ## The pathwise bound on `Z^{(S)}_s` ((opbound), Lemma 4.9) -/

/-- `K_det = (1 + 5√2 τ⁻¹)(τ⁻¹ + τ⁻²)`. -/
def detZConst (τ : ℝ) : ℝ := (1 + 5 * √2 * τ⁻¹) * (τ⁻¹ + τ⁻¹ ^ 2)

/-- `(1 + 5|z|)η⁻¹ ≤ (1 + 5√2 τ⁻¹) N` on `𝐃(τ,N)`. -/
private theorem bounds_opconst {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {z : ℂ} (hz : z ∈ specDomain τ N) :
    (1 + 5 * ‖z‖) / z.im ≤ (1 + 5 * √2 * τ⁻¹) * N := by
  obtain ⟨hz1, hz2⟩ := bounds_z h hz
  rw [div_eq_mul_inv]
  have : 1 + 5 * ‖z‖ ≤ 1 + 5 * √2 * τ⁻¹ := by nlinarith
  have hτ := h.pos
  exact mul_le_mul this hz2 (inv_pos.2 hz.1).le (by positivity)

/-- The pathwise bound `|Z^{(S)}_μ| ≤ K_det N (1 + |x_μ|²)` on `𝐃(τ,N)`, `x_μ` the column `μ`. -/
theorem ZmuS_det_bound {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N)
    (S : Finset (Fin N)) (μ : Fin N) :
    ‖ZmuS σ Xm z S μ‖ ≤ detZConst τ * N * (1 + ∑ i, Xm i μ ^ 2) := by
  set R : Finset (Fin M ⊕ Fin N) := colSet (insert μ S)
  set C := (1 + 5 * ‖z‖) / z.im
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  have hN : (0 : ℝ) < N := by exact_mod_cast bounds_N_pos h
  have hC0 : 0 ≤ C := div_nonneg (by positivity) hz.1.le
  have hC := bounds_opconst h hz
  have hX0 : 0 ≤ ∑ i, Xm i μ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the quadratic part
  have hq : ‖((Xhat Xm)ᵀ * Gm (diagonal σ) Xm z R * Xhat Xm) (Sum.inr μ) (Sum.inr μ)‖
      ≤ C * (τ⁻¹ * ∑ i, Xm i μ ^ 2) := by
    rw [bounds_quad_inr]
    refine (bounds_opbound_minor hσ Xm hz.1 R _ _).trans ?_
    have e : ∑ s : Fin M ⊕ Fin N, sigS σ s * (Sum.elim (fun i => Xm i μ) 0 s : ℝ) ^ 2
        = ∑ i, σ i * Xm i μ ^ 2 := by
      simp [Fintype.sum_sum_type, sigS]
    have hle : ∑ i, σ i * Xm i μ ^ 2 ≤ τ⁻¹ * ∑ i, Xm i μ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (h.bound_Sigma i) (sq_nonneg _)
    rw [e, mul_assoc, Real.mul_self_sqrt (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hσ i).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hle hC0
  -- the trace part
  have htr : ‖(N : ℂ)⁻¹ * ∑ i, Gm (diagonal σ) Xm z R (Sum.inl i) (Sum.inl i)‖
      ≤ C * τ⁻¹ ^ 2 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ i, Gm (diagonal σ) Xm z R (Sum.inl i) (Sum.inl i)‖ ≤ ∑ _i : Fin M, C * τ⁻¹ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (bounds_diag_le hσ Xm hz.1 R _).trans
          (mul_le_mul_of_nonneg_left (bounds_sigS_le h _) hC0))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hM := bounds_M_le h
    calc (N : ℝ)⁻¹ * ‖∑ i, Gm (diagonal σ) Xm z R (Sum.inl i) (Sum.inl i)‖
        ≤ (N : ℝ)⁻¹ * (M * (C * τ⁻¹)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (N : ℝ)⁻¹ * (τ⁻¹ * N * (C * τ⁻¹)) := by gcongr
      _ = C * τ⁻¹ ^ 2 := by field_simp
  unfold ZmuS
  refine (norm_sub_le _ _).trans ((add_le_add hq htr).trans ?_)
  have hK : C ≤ (1 + 5 * √2 * τ⁻¹) * N := hC
  calc C * (τ⁻¹ * ∑ i, Xm i μ ^ 2) + C * τ⁻¹ ^ 2
      ≤ C * ((τ⁻¹ + τ⁻¹ ^ 2) * (1 + ∑ i, Xm i μ ^ 2)) := by
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        nlinarith
    _ ≤ (1 + 5 * √2 * τ⁻¹) * N * ((τ⁻¹ + τ⁻¹ ^ 2) * (1 + ∑ i, Xm i μ ^ 2)) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = detZConst τ * N * (1 + ∑ i, Xm i μ ^ 2) := by unfold detZConst; ring

/-- The pathwise bound `|Z^{(S)}_i| ≤ K_det N (1 + |x_i|²)` on `𝐃(τ,N)`, `x_i` the row `i`. -/
theorem ZiS_det_bound {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : z ∈ specDomain τ N)
    (S : Finset (Fin M)) (i : Fin M) :
    ‖ZiS σ Xm z S i‖ ≤ detZConst τ * N * (1 + ∑ ν, Xm i ν ^ 2) := by
  set R : Finset (Fin M ⊕ Fin N) := rowSet (insert i S)
  set C := (1 + 5 * ‖z‖) / z.im
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  have hN : (0 : ℝ) < N := by exact_mod_cast bounds_N_pos h
  have hC0 : 0 ≤ C := div_nonneg (by positivity) hz.1.le
  have hC := bounds_opconst h hz
  have hX0 : 0 ≤ ∑ ν, Xm i ν ^ 2 := Finset.sum_nonneg fun ν _ => sq_nonneg _
  have hq : ‖(Xhat Xm * Gm (diagonal σ) Xm z R * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl i)‖
      ≤ C * ∑ ν, Xm i ν ^ 2 := by
    rw [bounds_quad_inl]
    refine (bounds_opbound_minor hσ Xm hz.1 R _ _).trans ?_
    have e : ∑ s : Fin M ⊕ Fin N, sigS σ s * (Sum.elim 0 (fun ν => Xm i ν) s : ℝ) ^ 2
        = ∑ ν, Xm i ν ^ 2 := by
      simp [Fintype.sum_sum_type, sigS]
    rw [e, mul_assoc, Real.mul_self_sqrt hX0]
  have htr : ‖(N : ℂ)⁻¹ * ∑ ν, Gm (diagonal σ) Xm z R (Sum.inr ν) (Sum.inr ν)‖ ≤ C := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ ν, Gm (diagonal σ) Xm z R (Sum.inr ν) (Sum.inr ν)‖ ≤ ∑ _ν : Fin N, C := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
      have := bounds_diag_le hσ Xm hz.1 R (Sum.inr ν)
      simpa [sigS] using this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc (N : ℝ)⁻¹ * ‖∑ ν, Gm (diagonal σ) Xm z R (Sum.inr ν) (Sum.inr ν)‖
        ≤ (N : ℝ)⁻¹ * (N * C) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C := by field_simp
  unfold ZiS
  refine (norm_sub_le _ _).trans ((add_le_add hq htr).trans ?_)
  calc C * ∑ ν, Xm i ν ^ 2 + C
      ≤ C * ((τ⁻¹ + τ⁻¹ ^ 2) * (1 + ∑ ν, Xm i ν ^ 2)) := by
        rw [← mul_add_one]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        nlinarith
    _ ≤ (1 + 5 * √2 * τ⁻¹) * N * ((τ⁻¹ + τ⁻¹ ^ 2) * (1 + ∑ ν, Xm i ν ^ 2)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = detZConst τ * N * (1 + ∑ ν, Xm i ν ^ 2) := by unfold detZConst; ring

/-! ## Minors with `|S| ≤ 2p`: (Gtt_bound) in the proof of Lemma 5.6 -/

/-- `|G_{st} − δ_{st} m_s| ≤ σ̲_s σ̲_t Λ`. -/
private theorem bounds_entry_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (s t : Fin M ⊕ Fin N) :
    ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      ≤ sigS σ s * sigS σ t * Lambda σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (bounds_sigS_pos hσ s) (bounds_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      / (sigS σ s * sigS σ t) ≤ Lambda σ Xm z := by
    unfold Lambda
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove s)
    exact le_ciSup (f := fun t => ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      / (sigS σ s * sigS σ t)) (Set.finite_range _).bddAbove t
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `Λ ≥ 0`. -/
private theorem bounds_lambda_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ Lambda σ Xm z :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun t =>
    div_nonneg (norm_nonneg _) (mul_pos (bounds_sigS_pos hσ s) (bounds_sigS_pos hσ t)).le

/-- `|G_{st}| ≤ σ̲_s σ̲_t Λ_o` for `s ≠ t`. -/
private theorem bounds_offO_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖G (diagonal σ) Xm z s t‖ ≤ sigS σ s * sigS σ t * LambdaO σ Xm z := by
  have hpos : 0 < sigS (N := N) σ s * sigS σ t :=
    mul_pos (bounds_sigS_pos hσ s) (bounds_sigS_pos hσ t)
  have h1 : ‖G (diagonal σ) Xm z s t‖ / (sigS σ s * sigS σ t) ≤ LambdaO σ Xm z := by
    unfold LambdaO
    exact le_ciSup (f := fun q : {q : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // q.1 ≠ q.2} =>
      ‖G (diagonal σ) Xm z q.1.1 q.1.2‖ / (sigS σ q.1.1 * sigS σ q.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩
  rw [div_le_iff₀ hpos] at h1
  linarith

/-- `|ab/c| ≤ AB/C` from `|a| ≤ A`, `|b| ≤ B`, `0 < C ≤ |c|`. -/
private theorem bounds_quot_le {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hC : 0 < C) (hc : C ≤ ‖c‖) : ‖a * b / c‖ ≤ A * B / C := by
  rw [norm_div, norm_mul]
  exact div_le_div₀ (mul_nonneg ((norm_nonneg _).trans ha) ((norm_nonneg _).trans hb))
    (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)) hC hc

/-- The scale facts behind (G*): `0 ≤ N^{ε₁}Υ ≤ N^{ε₁−c₀}` and
`4^p N^{ε₁−c₀} τ⁻¹ ≤ c_as/16`. -/
private theorem bounds_scale {τ c₀ ε₁ Υ : ℝ} {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥ : 0 ≤ Υ)
    (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2)) :
    0 ≤ (N : ℝ) ^ ε₁ * Υ ∧ (N : ℝ) ^ ε₁ * Υ ≤ (N : ℝ) ^ (ε₁ - c₀) ∧
      4 ^ p * (N : ℝ) ^ (ε₁ - c₀) * τ⁻¹ ≤ mAsympLower τ / 16 := by
  have hτ := h.pos
  have hτ1 := bounds_tau_le_one h
  obtain ⟨hca, -⟩ := bounds_cas h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast bounds_N_pos h
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 ≤ (N : ℝ) ^ (ε₁ - c₀) := Real.rpow_nonneg hN0.le _
  have hLc : (N : ℝ) ^ (ε₁ - c₀) ≤ ((N : ℝ) ^ (c₀ / 2))⁻¹ := by
    rw [← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hK0 : 0 < 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ := by positivity
  have hLK : (N : ℝ) ^ (ε₁ - c₀) * (4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹) ≤ 1 := by
    calc (N : ℝ) ^ (ε₁ - c₀) * (4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹)
        ≤ (4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹)⁻¹
          * (4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹) :=
          mul_le_mul_of_nonneg_right (hLc.trans (inv_anti₀ hK0 hG)) hK0.le
      _ = 1 := inv_mul_cancel₀ hK0.ne'
  refine ⟨mul_nonneg (Real.rpow_nonneg hN0.le _) hΥ, ?_, ?_⟩
  · rw [sub_eq_add_neg, Real.rpow_add hN0]
    exact mul_le_mul_of_nonneg_left hΥc₀ (Real.rpow_nonneg hN0.le _)
  · set L := (N : ℝ) ^ (ε₁ - c₀)
    set ca := mAsympLower τ
    have e : L * (4 ^ (p + 2) * τ⁻¹ ^ 2 * ca⁻¹)
        = (4 ^ p * L * τ⁻¹) * (16 * τ⁻¹ * ca⁻¹) := by ring
    rw [e] at hLK
    have h16 : 0 < 16 * τ⁻¹ * ca⁻¹ := by positivity
    have h1 : 4 ^ p * L * τ⁻¹ ≤ (16 * τ⁻¹ * ca⁻¹)⁻¹ := by
      rw [show (16 * τ⁻¹ * ca⁻¹)⁻¹ = 1 / (16 * τ⁻¹ * ca⁻¹) from (one_div _).symm,
        le_div_iff₀ h16]
      exact hLK
    calc 4 ^ p * L * τ⁻¹ ≤ (16 * τ⁻¹ * ca⁻¹)⁻¹ := h1
      _ = τ * ca / 16 := by field_simp
      _ ≤ ca / 16 := by
          have : τ * ca ≤ 1 * ca := mul_le_mul_of_nonneg_right hτ1 hca.le
          linarith

/-- (Gtt_bound) for minors with `|S| ≤ 2p`: on `{Λ ≤ N^{ε₁−c₀}} ∩ {Λ_o ≤ N^{ε₁}Υ}`, under
(G*) `4^{p+2} τ⁻² c_as⁻¹ ≤ N^{c₀/2}`, for `s, t ∉ S`:
`|G^{(S)}_{st}| ≤ 2^{|S|} σ̲_s σ̲_t N^{ε₁}Υ` (`s ≠ t`) and
`(c_as/2) σ̲_t ≤ |G^{(S)}_{tt}| ≤ (C_as + 1) σ̲_t`. -/
theorem minor_bounds {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥ : 0 ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (S : Finset (Fin M ⊕ Fin N)) (hS : S.card ≤ 2 * p) (s t : Fin M ⊕ Fin N) (hs : s ∉ S)
    (ht : t ∉ S) :
    (s ≠ t → ‖Gm (diagonal σ) Xm z S s t‖ ≤
        2 ^ S.card * sigS σ s * sigS σ t * ((N : ℝ) ^ ε₁ * Υ)) ∧
      mAsympLower τ / 2 * sigS σ t ≤ ‖Gm (diagonal σ) Xm z S t t‖ ∧
      ‖Gm (diagonal σ) Xm z S t t‖ ≤ (mAsympUpper c τ + 1) * sigS σ t := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  obtain ⟨hca, hca1⟩ := bounds_cas h
  obtain ⟨hδ0, hδL, hkey⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  set δ := (N : ℝ) ^ ε₁ * Υ with hδdef
  set L := (N : ℝ) ^ (ε₁ - c₀) with hLdef
  set ca := mAsympLower τ with hcadef
  set u : ℝ := 4 ^ p with hudef
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hL0 : 0 ≤ L := hδ0.trans hδL
  set ρ := τ⁻¹ ^ 2 * δ ^ 2 * (2 / ca) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hw := fun x => bounds_sigS_pos (N := N) hσ x
  have hw' := fun x => bounds_sigS_le h x
  -- `u δ τ⁻¹ ≤ c_as/16`
  have hkeyδ : u * δ * τ⁻¹ ≤ ca / 16 :=
    le_trans (by gcongr) hkey
  have hgain : u * τ⁻¹ * δ * (2 / ca) ≤ 1 := by
    have : u * τ⁻¹ * δ * (2 / ca) = (u * δ * τ⁻¹) * (2 / ca) := by ring
    rw [this]
    calc (u * δ * τ⁻¹) * (2 / ca) ≤ ca / 16 * (2 / ca) :=
          mul_le_mul_of_nonneg_right hkeyδ (by positivity)
      _ = 1 / 8 := by field_simp; norm_num
      _ ≤ 1 := by norm_num
  have hdrift : u ^ 2 * ρ ≤ ca / 128 := by
    have : u ^ 2 * ρ = (u * δ * τ⁻¹) ^ 2 * (2 / ca) := by rw [hρdef]; ring
    rw [this]
    calc (u * δ * τ⁻¹) ^ 2 * (2 / ca) ≤ (ca / 16) ^ 2 * (2 / ca) := by
          gcongr
      _ = ca / 128 := by field_simp; norm_num
  have htL : τ⁻¹ * L ≤ ca / 16 := by
    calc τ⁻¹ * L = 1 * L * τ⁻¹ := by ring
      _ ≤ u * L * τ⁻¹ := by gcongr
      _ ≤ ca / 16 := hkey
  have hd : ∀ k, k ≤ 2 * p → τ⁻¹ * L + 4 ^ k * ρ ≤ ca / 2 := by
    intro k hk
    have h4 : (4 : ℝ) ^ k ≤ u ^ 2 := by
      rw [hudef, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (4 : ℝ) ^ k * ρ ≤ u ^ 2 * ρ := mul_le_mul_of_nonneg_right h4 hρ0
    linarith
  have h2u : ∀ k, k ≤ 2 * p → (2 : ℝ) ^ k ≤ u := by
    intro k hk
    calc (2 : ℝ) ^ k ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) hk
      _ = u := by rw [hudef, pow_mul]; norm_num
  have hm := fun x => norm_mS_bounds hc h hσ hz hx x
  -- the induction on `|S|`
  have key : ∀ k, k ≤ 2 * p → ∀ S : Finset (Fin M ⊕ Fin N), S.card = k →
      (∀ x y, x ∉ S → y ∉ S → x ≠ y →
        ‖Gm (diagonal σ) Xm z S x y‖ ≤ 2 ^ k * sigS σ x * sigS σ y * δ) ∧
      (∀ x, x ∉ S → ‖Gm (diagonal σ) Xm z S x x - mS N σ z x‖
        ≤ (τ⁻¹ * L + 4 ^ k * ρ) * sigS σ x) := by
    intro k
    induction k with
    | zero =>
      intro _ S0 hS0
      rw [Finset.card_eq_zero.1 hS0, Gm_empty]
      refine ⟨fun x y _ _ hxy => ?_, fun x _ => ?_⟩
      · refine (bounds_offO_le hσ Xm z hxy).trans ?_
        rw [pow_zero, one_mul]
        exact mul_le_mul_of_nonneg_left hΛo (mul_pos (hw x) (hw y)).le
      · have h1 := bounds_entry_le hσ Xm z x x
        simp only [↓reduceIte] at h1
        refine h1.trans ?_
        have hΛ0 := bounds_lambda_nonneg hσ Xm z
        calc sigS σ x * sigS σ x * Lambda σ Xm z = (sigS σ x * Lambda σ Xm z) * sigS σ x := by
              ring
          _ ≤ (τ⁻¹ * L + 4 ^ 0 * ρ) * sigS σ x := by
              refine mul_le_mul_of_nonneg_right ?_ (hw x).le
              have : sigS σ x * Lambda σ Xm z ≤ τ⁻¹ * L :=
                mul_le_mul (hw' x) hΛ hΛ0 (by positivity)
              have : 0 ≤ (4 : ℝ) ^ 0 * ρ := by positivity
              linarith
    | succ k ih =>
      intro hk S0 hS0
      obtain ⟨r, hr⟩ := Finset.card_pos.1 (by omega : 0 < S0.card)
      set S1 := S0.erase r with hS1
      have hS1c : S1.card = k := by rw [Finset.card_erase_of_mem hr]; omega
      have hins : insert r S1 = S0 := Finset.insert_erase hr
      have hrS1 : r ∉ S1 := Finset.notMem_erase r S0
      obtain ⟨ihO, ihD⟩ := ih (by omega) S1 hS1c
      have hnot : ∀ x, x ∉ S0 → x ∉ S1 := fun x hx h1 => hx (Finset.mem_of_mem_erase h1)
      have hne : ∀ x, x ∉ S0 → x ≠ r := fun x hx e => hx (e ▸ hr)
      have hstu : ∀ x y, x ∉ S0 → y ∉ S0 → Gm (diagonal σ) Xm z S0 x y
          = Gm (diagonal σ) Xm z S1 x y - Gm (diagonal σ) Xm z S1 x r
            * Gm (diagonal σ) Xm z S1 r y / Gm (diagonal σ) Xm z S1 r r := by
        intro x y hx hy
        have := Gstu_minor hSig Xm hz.1 S1 r x y hrS1 (by rwa [hins]) (by rwa [hins])
        rwa [hins] at this
      have hdk := hd k (by omega)
      have hrr : ca / 2 * sigS σ r ≤ ‖Gm (diagonal σ) Xm z S1 r r‖ := by
        have h1 := ihD r hrS1
        have h2 := norm_sub_norm_le (mS N σ z r) (Gm (diagonal σ) Xm z S1 r r)
        rw [norm_sub_rev] at h2
        have h3 := (hm r).1
        have h4 : (τ⁻¹ * L + 4 ^ k * ρ) * sigS σ r ≤ ca / 2 * sigS σ r :=
          mul_le_mul_of_nonneg_right hdk (hw r).le
        linarith
      have hrr0 : 0 < ca / 2 * sigS σ r := by have := hw r; positivity
      have h2k := h2u k (by omega)
      have hquot : ∀ x y, x ∉ S0 → y ∉ S0 →
          ‖Gm (diagonal σ) Xm z S1 x r * Gm (diagonal σ) Xm z S1 r y
            / Gm (diagonal σ) Xm z S1 r r‖
          ≤ 2 ^ k * sigS σ x * sigS σ y * δ * (2 ^ k * sigS σ r * δ * (2 / ca)) := by
        intro x y hx hy
        refine (bounds_quot_le (ihO x r (hnot x hx) hrS1 (hne x hx))
          (ihO r y hrS1 (hnot y hy) (hne y hy).symm) hrr0 hrr).trans (le_of_eq ?_)
        have := hw r
        field_simp
      have hg : 2 ^ k * sigS σ r * δ * (2 / ca) ≤ 1 := by
        calc 2 ^ k * sigS σ r * δ * (2 / ca) ≤ u * τ⁻¹ * δ * (2 / ca) := by
              gcongr
              all_goals first | exact hw' r | exact (hw r).le
          _ ≤ 1 := hgain
      refine ⟨fun x y hx hy hxy => ?_, fun x hx => ?_⟩
      · rw [hstu x y hx hy]
        refine (norm_sub_le _ _).trans ?_
        have h1 := ihO x y (hnot x hx) (hnot y hy) hxy
        have h2 := hquot x y hx hy
        have h3 : 0 ≤ 2 ^ k * sigS σ x * sigS σ y * δ := by
          have := hw x; have := hw y; positivity
        have h4 := mul_le_mul_of_nonneg_left hg h3
        rw [pow_succ]
        nlinarith
      · rw [hstu x x hx hx]
        have e : Gm (diagonal σ) Xm z S1 x x - Gm (diagonal σ) Xm z S1 x r
              * Gm (diagonal σ) Xm z S1 r x / Gm (diagonal σ) Xm z S1 r r - mS N σ z x
            = (Gm (diagonal σ) Xm z S1 x x - mS N σ z x) - Gm (diagonal σ) Xm z S1 x r
              * Gm (diagonal σ) Xm z S1 r x / Gm (diagonal σ) Xm z S1 r r := by ring
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        have h1 := ihD x (hnot x hx)
        have h2 := hquot x x hx hx
        have h3 : 2 ^ k * sigS σ x * sigS σ x * δ * (2 ^ k * sigS σ r * δ * (2 / ca))
            ≤ 4 ^ k * ρ * sigS σ x := by
          have e2 : 2 ^ k * sigS σ x * sigS σ x * δ * (2 ^ k * sigS σ r * δ * (2 / ca))
              = 4 ^ k * ((sigS σ x * sigS σ r) * δ ^ 2 * (2 / ca)) * sigS σ x := by
            rw [show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
            ring
          rw [e2, hρdef]
          have hxr : sigS σ x * sigS σ r ≤ τ⁻¹ ^ 2 := by
            rw [sq]
            exact mul_le_mul (hw' x) (hw' r) (hw r).le (by positivity)
          have := hw x
          gcongr
        have h6 : (τ⁻¹ * L + 4 ^ (k + 1) * ρ) * sigS σ x = (τ⁻¹ * L + 4 ^ k * ρ) * sigS σ x
            + 4 ^ k * ρ * sigS σ x + 2 * (4 ^ k * ρ * sigS σ x) := by
          rw [pow_succ]; ring
        have h7 : 0 ≤ 4 ^ k * ρ * sigS σ x := by have := hw x; positivity
        linarith
  obtain ⟨hO, hD⟩ := key S.card hS S rfl
  have hdS := hd S.card hS
  have h1 := hD t ht
  have h2 : (τ⁻¹ * L + 4 ^ S.card * ρ) * sigS σ t ≤ ca / 2 * sigS σ t :=
    mul_le_mul_of_nonneg_right hdS (hw t).le
  refine ⟨fun hst => hO s t hs ht hst, ?_, ?_⟩
  · have h3 := norm_sub_norm_le (mS N σ z t) (Gm (diagonal σ) Xm z S t t)
    rw [norm_sub_rev] at h3
    have h4 := (hm t).1
    linarith
  · have h3 := norm_le_norm_add_norm_sub' (Gm (diagonal σ) Xm z S t t) (mS N σ z t)
    have h4 := (hm t).2
    have h5 : ca / 2 * sigS σ t ≤ 1 * sigS σ t :=
      mul_le_mul_of_nonneg_right (by linarith) (hw t).le
    nlinarith

/-! ## Calculus of the Möbius pieces `F^{[U]}(T)` (proof of Lemma 5.6) -/

section MobCalc

variable {α : Type*} [DecidableEq α]

/-- The difference `Δ_v F (S) = F(S ∖ {v}) − F(S)`. -/
private def bndDiff (v : α) (F : Finset α → ℂ) (S : Finset α) : ℂ := F (S.erase v) - F S

/-- `F^{[U ∪ {v}]}(R) = (Δ_v F)^{[U]}(R)` for `v ∉ U`. -/
private theorem mobPart_insert' (F : Finset α → ℂ) (R A : Finset α) {v : α} (hv : v ∉ A) :
    mobPart F R (insert v A) = mobPart (bndDiff v F) R A := by
  unfold mobPart bndDiff
  rw [Finset.sum_powerset_insert hv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun V hV => ?_
  have hVA := Finset.mem_powerset.1 hV
  have hvV : v ∉ V := fun h => hv (hVA h)
  have hc := Finset.card_le_card hVA
  rw [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem hvV, Finset.sdiff_insert,
    Nat.add_sub_add_right, show A.card + 1 - V.card = A.card - V.card + 1 by omega, pow_succ]
  ring

private theorem mobPart_congr' {F G : Finset α → ℂ} {R A : Finset α}
    (h : ∀ V ⊆ A, F (R \ V) = G (R \ V)) : mobPart F R A = mobPart G R A := by
  unfold mobPart
  exact Finset.sum_congr rfl fun V hV => by rw [h V (Finset.mem_powerset.1 hV)]

private theorem mobPart_add' (F G : Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => F S + G S) R A = mobPart F R A + mobPart G R A := by
  unfold mobPart
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun V _ => by ring

private theorem mobPart_sub' (F G : Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => F S - G S) R A = mobPart F R A - mobPart G R A := by
  unfold mobPart
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun V _ => by ring

private theorem mobPart_neg' (F : Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => -F S) R A = -mobPart F R A := by
  unfold mobPart
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun V _ => by ring

private theorem mobPart_const_mul' (c : ℂ) (F : Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => c * F S) R A = c * mobPart F R A := by
  unfold mobPart
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun V _ => by ring

private theorem mobPart_sum' {ι : Type*} (s : Finset ι) (F : ι → Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => ∑ i ∈ s, F i S) R A = ∑ i ∈ s, mobPart (F i) R A := by
  unfold mobPart
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- `c^{[U]} = 0` for a constant `c` and `U ≠ ∅`. -/
private theorem mobPart_const' (c : ℂ) (R A : Finset α) (hA : A.Nonempty) :
    mobPart (fun _ => c) R A = 0 := by
  obtain ⟨v, hv⟩ := hA
  rw [← Finset.insert_erase hv, mobPart_insert' _ _ _ (Finset.notMem_erase v A)]
  unfold mobPart bndDiff
  simp

/-- `(F ∘ (· ∖ {v}))^{[U]}(R) = F^{[U]}(R ∖ {v})`. -/
private theorem mobPart_erase' (F : Finset α → ℂ) (R A : Finset α) (v : α) :
    mobPart (fun S => F (S.erase v)) R A = mobPart F (R.erase v) A := by
  unfold mobPart
  exact Finset.sum_congr rfl fun V _ => by rw [Finset.erase_sdiff_comm]

/-- `(F ∘ (· ∪ {v}))^{[U]}(R) = F^{[U]}(R ∪ {v})` for `v ∉ U`. -/
private theorem mobPart_insertShift' (F : Finset α → ℂ) (R A : Finset α) {v : α} (hv : v ∉ A) :
    mobPart (fun S => F (insert v S)) R A = mobPart F (insert v R) A := by
  unfold mobPart
  refine Finset.sum_congr rfl fun V hV => ?_
  have hvV : v ∉ V := fun h => hv (Finset.mem_powerset.1 hV h)
  rw [Finset.insert_sdiff_of_notMem _ hvV]

/-- Transport along an embedding: `(Φ ∘ map e)^{[U]}(T) = Φ^{[e U]}(e T)`. -/
private theorem mobPart_map' {β : Type*} [DecidableEq β] (e : α ↪ β) (Φ : Finset β → ℂ)
    (T U : Finset α) : mobPart (fun S => Φ (S.map e)) T U = mobPart Φ (T.map e) (U.map e) := by
  induction U using Finset.induction_on generalizing Φ with
  | empty => simp [mobPart_empty]
  | insert v U hv ih =>
    rw [mobPart_insert' _ _ _ hv, Finset.map_insert,
      mobPart_insert' _ _ _ (by simpa using hv)]
    rw [← ih]
    unfold bndDiff
    congr 1
    funext S
    simp only [Finset.map_erase]

/-- The product rule `(fg)^{[U]}(R) = Σ_{B ⊆ U} f^{[B]}(R) g^{[U∖B]}(R∖B)`. -/
private theorem mobPart_mul' (f g : Finset α → ℂ) (R A : Finset α) :
    mobPart (fun S => f S * g S) R A
      = ∑ B ∈ A.powerset, mobPart f R B * mobPart g (R \ B) (A \ B) := by
  induction A using Finset.induction_on generalizing f g R with
  | empty => simp [mobPart_empty]
  | insert v A hv ih =>
    rw [mobPart_insert' _ _ _ hv]
    have e : bndDiff v (fun S => f S * g S)
        = fun S => bndDiff v f S * g (S.erase v) + f S * bndDiff v g S := by
      funext S
      unfold bndDiff
      ring
    rw [e, mobPart_add', ih, ih, Finset.sum_powerset_insert hv, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun B hB => ?_
      have hvB : v ∉ B := fun h => hv (Finset.mem_powerset.1 hB h)
      have hvAB : v ∉ A \ B := fun h => hv (Finset.mem_sdiff.1 h).1
      rw [← mobPart_insert' _ _ _ hvAB, Finset.insert_sdiff_of_notMem _ hvB]
    · refine Finset.sum_congr rfl fun B hB => ?_
      have hvB : v ∉ B := fun h => hv (Finset.mem_powerset.1 hB h)
      rw [← mobPart_insert' _ _ _ hvB, mobPart_erase', Finset.sdiff_insert,
        Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hv]

/-- The rising factorial `(a)_n = a (a+1) ⋯ (a+n−1)`. -/
private def bndRise (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => bndRise a n * (a + n)

private theorem bndRise_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ bndRise a n := by
  induction n with
  | zero => simp [bndRise]
  | succ n ih => simp only [bndRise]; positivity

private theorem bndRise_succ' (a : ℝ) (n : ℕ) : bndRise a (n + 1) = a * bndRise (a + 1) n := by
  induction n with
  | zero => simp [bndRise]
  | succ n ih =>
    rw [bndRise, ih, bndRise]
    push_cast
    ring

private theorem bndRise_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    bndRise a n ≤ bndRise b n := by
  induction n with
  | zero => simp [bndRise]
  | succ n ih =>
    simp only [bndRise]
    exact mul_le_mul ih (by linarith) (by positivity) ((bndRise_nonneg ha n).trans ih)

private theorem bndRise_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : bndRise a n ≤ (a + n) ^ n := by
  induction n with
  | zero => simp [bndRise]
  | succ n ih =>
    simp only [bndRise, pow_succ]
    push_cast
    exact mul_le_mul (ih.trans (pow_le_pow_left₀ (by positivity) (by linarith) n))
      (by linarith) (by positivity) (by positivity)

/-- The Vandermonde identity `Σ_{B ⊆ A} (a)_{|B|} (b)_{|A∖B|} = (a+b)_{|A|}`. -/
private theorem bndRise_vandermonde (a b : ℝ) (A : Finset α) :
    ∑ B ∈ A.powerset, bndRise a B.card * bndRise b (A \ B).card = bndRise (a + b) A.card := by
  induction A using Finset.induction_on with
  | empty => simp [bndRise]
  | insert v A hv ih =>
    rw [Finset.sum_powerset_insert hv, Finset.card_insert_of_notMem hv, bndRise, ← ih,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hBA := Finset.mem_powerset.1 hB
    have hvB : v ∉ B := fun h => hv (hBA h)
    have hvAB : v ∉ A \ B := fun h => hv (Finset.mem_sdiff.1 h).1
    rw [Finset.insert_sdiff_of_notMem _ hvB, Finset.card_insert_of_notMem hvAB,
      Finset.card_insert_of_notMem hvB, Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem hv, bndRise, bndRise]
    have hc : ((A \ B).card : ℝ) + B.card = A.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hBA
    linear_combination (bndRise a B.card * bndRise b (A \ B).card) * hc

/-- The control `|f^{[A]}(R)| ≤ K Γ^{|A|} (a)_{|A|} δ^{|A|+e}` for `R ⊆ R₀`, `A ⊆ W₀ ∩ R`. -/
private def bndCtrl (R0 W0 : Finset α) (f : Finset α → ℂ) (K Γ δ a : ℝ) (e : ℕ) : Prop :=
  ∀ R ⊆ R0, ∀ A ⊆ W0, A ⊆ R → ‖mobPart f R A‖ ≤ K * Γ ^ A.card * bndRise a A.card * δ ^ (A.card + e)

/-- Controls multiply: the constants multiply, the rising-factorial parameters and the
`δ`-excesses add. -/
private theorem bndCtrl_mul {R0 W0 : Finset α} {f g : Finset α → ℂ} {K1 K2 Γ δ a b : ℝ}
    {e1 e2 : ℕ} (hf : bndCtrl R0 W0 f K1 Γ δ a e1) (hg : bndCtrl R0 W0 g K2 Γ δ b e2) :
    bndCtrl R0 W0 (fun S => f S * g S) (K1 * K2) Γ δ (a + b) (e1 + e2) := by
  intro R hR A hA hAR
  rw [mobPart_mul']
  refine (norm_sum_le _ _).trans ?_
  calc ∑ B ∈ A.powerset, ‖mobPart f R B * mobPart g (R \ B) (A \ B)‖
      ≤ ∑ B ∈ A.powerset, (K1 * Γ ^ B.card * bndRise a B.card * δ ^ (B.card + e1))
          * (K2 * Γ ^ (A \ B).card * bndRise b (A \ B).card * δ ^ ((A \ B).card + e2)) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hBA := Finset.mem_powerset.1 hB
        rw [norm_mul]
        have h1 := hf R hR B (hBA.trans hA) (hBA.trans hAR)
        have h2 := hg (R \ B) (Finset.sdiff_subset.trans hR) (A \ B)
          (Finset.sdiff_subset.trans hA) (Finset.sdiff_subset_sdiff hAR le_rfl)
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = ∑ B ∈ A.powerset, (K1 * K2 * Γ ^ A.card * δ ^ (A.card + (e1 + e2)))
          * (bndRise a B.card * bndRise b (A \ B).card) := by
        refine Finset.sum_congr rfl fun B hB => ?_
        have hc := Finset.card_sdiff_add_card_eq_card (Finset.mem_powerset.1 hB)
        have e1' : Γ ^ A.card = Γ ^ B.card * Γ ^ (A \ B).card := by
          rw [← pow_add]; congr 1; omega
        have e2' : δ ^ (A.card + (e1 + e2)) = δ ^ (B.card + e1) * δ ^ ((A \ B).card + e2) := by
          rw [← pow_add]; congr 1; omega
        rw [e1', e2']
        ring
    _ = K1 * K2 * Γ ^ A.card * bndRise (a + b) A.card * δ ^ (A.card + (e1 + e2)) := by
        rw [← Finset.mul_sum, bndRise_vandermonde]
        ring

/-- A control at `R ∪ {v}` gives a control of `S ↦ f(S ∪ {v})` at `R`, for `v ∉ W₀`. -/
private theorem bndCtrl_insertShift {R0 W0 : Finset α} {f : Finset α → ℂ} {K Γ δ a : ℝ} {e : ℕ}
    {v : α} (hv : v ∉ W0) (hf : bndCtrl (insert v R0) W0 f K Γ δ a e) :
    bndCtrl R0 W0 (fun S => f (insert v S)) K Γ δ a e := by
  intro R hR A hA hAR
  rw [mobPart_insertShift' _ _ _ (fun h => hv (hA h))]
  exact hf (insert v R) (Finset.insert_subset_insert v hR) A hA
    (hAR.trans (Finset.subset_insert v R))

end MobCalc

/-! ## The Möbius pieces of `G^{(S)}_{xy}` and `1/G^{(S)}_{xx}` -/

section MobBound

variable {κ : Type*} [DecidableEq κ]

/-- The recursion (β) for an abstract family of minors `Gf S` satisfying (Gstu) and the bounds of
`minor_bounds` with `a₀ = 4^p` and `H = 2/c_as` for `|S| ≤ L`: with `Γ = 4a₀²H²t²`, for
`W ⊆ R`, `|R| ≤ L`, `x, y ∉ R`, `n = |W|`,
`|(G_{xy})^{[W]}(R)| ≤ a₀ w_x w_y Γ^n (1/4)_n δ^{n+1}` (`x ≠ y` or `n ≥ 1`) and
`|(1/G_{xx})^{[W]}(R)| ≤ (H/t) Γ^n (1/4)_n δ^{n+1}` (`n ≥ 1`). -/
private theorem bounds_mob_main (Gf : Finset κ → κ → κ → ℂ) (w : κ → ℝ) (L : ℕ)
    {a0 Hc tt δ : ℝ}
    (hstu : ∀ S r s t, r ∉ S → s ∉ insert r S → t ∉ insert r S →
      Gf (insert r S) s t = Gf S s t - Gf S s r * Gf S r t / Gf S r r)
    (hnz : ∀ S r, r ∉ S → Gf S r r ≠ 0)
    (hoff : ∀ S : Finset κ, S.card ≤ L → ∀ s t, s ∉ S → t ∉ S → s ≠ t →
      ‖Gf S s t‖ ≤ a0 * w s * w t * δ)
    (hinv : ∀ S : Finset κ, S.card ≤ L → ∀ t, t ∉ S → ‖(Gf S t t)⁻¹‖ ≤ Hc / w t)
    (hw0 : ∀ s, 0 < w s) (hwt : ∀ s, w s ≤ tt) (ha0 : 1 ≤ a0) (hHc : 1 ≤ Hc) (htt : 1 ≤ tt)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    (∀ (R W : Finset κ) x y, R.card ≤ L → x ∉ R → y ∉ R → W ⊆ R → W.card = n →
      (x ≠ y ∨ 0 < n) → ‖mobPart (fun S => Gf S x y) R W‖
        ≤ a0 * w x * w y * (4 * a0 ^ 2 * Hc ^ 2 * tt ^ 2) ^ n * bndRise (1 / 4) n
          * δ ^ (n + 1)) ∧
    (∀ (R W : Finset κ) x, R.card ≤ L → x ∉ R → W ⊆ R → W.card = n → 0 < n →
      ‖mobPart (fun S => (Gf S x x)⁻¹) R W‖
        ≤ Hc / tt * (4 * a0 ^ 2 * Hc ^ 2 * tt ^ 2) ^ n * bndRise (1 / 4) n * δ ^ (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  set Γ := 4 * a0 ^ 2 * Hc ^ 2 * tt ^ 2 with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  -- the controls given by the induction hypothesis
  have cO : ∀ B : Finset κ, B.card ≤ L → ∀ W0 : Finset κ, W0.card < n → ∀ x y, x ∉ B → y ∉ B →
      x ≠ y → bndCtrl B W0 (fun S => Gf S x y) (a0 * w x * w y) Γ δ (1 / 4) 1 := by
    intro B hB W0 hW0 x y hx hy hxy R hR A hA hAR
    exact (ih A.card ((Finset.card_le_card hA).trans_lt hW0)).1 R A x y
      ((Finset.card_le_card hR).trans hB) (fun h => hx (hR h)) (fun h => hy (hR h)) hAR rfl
      (Or.inl hxy)
  have cH : ∀ B : Finset κ, B.card ≤ L → ∀ W0 : Finset κ, W0.card < n → ∀ x, x ∉ B →
      bndCtrl B W0 (fun S => (Gf S x x)⁻¹) (Hc / w x) Γ δ (1 / 4) 0 := by
    intro B hB W0 hW0 x hx R hR A hA hAR
    have hRL := (Finset.card_le_card hR).trans hB
    have hxR : x ∉ R := fun h => hx (hR h)
    rcases Nat.eq_zero_or_pos A.card with h0 | h0
    · rw [Finset.card_eq_zero.1 h0, mobPart_empty]
      simpa [bndRise] using hinv R hRL x hxR
    · refine ((ih A.card ((Finset.card_le_card hA).trans_lt hW0)).2 R A x hRL hxR hAR rfl
        h0).trans ?_
      rw [add_zero]
      have h1 : Hc / tt ≤ Hc / w x :=
        div_le_div_of_nonneg_left (by linarith) (hw0 x) (hwt x)
      have h2 : δ ^ (A.card + 1) ≤ δ ^ A.card := pow_le_pow_of_le_one hδ0 hδ1 (by omega)
      have h3 := bndRise_nonneg (a := 1 / 4) (by norm_num) A.card
      have h4 : 0 ≤ Hc / w x := div_nonneg (by linarith) (hw0 x).le
      gcongr
  refine ⟨?_, ?_⟩
  · intro R W x y hRL hx hy hWR hWn hxy
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Finset.card_eq_zero.1 hWn, mobPart_empty]
      simpa [bndRise] using hoff R hRL x y hx hy (hxy.resolve_right (lt_irrefl 0))
    obtain ⟨v, hvW⟩ := Finset.card_pos.1 (by omega : 0 < W.card)
    have hvW0 : v ∉ W.erase v := Finset.notMem_erase v W
    have hW0c : (W.erase v).card = n - 1 := by rw [Finset.card_erase_of_mem hvW]; omega
    have hvR : v ∈ R := hWR hvW
    have hR0L : (R.erase v).card ≤ L := (Finset.card_le_card (Finset.erase_subset v R)).trans hRL
    have hxR0 : x ∉ R.erase v := fun h => hx (Finset.mem_of_mem_erase h)
    have hyR0 : y ∉ R.erase v := fun h => hy (Finset.mem_of_mem_erase h)
    have hvR0 : v ∉ R.erase v := Finset.notMem_erase v R
    have hxv : x ≠ v := fun e => hx (e ▸ hvR)
    have hyv : y ≠ v := fun e => hy (e ▸ hvR)
    have hW0R0 : W.erase v ⊆ R.erase v := Finset.erase_subset_erase v hWR
    have hW0n : (W.erase v).card < n := by omega
    rw [← Finset.insert_erase hvW, mobPart_insert' _ _ _ hvW0]
    have hP : mobPart (bndDiff v (fun S => Gf S x y)) R (W.erase v)
        = mobPart (fun S => Gf S x v * Gf S v y * (Gf S v v)⁻¹) (R.erase v) (W.erase v) := by
      rw [← mobPart_erase']
      refine mobPart_congr' fun V hV => ?_
      have hvS : v ∈ R \ V := Finset.mem_sdiff.2 ⟨hvR, fun h => hvW0 (hV h)⟩
      have e1 := Finset.insert_erase hvS
      have hxS : x ∉ R \ V := fun h => hx (Finset.mem_sdiff.1 h).1
      have hyS : y ∉ R \ V := fun h => hy (Finset.mem_sdiff.1 h).1
      have hst := hstu ((R \ V).erase v) v x y (Finset.notMem_erase v _) (by rw [e1]; exact hxS)
        (by rw [e1]; exact hyS)
      rw [e1] at hst
      unfold bndDiff
      dsimp only
      rw [hst]
      ring
    rw [hP]
    have hc := bndCtrl_mul (bndCtrl_mul (cO _ hR0L _ hW0n x v hxR0 hvR0 hxv)
      (cO _ hR0L _ hW0n v y hvR0 hyR0 hyv.symm)) (cH _ hR0L _ hW0n v hvR0)
    refine (hc (R.erase v) le_rfl (W.erase v) le_rfl hW0R0).trans ?_
    rw [hW0c]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, bndRise_succ']
    have hwv := hw0 v
    have eK : a0 * w x * w v * (a0 * w v * w y) * (Hc / w v)
        = (a0 * w x * w y) * (a0 * Hc * w v) := by
      field_simp
    have hKv : a0 * Hc * w v ≤ Γ / 4 := by
      have h1 : a0 * Hc * w v ≤ a0 * Hc * tt := by
        have : 0 ≤ a0 * Hc := by positivity
        exact mul_le_mul_of_nonneg_left (hwt v) this
      have h2 : a0 * Hc * tt ≤ a0 * Hc * tt * (a0 * Hc * tt) := by
        have : 1 ≤ a0 * Hc * tt := by
          have := mul_le_mul ha0 hHc zero_le_one (by linarith)
          nlinarith
        nlinarith
      rw [hΓ]
      nlinarith
    have hr : bndRise (1 / 4 + 1 / 4 + 1 / 4) m ≤ bndRise (1 / 4 + 1) m :=
      bndRise_mono (by norm_num) (by norm_num) m
    have hx0 : 0 ≤ a0 * w x * w y := by have := hw0 x; have := hw0 y; positivity
    have hr0 := bndRise_nonneg (a := 1 / 4 + 1 / 4 + 1 / 4) (by norm_num) m
    rw [eK]
    calc a0 * w x * w y * (a0 * Hc * w v) * Γ ^ m * bndRise (1 / 4 + 1 / 4 + 1 / 4) m
          * δ ^ (m + (1 + 1 + 0))
        ≤ a0 * w x * w y * (Γ / 4) * Γ ^ m * bndRise (1 / 4 + 1) m * δ ^ (m + (1 + 1 + 0)) := by
          gcongr
      _ = a0 * w x * w y * Γ ^ (m + 1) * (1 / 4 * bndRise (1 / 4 + 1) m) * δ ^ (m + 1 + 1) := by
          rw [pow_succ]
          ring
  · intro R W x hRL hx hWR hWn hn
    obtain ⟨v, hvW⟩ := Finset.card_pos.1 (by omega : 0 < W.card)
    have hvW0 : v ∉ W.erase v := Finset.notMem_erase v W
    have hW0c : (W.erase v).card = n - 1 := by rw [Finset.card_erase_of_mem hvW]; omega
    have hvR : v ∈ R := hWR hvW
    have hR0L : (R.erase v).card ≤ L := (Finset.card_le_card (Finset.erase_subset v R)).trans hRL
    have hxR0 : x ∉ R.erase v := fun h => hx (Finset.mem_of_mem_erase h)
    have hvR0 : v ∉ R.erase v := Finset.notMem_erase v R
    have hxv : x ≠ v := fun e => hx (e ▸ hvR)
    have hW0R0 : W.erase v ⊆ R.erase v := Finset.erase_subset_erase v hWR
    have hW0n : (W.erase v).card < n := by omega
    rw [← Finset.insert_erase hvW, mobPart_insert' _ _ _ hvW0]
    have hP : mobPart (bndDiff v (fun S => (Gf S x x)⁻¹)) R (W.erase v)
        = -mobPart (fun S => Gf S x v * Gf S v x * (Gf S v v)⁻¹ * (Gf S x x)⁻¹
            * (Gf (insert v S) x x)⁻¹) (R.erase v) (W.erase v) := by
      rw [← mobPart_erase', ← mobPart_neg']
      refine mobPart_congr' fun V hV => ?_
      have hvS : v ∈ R \ V := Finset.mem_sdiff.2 ⟨hvR, fun h => hvW0 (hV h)⟩
      have e1 := Finset.insert_erase hvS
      have hxS : x ∉ R \ V := fun h => hx (Finset.mem_sdiff.1 h).1
      have hst := hstu ((R \ V).erase v) v x x (Finset.notMem_erase v _) (by rw [e1]; exact hxS)
        (by rw [e1]; exact hxS)
      rw [e1] at hst
      have hA := hnz ((R \ V).erase v) x (fun h => hxS (Finset.mem_of_mem_erase h))
      have hC := hnz ((R \ V).erase v) v (Finset.notMem_erase v _)
      have hD := hnz (R \ V) x hxS
      unfold bndDiff
      simp only [e1]
      have h1 : (Gf ((R \ V).erase v) x x)⁻¹ - (Gf (R \ V) x x)⁻¹
          = (Gf (R \ V) x x - Gf ((R \ V).erase v) x x) * (Gf ((R \ V).erase v) x x)⁻¹
            * (Gf (R \ V) x x)⁻¹ := by
        field_simp
      rw [h1, hst]
      ring
    rw [hP, norm_neg]
    have hk : bndCtrl (R.erase v) (W.erase v) (fun S => (Gf (insert v S) x x)⁻¹) (Hc / w x) Γ δ
        (1 / 4) 0 := by
      refine bndCtrl_insertShift (f := fun T => (Gf T x x)⁻¹) hvW0 ?_
      rw [Finset.insert_erase hvR]
      exact cH R hRL _ hW0n x hx
    have hc := bndCtrl_mul (bndCtrl_mul (bndCtrl_mul (bndCtrl_mul
      (cO _ hR0L _ hW0n x v hxR0 hvR0 hxv) (cO _ hR0L _ hW0n v x hvR0 hxR0 hxv.symm))
      (cH _ hR0L _ hW0n v hvR0)) (cH _ hR0L _ hW0n x hxR0)) hk
    refine (hc (R.erase v) le_rfl (W.erase v) le_rfl hW0R0).trans ?_
    rw [hW0c]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, bndRise_succ']
    have hwv := hw0 v
    have hwx := hw0 x
    have eK : a0 * w x * w v * (a0 * w v * w x) * (Hc / w v) * (Hc / w x) * (Hc / w x)
        = a0 ^ 2 * Hc ^ 3 * w v := by
      field_simp
    have hKv : a0 ^ 2 * Hc ^ 3 * w v ≤ Hc / tt * (Γ / 4) := by
      have e : Hc / tt * (Γ / 4) = a0 ^ 2 * Hc ^ 3 * tt := by
        rw [hΓ]; field_simp
      rw [e]
      have : 0 ≤ a0 ^ 2 * Hc ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_left (hwt v) this
    have hr : bndRise (1 / 4 + 1 / 4 + 1 / 4 + 1 / 4 + 1 / 4) m ≤ bndRise (1 / 4 + 1) m :=
      le_of_eq (by norm_num)
    have hr0 := bndRise_nonneg (a := 1 / 4 + 1 / 4 + 1 / 4 + 1 / 4 + 1 / 4) (by norm_num) m
    rw [eK]
    calc a0 ^ 2 * Hc ^ 3 * w v * Γ ^ m * bndRise (1 / 4 + 1 / 4 + 1 / 4 + 1 / 4 + 1 / 4) m
          * δ ^ (m + (1 + 1 + 0 + 0 + 0))
        ≤ Hc / tt * (Γ / 4) * Γ ^ m * bndRise (1 / 4 + 1) m * δ ^ (m + (1 + 1 + 0 + 0 + 0)) := by
          gcongr
      _ = Hc / tt * Γ ^ (m + 1) * (1 / 4 * bndRise (1 / 4 + 1) m) * δ ^ (m + 1 + 1) := by
          rw [pow_succ]
          ring

end MobBound

/-- The Möbius piece of `Φ(R) = −h(R) − c − K Σ_j g_j(R ∪ {q})` for `∅ ≠ U ∌ q`:
`Φ^{[U]}(R) = −h^{[U]}(R) − K Σ_j g_j^{[U]}(R ∪ {q})`. -/
private theorem bounds_mob_split {κ ι : Type*} [DecidableEq κ] [Fintype ι] (h : Finset κ → ℂ)
    (g : ι → Finset κ → ℂ) (c K : ℂ) (q : κ) (R U : Finset κ) (hU : U.Nonempty) (hq : q ∉ U) :
    mobPart (fun S => -h S - c - K * ∑ j, g j (insert q S)) R U
      = -mobPart h R U - K * ∑ j, mobPart (g j) (insert q R) U := by
  rw [mobPart_sub', mobPart_sub', mobPart_neg', mobPart_const' c R U hU, mobPart_const_mul',
    mobPart_sum']
  congr 2
  · ring
  · exact Finset.sum_congr rfl fun j _ => mobPart_insertShift' _ _ _ hq

/-- `K_Z(p) = (1 + τ⁻¹)(8p)^{2p} (4^p (C_as + 1) · 2/c_as)^{8p} τ^{−16p}`. -/
def mobConst (p : ℕ) (τ c : ℝ) : ℝ :=
  (1 + τ⁻¹) * (8 * p : ℝ) ^ (2 * p) *
    (4 ^ p * (mAsympUpper c τ + 1) * (2 / mAsympLower τ)) ^ (8 * p) * τ⁻¹ ^ (16 * p)

/-- The constant of the recursion is at most `K_Z(p)`: for `1 ≤ n ≤ 2p`,
`(H/t + a₀t³) Γ^n (1/4)_n ≤ K_Z(p)` with `a₀ = 4^p`, `H = 2/c_as`, `t = τ⁻¹`, `Γ = 4a₀²H²t²`. -/
private theorem bounds_mobConst_le {p n : ℕ} {τ c : ℝ} (hp : 1 ≤ p) (hn : n ≤ 2 * p)
    (hc : 0 < c) (ht1 : 1 ≤ τ⁻¹) (hca : 0 < mAsympLower τ) (hca1 : mAsympLower τ ≤ 1) :
    (2 / mAsympLower τ / τ⁻¹ + 4 ^ p * τ⁻¹ ^ 3)
      * (4 * (4 ^ p) ^ 2 * (2 / mAsympLower τ) ^ 2 * τ⁻¹ ^ 2) ^ n * bndRise (1 / 4) n
      ≤ mobConst p τ c := by
  set t := τ⁻¹
  set a0 : ℝ := 4 ^ p
  set Hc := 2 / mAsympLower τ
  set Dc := mAsympUpper c τ + 1
  have ha0 : 4 ≤ a0 := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hHc : 1 ≤ Hc := by
    rw [le_div_iff₀ hca]
    linarith
  have hDc : 1 ≤ Dc := bounds_Cas hc
  set X := a0 * Dc * Hc
  have hX : 1 ≤ X := by
    have h1 : 1 ≤ a0 * Dc := by nlinarith
    nlinarith
  have hb : Hc / t + a0 * t ^ 3 ≤ (1 + t) * X * t ^ 3 := by
    have h1 : Hc / t ≤ X * t ^ 3 := by
      calc Hc / t ≤ Hc := div_le_self (by linarith) ht1
        _ ≤ X := by
            have : 1 ≤ a0 * Dc := by nlinarith
            calc Hc = 1 * Hc := (one_mul _).symm
              _ ≤ a0 * Dc * Hc := by gcongr
        _ ≤ X * t ^ 3 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ ht1)
    have h2 : a0 * t ^ 3 ≤ X * t ^ 3 := by
      gcongr
      calc a0 = a0 * 1 * 1 := by ring
        _ ≤ a0 * Dc * Hc := by gcongr
    have h3 : 0 ≤ X * t ^ 3 := by positivity
    nlinarith
  have hΓ : 4 * a0 ^ 2 * Hc ^ 2 * t ^ 2 ≤ X ^ 3 * t ^ 2 := by
    have : 4 * a0 ^ 2 * Hc ^ 2 ≤ X ^ 3 := by
      calc 4 * a0 ^ 2 * Hc ^ 2 ≤ a0 * a0 ^ 2 * Hc ^ 2 := by gcongr
        _ = a0 ^ 3 * 1 ^ 3 * Hc ^ 2 * 1 := by ring
        _ ≤ a0 ^ 3 * Dc ^ 3 * Hc ^ 2 * Hc := by gcongr
        _ = X ^ 3 := by ring
    gcongr
  have hX1 : 1 ≤ X ^ 3 * t ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) (one_le_pow₀ ht1)
  have hΓn : (4 * a0 ^ 2 * Hc ^ 2 * t ^ 2) ^ n ≤ X ^ (6 * p) * t ^ (4 * p) := by
    calc (4 * a0 ^ 2 * Hc ^ 2 * t ^ 2) ^ n ≤ (X ^ 3 * t ^ 2) ^ n :=
          pow_le_pow_left₀ (by positivity) hΓ n
      _ ≤ (X ^ 3 * t ^ 2) ^ (2 * p) := pow_le_pow_right₀ hX1 hn
      _ = X ^ (6 * p) * t ^ (4 * p) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          ring_nf
  have hp8 : (1 : ℝ) ≤ 8 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hr : bndRise (1 / 4) n ≤ (8 * p : ℝ) ^ (2 * p) := by
    calc bndRise (1 / 4) n ≤ (1 / 4 + n) ^ n := bndRise_le (by norm_num) n
      _ ≤ (8 * p : ℝ) ^ n := by
          refine pow_le_pow_left₀ (by positivity) ?_ n
          have : (n : ℝ) ≤ 2 * p := by exact_mod_cast hn
          have : (1 : ℝ) ≤ p := by exact_mod_cast hp
          linarith
      _ ≤ (8 * p : ℝ) ^ (2 * p) := pow_le_pow_right₀ hp8 hn
  have hr0 := bndRise_nonneg (a := 1 / 4) (by norm_num) n
  calc (Hc / t + a0 * t ^ 3) * (4 * a0 ^ 2 * Hc ^ 2 * t ^ 2) ^ n * bndRise (1 / 4) n
      ≤ ((1 + t) * X * t ^ 3) * (X ^ (6 * p) * t ^ (4 * p)) * (8 * p : ℝ) ^ (2 * p) := by
        gcongr
    _ = (1 + t) * (8 * p : ℝ) ^ (2 * p) * X ^ (6 * p + 1) * t ^ (4 * p + 3) := by ring
    _ ≤ (1 + t) * (8 * p : ℝ) ^ (2 * p) * X ^ (8 * p) * t ^ (16 * p) := by
        gcongr
        all_goals omega
    _ = mobConst p τ c := by unfold mobConst; rfl

/-- The hypotheses of `minor_bounds` give the hypotheses of the recursion (β) for
`S ↦ G^{(S)}`, with `L = 2p`, `a₀ = 4^p`, `H = 2/c_as`, `t = τ⁻¹`, and `δ = N^{ε₁}Υ ≤ 1`. -/
private theorem bounds_mob_Gm {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥ : 0 ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (n : ℕ) :
    (∀ (R W : Finset (Fin M ⊕ Fin N)) x y, R.card ≤ 2 * p → x ∉ R → y ∉ R → W ⊆ R →
      W.card = n → (x ≠ y ∨ 0 < n) → ‖mobPart (fun S => Gm (diagonal σ) Xm z S x y) R W‖
        ≤ 4 ^ p * sigS σ x * sigS σ y
          * (4 * (4 ^ p) ^ 2 * (2 / mAsympLower τ) ^ 2 * τ⁻¹ ^ 2) ^ n * bndRise (1 / 4) n
          * ((N : ℝ) ^ ε₁ * Υ) ^ (n + 1)) ∧
    (∀ (R W : Finset (Fin M ⊕ Fin N)) x, R.card ≤ 2 * p → x ∉ R → W ⊆ R → W.card = n →
      0 < n → ‖mobPart (fun S => (Gm (diagonal σ) Xm z S x x)⁻¹) R W‖
        ≤ 2 / mAsympLower τ / τ⁻¹
          * (4 * (4 ^ p) ^ 2 * (2 / mAsympLower τ) ^ 2 * τ⁻¹ ^ 2) ^ n * bndRise (1 / 4) n
          * ((N : ℝ) ^ ε₁ * Υ) ^ (n + 1)) := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  obtain ⟨hca, hca1⟩ := bounds_cas h
  obtain ⟨hδ0, hδL, hkey⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hu1 : (1 : ℝ) ≤ 4 ^ p := one_le_pow₀ (by norm_num)
  have hδ1 : (N : ℝ) ^ ε₁ * Υ ≤ 1 := by
    have hL1 : (N : ℝ) ^ (ε₁ - c₀) ≤ 1 := by
      have hL0 : 0 ≤ (N : ℝ) ^ (ε₁ - c₀) := hδ0.trans hδL
      have h1 : (N : ℝ) ^ (ε₁ - c₀) ≤ 4 ^ p * (N : ℝ) ^ (ε₁ - c₀) * τ⁻¹ := by
        calc (N : ℝ) ^ (ε₁ - c₀) = 1 * (N : ℝ) ^ (ε₁ - c₀) * 1 := by ring
          _ ≤ 4 ^ p * (N : ℝ) ^ (ε₁ - c₀) * τ⁻¹ := by gcongr
      linarith
    linarith
  have hHc : 1 ≤ 2 / mAsympLower τ := by
    rw [le_div_iff₀ hca]
    linarith
  refine bounds_mob_main (fun S => Gm (diagonal σ) Xm z S) (sigS σ) (2 * p)
    (fun S r s t hr hs ht => Gstu_minor hSig Xm hz.1 S r s t hr hs ht)
    (fun S r hr => Gm_diag_ne_zero hSig Xm hz.1 S r hr) ?_ ?_ (bounds_sigS_pos hσ)
    (bounds_sigS_le h) hu1 hHc ht1 hδ0 hδ1 n
  · intro S hS s t hs ht hst
    refine ((minor_bounds hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo S hS s t hs ht).1
      hst).trans ?_
    have h2 : (2 : ℝ) ^ S.card ≤ 4 ^ p := by
      calc (2 : ℝ) ^ S.card ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) hS
        _ = 4 ^ p := by rw [pow_mul]; norm_num
    have := bounds_sigS_pos (N := N) hσ s
    have := bounds_sigS_pos (N := N) hσ t
    gcongr
  · intro S hS t ht
    have hlow := (minor_bounds hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo S hS t t ht ht).2.1
    have hw := bounds_sigS_pos (N := N) hσ t
    have hpos : 0 < mAsympLower τ / 2 * sigS σ t := by positivity
    rw [norm_inv]
    calc ‖Gm (diagonal σ) Xm z S t t‖⁻¹ ≤ (mAsympLower τ / 2 * sigS σ t)⁻¹ :=
          inv_anti₀ hpos hlow
      _ = 2 / mAsympLower τ / sigS σ t := by field_simp

/-- (β): for `∅ ≠ U ⊆ T`, `μ ∉ T`, `|T| + 1 ≤ 2p`, under the hypotheses of `minor_bounds`:
`|Z^{[U]}_μ| ≤ K_Z(p) (N^{ε₁}Υ)^{|U|+1}`. -/
theorem ZmuMob_bound {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥ : 0 ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (T U : Finset (Fin N)) (hT : T.card + 1 ≤ 2 * p) (hU : U ⊆ T) (hUne : U.Nonempty)
    (μ : Fin N) (hμ : μ ∉ T) :
    ‖ZmuMob σ Xm z T U μ‖ ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  obtain ⟨hca, hca1⟩ := bounds_cas h
  obtain ⟨hδ0, -, -⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  have hN : (0 : ℝ) < N := by exact_mod_cast bounds_N_pos h
  have hmain := bounds_mob_Gm hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo U.card
  set δ := (N : ℝ) ^ ε₁ * Υ
  set n := U.card with hn
  set Γ := 4 * (4 ^ p : ℝ) ^ 2 * (2 / mAsympLower τ) ^ 2 * τ⁻¹ ^ 2
  have hn0 : 0 < n := Finset.card_pos.2 hUne
  have hnT : n ≤ T.card := Finset.card_le_card hU
  have hp : 1 ≤ p := by omega
  set e : Fin N ↪ Fin M ⊕ Fin N := Function.Embedding.inr
  set μ' : Fin M ⊕ Fin N := Sum.inr μ
  have hμ' : μ' ∉ T.map e := by simpa [e, μ'] using hμ
  have hUe : U.map e ⊆ T.map e := Finset.map_subset_map.2 hU
  have hμU : μ' ∉ U.map e := fun h' => hμ' (hUe h')
  -- the Schur form of `Z^{(S)}_μ` and the transport to `𝓘`
  have e1 : ZmuMob σ Xm z T U μ = mobPart (fun S => -(Gm (diagonal σ) Xm z S μ' μ')⁻¹ - z
      - (N : ℂ)⁻¹ * ∑ i, Gm (diagonal σ) Xm z (insert μ' S) (Sum.inl i) (Sum.inl i))
      (T.map e) (U.map e) := by
    unfold ZmuMob
    rw [← mobPart_map']
    refine mobPart_congr' fun V hV => ?_
    have hμV : μ ∉ T \ V := fun h' => hμ (Finset.mem_sdiff.1 h').1
    have hs := ZmuS_schur hσ Xm hz.1 (T \ V) μ hμV
    have hins : colSet (M := M) (insert μ (T \ V)) = insert μ' ((T \ V).map e) := by
      simp [colSet, e, μ', Finset.map_insert]
    rw [hins] at hs
    have hcol : colSet (M := M) (T \ V) = (T \ V).map e := rfl
    rw [hcol, one_div] at hs
    linear_combination hs
  rw [e1, bounds_mob_split (fun S => (Gm (diagonal σ) Xm z S μ' μ')⁻¹)
    (fun i S => Gm (diagonal σ) Xm z S (Sum.inl i) (Sum.inl i)) z (N : ℂ)⁻¹ μ' _ _
    (Finset.map_nonempty.2 hUne) hμU]
  have hcardT : (T.map e).card ≤ 2 * p := by rw [Finset.card_map]; omega
  have hcardT' : (insert μ' (T.map e)).card ≤ 2 * p := by
    rw [Finset.card_insert_of_notMem hμ', Finset.card_map]; omega
  have hUc : (U.map e).card = n := Finset.card_map _
  have hA := (hmain.2 (T.map e) (U.map e) μ' hcardT hμ' hUe hUc hn0)
  have hB : ∀ i : Fin M, ‖mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inl i) (Sum.inl i))
      (insert μ' (T.map e)) (U.map e)‖ ≤ 4 ^ p * τ⁻¹ ^ 2 * Γ ^ n * bndRise (1 / 4) n
        * δ ^ (n + 1) := by
    intro i
    have hi : (Sum.inl i : Fin M ⊕ Fin N) ∉ insert μ' (T.map e) := by simp [e, μ']
    refine (hmain.1 _ (U.map e) _ _ hcardT' hi hi (hUe.trans (Finset.subset_insert _ _)) hUc
      (Or.inr hn0)).trans ?_
    have hw := bounds_sigS_le h (Sum.inl i : Fin M ⊕ Fin N)
    have hw0 := bounds_sigS_pos (N := N) hσ (Sum.inl i)
    have : sigS σ (Sum.inl i : Fin M ⊕ Fin N) * sigS σ (Sum.inl i : Fin M ⊕ Fin N) ≤ τ⁻¹ ^ 2 := by
      rw [sq]; exact mul_le_mul hw hw hw0.le (by positivity)
    have := bndRise_nonneg (a := 1 / 4) (by norm_num) n
    calc 4 ^ p * sigS σ (Sum.inl i : Fin M ⊕ Fin N) * sigS σ (Sum.inl i : Fin M ⊕ Fin N)
          * Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1)
        = 4 ^ p * (sigS σ (Sum.inl i : Fin M ⊕ Fin N) * sigS σ (Sum.inl i : Fin M ⊕ Fin N))
          * Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1) := by ring
      _ ≤ 4 ^ p * τ⁻¹ ^ 2 * Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1) := by gcongr
  set Q := Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1)
  have hQ : 0 ≤ Q := by
    have := bndRise_nonneg (a := 1 / 4) (by norm_num) n
    positivity
  have hsum : ‖(N : ℂ)⁻¹ * ∑ i : Fin M, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inl i)
      (Sum.inl i)) (insert μ' (T.map e)) (U.map e)‖ ≤ 4 ^ p * τ⁻¹ ^ 3 * Q := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hB i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hM := bounds_M_le h
    calc (N : ℝ)⁻¹ * ‖∑ i : Fin M, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inl i)
          (Sum.inl i)) (insert μ' (T.map e)) (U.map e)‖
        ≤ (N : ℝ)⁻¹ * (M * (4 ^ p * τ⁻¹ ^ 2 * Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (N : ℝ)⁻¹ * (τ⁻¹ * N * (4 ^ p * τ⁻¹ ^ 2 * Q)) := by
          have hX0 : 0 ≤ 4 ^ p * τ⁻¹ ^ 2 * Q := mul_nonneg (by positivity) hQ
          have e : 4 ^ p * τ⁻¹ ^ 2 * Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1)
              = 4 ^ p * τ⁻¹ ^ 2 * Q := by simp only [Q]; ring
          rw [e]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hX0) (by positivity)
      _ = 4 ^ p * τ⁻¹ ^ 3 * Q := by field_simp
  calc ‖-mobPart (fun S => (Gm (diagonal σ) Xm z S μ' μ')⁻¹) (T.map e) (U.map e)
        - (N : ℂ)⁻¹ * ∑ i : Fin M, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inl i)
          (Sum.inl i)) (insert μ' (T.map e)) (U.map e)‖
      ≤ 2 / mAsympLower τ / τ⁻¹ * Q + 4 ^ p * τ⁻¹ ^ 3 * Q := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hsum)
        rw [norm_neg]
        refine hA.trans (le_of_eq ?_)
        simp only [Q]; ring
    _ = (2 / mAsympLower τ / τ⁻¹ + 4 ^ p * τ⁻¹ ^ 3) * Γ ^ n * bndRise (1 / 4) n
          * δ ^ (n + 1) := by simp only [Q]; ring
    _ ≤ mobConst p τ c * δ ^ (n + 1) := by
        gcongr
        exact bounds_mobConst_le hp (by omega) hc ht1 hca hca1

/-- (β) for row labels. -/
theorem ZiMob_bound {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥ : 0 ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (T U : Finset (Fin M)) (hT : T.card + 1 ≤ 2 * p) (hU : U ⊆ T) (hUne : U.Nonempty)
    (i : Fin M) (hi : i ∉ T) :
    ‖ZiMob σ Xm z T U i‖ ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  obtain ⟨hca, hca1⟩ := bounds_cas h
  obtain ⟨hδ0, -, -⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  have hN : (0 : ℝ) < N := by exact_mod_cast bounds_N_pos h
  have hmain := bounds_mob_Gm hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo U.card
  set δ := (N : ℝ) ^ ε₁ * Υ
  set n := U.card with hn
  set Γ := 4 * (4 ^ p : ℝ) ^ 2 * (2 / mAsympLower τ) ^ 2 * τ⁻¹ ^ 2
  have hn0 : 0 < n := Finset.card_pos.2 hUne
  have hnT : n ≤ T.card := Finset.card_le_card hU
  have hp : 1 ≤ p := by omega
  set e : Fin M ↪ Fin M ⊕ Fin N := Function.Embedding.inl
  set i' : Fin M ⊕ Fin N := Sum.inl i
  have hi' : i' ∉ T.map e := by simpa [e, i'] using hi
  have hUe : U.map e ⊆ T.map e := Finset.map_subset_map.2 hU
  have hiU : i' ∉ U.map e := fun h' => hi' (hUe h')
  -- the Schur form of `Z^{(S)}_i` and the transport to `𝓘`
  have e1 : ZiMob σ Xm z T U i = mobPart (fun S => -(Gm (diagonal σ) Xm z S i' i')⁻¹
      - 1 / (σ i : ℂ)
      - (N : ℂ)⁻¹ * ∑ ν, Gm (diagonal σ) Xm z (insert i' S) (Sum.inr ν) (Sum.inr ν))
      (T.map e) (U.map e) := by
    unfold ZiMob
    rw [← mobPart_map']
    refine mobPart_congr' fun V hV => ?_
    have hiV : i ∉ T \ V := fun h' => hi (Finset.mem_sdiff.1 h').1
    have hs := ZiS_schur hσ Xm hz.1 (T \ V) i hiV
    have hins : rowSet (N := N) (insert i (T \ V)) = insert i' ((T \ V).map e) := by
      simp [rowSet, e, i', Finset.map_insert]
    rw [hins] at hs
    have hrow : rowSet (N := N) (T \ V) = (T \ V).map e := rfl
    rw [hrow, one_div] at hs
    linear_combination hs
  rw [e1, bounds_mob_split (fun S => (Gm (diagonal σ) Xm z S i' i')⁻¹)
    (fun ν S => Gm (diagonal σ) Xm z S (Sum.inr ν) (Sum.inr ν)) (1 / (σ i : ℂ)) (N : ℂ)⁻¹ i' _ _
    (Finset.map_nonempty.2 hUne) hiU]
  have hcardT : (T.map e).card ≤ 2 * p := by rw [Finset.card_map]; omega
  have hcardT' : (insert i' (T.map e)).card ≤ 2 * p := by
    rw [Finset.card_insert_of_notMem hi', Finset.card_map]; omega
  have hUc : (U.map e).card = n := Finset.card_map _
  have hA := (hmain.2 (T.map e) (U.map e) i' hcardT hi' hUe hUc hn0)
  set Q := Γ ^ n * bndRise (1 / 4) n * δ ^ (n + 1)
  have hQ : 0 ≤ Q := by
    have := bndRise_nonneg (a := 1 / 4) (by norm_num) n
    positivity
  have hB : ∀ ν : Fin N, ‖mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inr ν) (Sum.inr ν))
      (insert i' (T.map e)) (U.map e)‖ ≤ 4 ^ p * Q := by
    intro ν
    have hν : (Sum.inr ν : Fin M ⊕ Fin N) ∉ insert i' (T.map e) := by simp [e, i']
    refine (hmain.1 _ (U.map e) _ _ hcardT' hν hν (hUe.trans (Finset.subset_insert _ _)) hUc
      (Or.inr hn0)).trans (le_of_eq ?_)
    simp only [Q, sigS, Sum.elim_inr]
    ring
  have hsum : ‖(N : ℂ)⁻¹ * ∑ ν : Fin N, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inr ν)
      (Sum.inr ν)) (insert i' (T.map e)) (U.map e)‖ ≤ 4 ^ p * τ⁻¹ ^ 3 * Q := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν (_ : ν ∈ Finset.univ) => hB ν)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc (N : ℝ)⁻¹ * ‖∑ ν : Fin N, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inr ν)
          (Sum.inr ν)) (insert i' (T.map e)) (U.map e)‖
        ≤ (N : ℝ)⁻¹ * (N * (4 ^ p * Q)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 ^ p * 1 * Q := by field_simp
      _ ≤ 4 ^ p * τ⁻¹ ^ 3 * Q := by
          gcongr
          exact one_le_pow₀ ht1
  calc ‖-mobPart (fun S => (Gm (diagonal σ) Xm z S i' i')⁻¹) (T.map e) (U.map e)
        - (N : ℂ)⁻¹ * ∑ ν : Fin N, mobPart (fun S => Gm (diagonal σ) Xm z S (Sum.inr ν)
          (Sum.inr ν)) (insert i' (T.map e)) (U.map e)‖
      ≤ 2 / mAsympLower τ / τ⁻¹ * Q + 4 ^ p * τ⁻¹ ^ 3 * Q := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hsum)
        rw [norm_neg]
        refine hA.trans (le_of_eq ?_)
        simp only [Q]; ring
    _ = (2 / mAsympLower τ / τ⁻¹ + 4 ^ p * τ⁻¹ ^ 3) * Γ ^ n * bndRise (1 / 4) n
          * δ ^ (n + 1) := by simp only [Q]; ring
    _ ≤ mobConst p τ c * δ ^ (n + 1) := by
        gcongr
        exact bounds_mobConst_le hp (by omega) hc ht1 hca hca1

/-! ## The LDE control parameters of `Z^{(S)}_s` ((E2) in the proof of Lemma 5.6) -/

/-- The LDE bound of `Z^{(S)}_μ`: `(Σ_{i≠j}|G^{(Sμ)}_{ij}|²)^{1/2}/N + (Σ_i|G^{(Sμ)}_{ii}|²)^{1/2}/N`. -/
def ldeZCol {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (S : Finset (Fin N)) (μ : Fin N) : ℝ :=
  ldeOffBound N (fun i j : Fin M =>
      Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl j)) +
    ldeDiagBound N (fun i : Fin M =>
      Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl i))

/-- The LDE bound of `Z^{(S)}_i`: `(Σ_{μ≠ν}|G^{(Si)}_{μν}|²)^{1/2}/N + (Σ_ν|G^{(Si)}_{νν}|²)^{1/2}/N`. -/
def ldeZRow {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (S : Finset (Fin M)) (i : Fin M) : ℝ :=
  ldeOffBound N (fun μ ν : Fin N =>
      Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr μ) (Sum.inr ν)) +
    ldeDiagBound N (fun ν : Fin N =>
      Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr ν) (Sum.inr ν))

/-- `K_L(p) = 2 · 4^p (C_as + 1) τ⁻³`. -/
def ldeZConst (p : ℕ) (τ c : ℝ) : ℝ := 2 * 4 ^ p * (mAsympUpper c τ + 1) * τ⁻¹ ^ 3

/-- `(Σ_{i≠j}|A_ij|²)^{1/2}/N ≤ |ι| K/N` when `|A_ij| ≤ K` for `i ≠ j`. -/
private theorem bounds_ldeOff_le {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (A : ι → ι → ℂ) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i j, i ≠ j → ‖A i j‖ ≤ K) :
    ldeOffBound N A ≤ Fintype.card ι * K / N := by
  unfold ldeOffBound
  gcongr
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * K) ^ 2 := by
    calc ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2
        ≤ ∑ _i : ι, ∑ _j : ι, K ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (Finset.sum_le_sum fun j hj => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
              fun _ _ _ => sq_nonneg K)
          exact pow_le_pow_left₀ (norm_nonneg _) (hA i j (Finset.ne_of_mem_erase hj).symm) 2
      _ = ((Fintype.card ι : ℝ) * K) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  calc Real.sqrt (∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2)
      ≤ Real.sqrt (((Fintype.card ι : ℝ) * K) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Fintype.card ι * K := Real.sqrt_sq (by positivity)

/-- `(Σ_i|a_i|²)^{1/2}/N ≤ |ι|^{1/2} K/N` when `|a_i| ≤ K`. -/
private theorem bounds_ldeDiag_le {ι : Type*} [Fintype ι] (N : ℕ) (a : ι → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    ldeDiagBound N a ≤ Real.sqrt (Fintype.card ι) * K / N := by
  unfold ldeDiagBound
  gcongr
  have h1 : ∑ i, ‖a i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * K ^ 2 := by
    calc ∑ i, ‖a i‖ ^ 2 ≤ ∑ _i : ι, K ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (ha i) 2
      _ = (Fintype.card ι : ℝ) * K ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖a i‖ ^ 2) ≤ Real.sqrt ((Fintype.card ι : ℝ) * K ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt (Fintype.card ι) * K := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

/-- `(√N)⁻¹ ≤ N^{ε₁} Υ` from `N^{-1/2} ≤ Υ`, `ε₁ ≥ 0`, `N ≥ 1`. -/
private theorem bounds_invsqrt_le {N : ℕ} {ε₁ Υ : ℝ} (hN : 0 < N) (hε₁ : 0 ≤ ε₁)
    (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ) : (Real.sqrt N)⁻¹ ≤ (N : ℝ) ^ ε₁ * Υ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e : (Real.sqrt N)⁻¹ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  have hΥ0 : 0 ≤ Υ := le_trans (by positivity) hΥN
  rw [e]
  calc (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ := hΥN
    _ = 1 * Υ := (one_mul _).symm
    _ ≤ (N : ℝ) ^ ε₁ * Υ := by gcongr; exact Real.one_le_rpow hN1 hε₁

/-- `a + b ≤ 2ab` for `a, b ≥ 1`. -/
private theorem bounds_add_le_two_mul {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a + b ≤ 2 * a * b := by
  nlinarith

/-- (γ): under the hypotheses of `minor_bounds` and `N^{-1/2} ≤ Υ`, for `|S| + 1 ≤ 2p`:
`ldeZ ≤ K_L(p) N^{ε₁} Υ`. -/
theorem ldeZCol_le {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ)
    (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (S : Finset (Fin N)) (hS : S.card + 1 ≤ 2 * p) (μ : Fin N) (hμ : μ ∉ S) :
    ldeZCol σ Xm z S μ ≤ ldeZConst p τ c * ((N : ℝ) ^ ε₁ * Υ) := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  have hNpos := bounds_N_pos h
  have hN : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΥ : 0 ≤ Υ := le_trans (by positivity) hΥN
  obtain ⟨hδ0, -, -⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  set δ := (N : ℝ) ^ ε₁ * Υ
  set R : Finset (Fin M ⊕ Fin N) := colSet (insert μ S)
  have hRc : R.card ≤ 2 * p := by
    simp only [R, colSet, Finset.card_map, Finset.card_insert_of_notMem hμ]; omega
  have hiR : ∀ i : Fin M, (Sum.inl i : Fin M ⊕ Fin N) ∉ R := by simp [R, colSet]
  have mb := fun s t hs ht => minor_bounds hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo R hRc
    s t hs ht
  have h2 : (2 : ℝ) ^ R.card ≤ 4 ^ p := by
    calc (2 : ℝ) ^ R.card ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) hRc
      _ = 4 ^ p := by rw [pow_mul]; norm_num
  set Dc := mAsympUpper c τ + 1
  have hDc : 1 ≤ Dc := bounds_Cas hc
  have hoff : ldeOffBound N (fun i j : Fin M =>
      Gm (diagonal σ) Xm z R (Sum.inl i) (Sum.inl j)) ≤ 4 ^ p * τ⁻¹ ^ 3 * δ := by
    refine (bounds_ldeOff_le N _ (K := 4 ^ p * τ⁻¹ ^ 2 * δ) (by positivity) fun i j hij => ?_).trans
      ?_
    · refine ((mb _ _ (hiR i) (hiR j)).1 (by simpa using hij)).trans ?_
      have hi := bounds_sigS_le h (Sum.inl i : Fin M ⊕ Fin N)
      have hj := bounds_sigS_le h (Sum.inl j : Fin M ⊕ Fin N)
      have hi0 := bounds_sigS_pos (N := N) hσ (Sum.inl i)
      have hj0 := bounds_sigS_pos (N := N) hσ (Sum.inl j)
      calc 2 ^ R.card * sigS σ (Sum.inl i : Fin M ⊕ Fin N) * sigS σ (Sum.inl j : Fin M ⊕ Fin N) * δ
          ≤ 4 ^ p * τ⁻¹ * τ⁻¹ * δ := by gcongr
        _ = 4 ^ p * τ⁻¹ ^ 2 * δ := by ring
    · rw [Fintype.card_fin]
      have hM := bounds_M_le h
      calc (M : ℝ) * (4 ^ p * τ⁻¹ ^ 2 * δ) / N ≤ τ⁻¹ * N * (4 ^ p * τ⁻¹ ^ 2 * δ) / N := by
            gcongr
        _ = 4 ^ p * τ⁻¹ ^ 3 * δ := by field_simp
  have hdiag : ldeDiagBound N (fun i : Fin M =>
      Gm (diagonal σ) Xm z R (Sum.inl i) (Sum.inl i)) ≤ Dc * τ⁻¹ ^ 3 * δ := by
    refine (bounds_ldeDiag_le N _ (K := Dc * τ⁻¹) (by positivity) fun i => ?_).trans ?_
    · refine (mb _ _ (hiR i) (hiR i)).2.2.trans ?_
      exact mul_le_mul_of_nonneg_left (bounds_sigS_le h _) (by positivity)
    · rw [Fintype.card_fin]
      have hM := bounds_M_le h
      have hsq : Real.sqrt M ≤ Real.sqrt τ⁻¹ * Real.sqrt N := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt hM
      have hst : Real.sqrt τ⁻¹ ≤ τ⁻¹ := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
      have hinv := bounds_invsqrt_le hNpos hε₁ hΥN
      calc Real.sqrt M * (Dc * τ⁻¹) / N ≤ Real.sqrt τ⁻¹ * Real.sqrt N * (Dc * τ⁻¹) / N := by
            gcongr
        _ = Real.sqrt τ⁻¹ * (Dc * τ⁻¹) * (Real.sqrt N / N) := by ring
        _ = Real.sqrt τ⁻¹ * (Dc * τ⁻¹) * (Real.sqrt N)⁻¹ := by rw [Real.sqrt_div_self]
        _ ≤ τ⁻¹ * (Dc * τ⁻¹) * δ := by gcongr
        _ ≤ Dc * τ⁻¹ ^ 3 * δ := by
            have : τ⁻¹ ^ 2 ≤ τ⁻¹ ^ 3 := pow_le_pow_right₀ ht1 (by norm_num)
            calc τ⁻¹ * (Dc * τ⁻¹) * δ = Dc * τ⁻¹ ^ 2 * δ := by ring
              _ ≤ Dc * τ⁻¹ ^ 3 * δ := by gcongr
  unfold ldeZCol
  calc _ ≤ 4 ^ p * τ⁻¹ ^ 3 * δ + Dc * τ⁻¹ ^ 3 * δ := add_le_add hoff hdiag
    _ = (4 ^ p + Dc) * τ⁻¹ ^ 3 * δ := by ring
    _ ≤ (2 * 4 ^ p * Dc) * τ⁻¹ ^ 3 * δ := by
        gcongr
        exact bounds_add_le_two_mul (one_le_pow₀ (by norm_num)) hDc
    _ = ldeZConst p τ c * δ := by unfold ldeZConst; ring

/-- (γ) for row labels. -/
theorem ldeZRow_le {τ c c₀ ε₁ Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ)
    (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀)) (hΛo : LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ)
    (S : Finset (Fin M)) (hS : S.card + 1 ≤ 2 * p) (i : Fin M) (hi : i ∉ S) :
    ldeZRow σ Xm z S i ≤ ldeZConst p τ c * ((N : ℝ) ^ ε₁ * Υ) := by
  have hτ := h.pos
  have ht1 := bounds_one_le_inv h
  have hNpos := bounds_N_pos h
  have hN : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΥ : 0 ≤ Υ := le_trans (by positivity) hΥN
  obtain ⟨hδ0, -, -⟩ := bounds_scale h hε₁c₀ hΥ hΥc₀ hG
  set δ := (N : ℝ) ^ ε₁ * Υ
  set R : Finset (Fin M ⊕ Fin N) := rowSet (insert i S)
  have hRc : R.card ≤ 2 * p := by
    simp only [R, rowSet, Finset.card_map, Finset.card_insert_of_notMem hi]; omega
  have hνR : ∀ ν : Fin N, (Sum.inr ν : Fin M ⊕ Fin N) ∉ R := by simp [R, rowSet]
  have mb := fun s t hs ht => minor_bounds hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo R hRc
    s t hs ht
  have h2 : (2 : ℝ) ^ R.card ≤ 4 ^ p := by
    calc (2 : ℝ) ^ R.card ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) hRc
      _ = 4 ^ p := by rw [pow_mul]; norm_num
  set Dc := mAsympUpper c τ + 1
  have hDc : 1 ≤ Dc := bounds_Cas hc
  have hoff : ldeOffBound N (fun μ ν : Fin N =>
      Gm (diagonal σ) Xm z R (Sum.inr μ) (Sum.inr ν)) ≤ 4 ^ p * δ := by
    refine (bounds_ldeOff_le N _ (K := 4 ^ p * δ) (by positivity) fun μ ν hμν => ?_).trans ?_
    · refine ((mb _ _ (hνR μ) (hνR ν)).1 (by simpa using hμν)).trans ?_
      simp only [sigS, Sum.elim_inr, mul_one]
      gcongr
    · rw [Fintype.card_fin]
      field_simp
      rfl
  have hdiag : ldeDiagBound N (fun ν : Fin N =>
      Gm (diagonal σ) Xm z R (Sum.inr ν) (Sum.inr ν)) ≤ Dc * δ := by
    refine (bounds_ldeDiag_le N _ (K := Dc) (by positivity) fun ν => ?_).trans ?_
    · refine (mb _ _ (hνR ν) (hνR ν)).2.2.trans (le_of_eq ?_)
      simp [sigS, Dc]
    · rw [Fintype.card_fin]
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
      have hinv := bounds_invsqrt_le hNpos hε₁ hΥN
      calc Real.sqrt N * Dc / N = Dc * (Real.sqrt N / N) := by ring
        _ = Dc * (Real.sqrt N)⁻¹ := by rw [Real.sqrt_div_self]
        _ ≤ Dc * δ := by gcongr
  unfold ldeZRow
  calc _ ≤ 4 ^ p * δ + Dc * δ := add_le_add hoff hdiag
    _ = (4 ^ p + Dc) * 1 * δ := by ring
    _ ≤ (2 * 4 ^ p * Dc) * τ⁻¹ ^ 3 * δ := by
        gcongr
        · exact bounds_add_le_two_mul (one_le_pow₀ (by norm_num)) hDc
        · exact one_le_pow₀ ht1
    _ = ldeZConst p τ c * δ := by unfold ldeZConst; ring

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` -/

section Checks

end Checks

end Anisotropic
