module

public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.Notation
public import Anisotropic.Comparison.Words
public import Anisotropic.Density.Basic
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Entrywise.Main
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.DominationUnion
public import Anisotropic.Framework.Model
public import Anisotropic.Gaussian.Invariance
public import Anisotropic.Gaussian.Main
public import Anisotropic.Gaussian.Measurable
public import Anisotropic.Gaussian.RotationLaw
public import Anisotropic.Gaussian.Spectral
public import Anisotropic.LinAlg.Basic
public import Anisotropic.LinAlg.Minor
public import Anisotropic.LinAlg.ResolventId
public import Anisotropic.Probability.NormBound.GaussianLower

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The averaged law with a control parameter `Φ`, (Phi_cond), the Gaussian input, the a priori input, `F̃` and its coefficients (§9) -/

/-- The averaged local law with parameters `(X, Σ, S, Φ)` (§9) at fixed `N, ε, D`:
`|m_N(z) − m(z)| ≺ Φ(z)` uniformly in `z ∈ S`. -/
def AveragedPhiLawAt {Ω : Type*} [MeasureSpace Ω] (N : ℕ) (ε D : ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ)
    (Φ : ℂ → ℝ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mN Sig (X ω) z - mFun N (specOf Sig) z) (fun _ => Φ z)

/-- (Phi_cond) on `S` with constant `c`: `c Ψ² ≤ Φ ≤ N^{−τ/2}`. -/
def PhiCond (τ c : ℝ) (N : ℕ) (σ : Fin M → ℝ) (S : Set ℂ) (Φ : ℂ → ℝ) : Prop :=
  ∀ z ∈ S, c * Psi N σ z ^ 2 ≤ Φ z ∧ Φ z ≤ (N : ℝ) ^ (-τ / 2)

/-- Definition 3.20 (iii) is the averaged law with `Φ = (Nη)⁻¹` (§9). -/
theorem averagedPhiLawAt_inv_iff {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ε D : ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} :
    AveragedPhiLawAt N ε D Sig X S (fun z => 1 / (N * z.im)) ↔ AveragedLawAt N ε D Sig X S :=
  Iff.rfl

/-- `C_m(τ) > 0` (Lemma 4.10 at `τ/2`). -/
theorem mBoundConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity

/-- The constant `c(τ) = 1/(2 C_m + 2)` of (Phi_cond) for `Φ = (Nη)⁻¹`. -/
def phiConst (τ : ℝ) : ℝ := 1 / (2 * mBoundConst τ + 2)

theorem phiConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < phiConst τ := by
  have := mBoundConst_pos hτ
  unfold phiConst
  positivity

/-- `Φ = (Nη)⁻¹` satisfies (Phi_cond) with `c = 1/(2 C_m + 2)` on every `S ⊆ 𝐃(τ, N)`. -/
theorem phiCond_inv {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {S : Set ℂ} (h : DensityAssumptions τ N σ)
    (hN : 1 ≤ N) (hS : S ⊆ specDomain τ N) :
    PhiCond τ (phiConst τ) N σ S (fun z => 1 / (N * z.im)) := by
  intro z hz
  have hzD := hS hz
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain h hzD
  obtain ⟨h0, -, -, hη, -⟩ := hzD
  have hC : 0 < mBoundConst τ := mBoundConst_pos h.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha0 : 0 ≤ (mFun N σ z).im := le_trans (by positivity) hm3
  have haC : (mFun N σ z).im ≤ mBoundConst τ := le_trans (Complex.im_le_norm _) hm2
  have hNη : (N : ℝ) ^ τ ≤ N * z.im := by
    have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one]
      field_simp
    calc (N : ℝ) ^ τ = N * (N : ℝ) ^ (-1 + τ) := e.symm
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left hη hN0.le
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1 h.pos.le
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  have hb0 : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  have hb1 : 1 / ((N : ℝ) * z.im) ≤ 1 := by rw [div_le_one hpos]; linarith
  refine ⟨?_, ?_⟩
  · have hsq : (√((mFun N σ z).im / (N * z.im))) ^ 2 =
        (mFun N σ z).im * (1 / ((N : ℝ) * z.im)) := by
      rw [Real.sq_sqrt (by positivity)]
      ring
    have hP : Psi N σ z ^ 2 ≤ (2 * mBoundConst τ + 2) * (1 / ((N : ℝ) * z.im)) := by
      have e : Psi N σ z = √((mFun N σ z).im / (N * z.im)) + 1 / (N * z.im) := rfl
      rw [e]
      set x := √((mFun N σ z).im / (N * z.im))
      set b := 1 / ((N : ℝ) * z.im)
      have h2 : (x + b) ^ 2 ≤ 2 * x ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (x - b)]
      have h3 : b ^ 2 ≤ b := by nlinarith
      have h4 : x ^ 2 ≤ mBoundConst τ * b := by
        rw [hsq]
        exact mul_le_mul_of_nonneg_right haC hb0.le
      nlinarith
    have hc2 : 0 < 2 * mBoundConst τ + 2 := by linarith
    calc phiConst τ * Psi N σ z ^ 2
        ≤ phiConst τ * ((2 * mBoundConst τ + 2) * (1 / ((N : ℝ) * z.im))) :=
          mul_le_mul_of_nonneg_left hP (phiConst_pos h.pos).le
      _ = 1 / ((N : ℝ) * z.im) := by
          unfold phiConst
          field_simp
  · have e1 : 1 / ((N : ℝ) * z.im) ≤ 1 / (N : ℝ) ^ τ :=
      one_div_le_one_div_of_le (by positivity) hNη
    have e2 : 1 / (N : ℝ) ^ τ = (N : ℝ) ^ (-τ) := by
      rw [Real.rpow_neg hN0.le, one_div]
    have e3 : (N : ℝ) ^ (-τ) ≤ (N : ℝ) ^ (-τ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.pos])
    calc 1 / ((N : ℝ) * z.im) ≤ 1 / (N : ℝ) ^ τ := e1
      _ = (N : ℝ) ^ (-τ) := e2
      _ ≤ (N : ℝ) ^ (-τ / 2) := e3

/-- Proposition 6.1 (ii) with a control parameter: for Gaussian `X` and symmetric `Σ`, the
averaged law with parameters `(X, D(Σ), S, Φ)` gives the averaged law with parameters
`(X, Σ, S, Φ)` at the same `(ε, D)`, for every deterministic `Φ`. -/
theorem gauss_averaged' {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {ε D : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : IsGaussianEnsemble X) {S : Set ℂ} {Φ : ℂ → ℝ}
    (h : AveragedPhiLawAt N ε D (diagonal (specOf Sig)) X S Φ) :
    AveragedPhiLawAt N ε D Sig X S Φ := by
  obtain ⟨U, hU, hUD⟩ := exists_orth_diag hSig
  have hUT : Uᵀ ∈ Matrix.orthogonalGroup (Fin M) ℝ :=
    (Matrix.mem_orthogonalGroup_iff _ _).2 (by
      rw [transpose_transpose]
      exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hU)
  have hON : (1 : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.orthogonalGroup (Fin N) ℝ := one_mem _
  intro z hz
  have h1 := h z hz
  unfold ODomAt at h1 ⊢
  rw [specOf_diagonal_specOf] at h1
  have hξ : Measurable fun A : Matrix (Fin M) (Fin N) ℝ =>
      ‖mN (diagonal (specOf Sig)) A z - mFun N (specOf Sig) z‖ :=
    ((measurable_mN _ z).sub_const _).norm
  have h2 := hX.domAt_rotate hUT hON
    (ξ := fun A => ‖mN (diagonal (specOf Sig)) A z - mFun N (specOf Sig) z‖)
    (ζ := fun _ => Φ z) hξ measurable_const h1
  have e : ∀ A : Matrix (Fin M) (Fin N) ℝ,
      mN (diagonal (specOf Sig)) (Uᵀ * A * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ) z = mN Sig A z := by
    intro A
    have := mN_rotate hUT hON Sig A z
    rwa [transpose_transpose, hUD] at this
  simp only [e] at h2
  exact h2

/-- Theorem 3.22 for `(X^Gauss, D(Σ))`: under (1+xm) and stability on `S`, the entrywise law and
the averaged law with `Φ = (Nη)⁻¹` hold with parameters `(X^Gauss, D(Σ), S)`. -/
theorem gauss_avg_input (τ c C₀ C₁ K₀ ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      IsModel τ gaussMoment M N Sig (gaussX M N) → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S → StableOn C₀ C₁ K₀ N (specOf Sig) S →
      EntrywiseLawAt N ε D (diagonal (specOf Sig)) (gaussX M N) S ∧
        AveragedPhiLawAt N ε D (diagonal (specOf Sig)) (gaussX M N) S
          (fun z => 1 / (N * z.im)) := by
  obtain ⟨N₀, h⟩ := diag_gen τ c C₀ C₁ K₀ gaussMoment ε D hτ hc hε
  exact ⟨N₀, fun N hN M Sig S hm hS hx hst =>
    h N hN M (specOf Sig) (gaussX M N) S hm.diagModel_specOf hS hx hst⟩

/-- `IsModel` forces `τ ≤ 1`. -/
theorem IsModel.tau_le_one {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {M N : ℕ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) : τ ≤ 1 := by
  by_contra h
  replace h := lt_of_not_ge h
  have h1 := hm.ratio_ge
  have h2 := hm.ratio_le
  have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
  linarith

/-- The anisotropic law at `(ε, D)` on `S` for every model with moment function `C` and the
deterministic data `(M, N, Σ)`: the a priori input of the proof of Proposition 9.1. -/
def AnisoAllAt (N : ℕ) (C : ℕ → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (ε D : ℝ) :
    Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → AnisotropicLawAt N ε D Sig X S

/-- `F̃ = |m_N − m|` (§9). -/
def Ft (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ‖mN Sig A z - mFun N (specOf Sig) z‖

/-- The coefficient of `t^k` in `m_N − m` along the entry `(i, μ)`:
`N⁻¹ ∑_ν a_k(e_ν)`, `a_k` the resolvent coefficients of (def_Fp) at `v = e_ν`. -/
def avgCoeff (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M)
    (μ : Fin N) (k : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ k

/-- The same with `ν = μ` removed (`Â` of §9). -/
def avgCoeffHat (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (k : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, resCoeff Sig A z (eI (Sum.inr ν)) i μ k

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem avgDefs_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
    vbar Sig (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) = eI (Sum.inr ν) := by
  funext s
  rcases s with i | j
  · have h0 : ((eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl) = 0 := by
      funext k
      simp [eI]
    simp only [vbar, Sum.elim_inl]
    rw [h0, mulVec_zero]
    simp [eI]
  · simp [vbar]

/-- The constant coefficient of `m_N − m` is `m_N − m`. -/
theorem avgCoeff_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (hN : 1 ≤ N) :
    avgCoeff Sig A z i μ 0 = mN Sig A z - mFun N (specOf Sig) z := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : ∀ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ 0 =
      G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z := by
    intro ν
    simp only [resCoeff, pow_zero, one_mul, mul_one]
    rw [avgDefs_vbar_inr, ent_eI_eI]
    simp [PiZ, piMat]
  unfold avgCoeff mN
  simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- `f_0 = F̃^p` for `p` even. -/
theorem fCoeff_avgCoeff_zero {p : ℕ} (hp : Even p) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (hN : 1 ≤ N) :
    fCoeff p (avgCoeff Sig A z i μ) 0 = (Ft Sig A z : ℂ) ^ p := by
  rw [fCoeff_zero hp, avgCoeff_zero Sig A z i μ hN]
  rfl

/-- (Gstu) for the a priori bounds of `G^{(μ)}`: `|G_{st} − Π_{st}| ≤ b ≤ 1` and
`|G_μμ| ≥ L⁻¹` give `|G^{(μ)}_{st} − Π_{st}| ≤ (1 + L) b` for `s, t ≠ μ`. -/
theorem minor_entry_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {b L : ℝ} (hb : 0 ≤ b)
    (hb1 : b ≤ 1) (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) :
    ∀ s t, s ≠ Sum.inr μ → t ≠ Sum.inr μ →
      ‖G1 Sig A z (Sum.inr μ) s t - PiZ N Sig z s t‖ ≤ (1 + L) * b := by
  intro s t hs ht
  have hPi : ∀ u, u ≠ Sum.inr μ →
      PiZ N Sig z u (Sum.inr μ) = 0 ∧ PiZ N Sig z (Sum.inr μ) u = 0 := by
    intro u hu
    rcases u with k | ν
    · simp [PiZ, piMat]
    · have hν : ν ≠ μ := fun h => hu (by rw [h])
      simp [PiZ, piMat, hν, Ne.symm hν]
  have hs' : ‖G Sig A z s (Sum.inr μ)‖ ≤ b := by
    simpa [(hPi s hs).1] using hG s (Sum.inr μ)
  have ht' : ‖G Sig A z (Sum.inr μ) t‖ ≤ b := by
    simpa [(hPi t ht).2] using hG (Sum.inr μ) t
  have hrr : G Sig A z (Sum.inr μ) (Sum.inr μ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hμ
    linarith
  have hnr : 0 < ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := norm_pos_iff.2 hrr
  have hcorr : ‖G Sig A z s (Sum.inr μ) * G Sig A z (Sum.inr μ) t /
      G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ L * b := by
    rw [norm_div, norm_mul, div_le_iff₀ hnr]
    have h1 : ‖G Sig A z s (Sum.inr μ)‖ * ‖G Sig A z (Sum.inr μ) t‖ ≤ b * b :=
      mul_le_mul hs' ht' (norm_nonneg _) hb
    nlinarith
  rw [Gstu hSig A hz (Sum.inr μ) s t hs ht]
  calc ‖G Sig A z s t - G Sig A z s (Sum.inr μ) * G Sig A z (Sum.inr μ) t /
        G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z s t‖
      = ‖(G Sig A z s t - PiZ N Sig z s t) - G Sig A z s (Sum.inr μ) * G Sig A z (Sum.inr μ) t /
        G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := by ring_nf
    _ ≤ b + L * b := (norm_sub_le _ _).trans (add_le_add (hG s t) hcorr)
    _ = (1 + L) * b := by ring

/-- `|Uᵀ x| = |x|` for `U Uᵀ = 1`. -/
private theorem avgDefs_sum_sq_orth {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem avgDefs_sum_sq_Sig_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ i, (Sig *ᵥ x) i ^ 2 ≤ τ⁻¹ ^ 2 * ∑ i, x i ^ 2 := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hS.posDef.1
  have h₁ : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h₂ : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  have hSd : U * diagonal (specOf Sig) * Uᵀ = Sig := by
    rw [← hD]
    simp only [← Matrix.mul_assoc, h₂, Matrix.one_mul]
    rw [Matrix.mul_assoc, h₂, Matrix.mul_one]
  have hle : ∀ i, specOf Sig i ^ 2 ≤ τ⁻¹ ^ 2 := fun i => by
    rw [specOf_eq hS.posDef.isHermitian]
    exact pow_le_pow_left₀ (hS.posDef.eigenvalues_pos i).le (hS.eigenvalues_le i) 2
  have e1 : Sig *ᵥ x = U *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    conv_lhs => rw [← hSd]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  have e2 : ∀ w : Fin M → ℝ, ∑ i, (U *ᵥ w) i ^ 2 = ∑ i, w i ^ 2 := by
    intro w
    have := avgDefs_sum_sq_orth (U := Uᵀ) (by rw [transpose_transpose]; exact h₁) w
    rwa [transpose_transpose] at this
  rw [e1, e2, ← avgDefs_sum_sq_orth h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)

/-- The test vector `Σ̲ e_s`. -/
private def avgDefs_vec (Sig : Matrix (Fin M) (Fin M) ℝ) (s : Fin M ⊕ Fin N) :
    Fin M ⊕ Fin N → ℝ :=
  Sum.elim (Sig *ᵥ ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl)) ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inr)

/-- `Σ̲⁻¹ Σ̲ e_s = e_s`. -/
private theorem avgDefs_vbar_vec {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (s : Fin M ⊕ Fin N) : vbar Sig (avgDefs_vec Sig s) = eI s := by
  have hI : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext r
  rcases r with i | j
  · simp [vbar, avgDefs_vec, mulVec_mulVec, hI]
  · simp [vbar, avgDefs_vec]

/-- `|Σ̲ e_s| ≤ τ⁻¹` under (bound_Sigma) and `τ ≤ 1`. -/
private theorem avgDefs_testNorm_vec {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (s : Fin M ⊕ Fin N) :
    testNorm (avgDefs_vec Sig s) ≤ τ⁻¹ := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hτ2 : 1 ≤ τ⁻¹ ^ 2 := one_le_pow₀ hτi
  have h1 := avgDefs_sum_sq_Sig_le hS ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl)
  have h0 : ∑ i, ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl) i ^ 2 +
      ∑ j, ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inr) j ^ 2 = 1 := by
    have := Fintype.sum_sum_type (fun r => (eI s : Fin M ⊕ Fin N → ℝ) r ^ 2)
    simp only [Function.comp_apply]
    rw [← this]
    simp [eI, Pi.single_apply]
  have hy : 0 ≤ ∑ j, ((eI s : Fin M ⊕ Fin N → ℝ) ∘ Sum.inr) j ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold testNorm
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [avgDefs_vec, Sum.elim_inl, Sum.elim_inr]
  nlinarith [mul_nonneg (sub_nonneg.2 hτ2) hy]

/-- The a priori event of §9: the anisotropic law at `(εa, Da)` gives, with probability
`≥ 1 − N^{−(Da − 3)}`, `|G_{st} − Π_{st}| ≤ τ⁻² N^{εa} Ψ` for all `s, t`. -/
theorem avg_entry_highProb (τ c : ℝ) (εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting τ c M N Sig S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), AnisotropicLawAt N εa Da Sig X S →
        ∀ z ∈ S, HighProbAt N (Da - 3) {ω | ∀ s t,
          ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤
            τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z} := by
  refine ⟨⌈(τ⁻¹ + 1) ^ 2⌉₊, fun N hN M Sig S hcs Ω _ _ X hX z hz => ?_⟩
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hN' : ((τ⁻¹ + 1) ^ 2 : ℝ) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN4 : (4 : ℝ) ≤ N := by nlinarith
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hN0 : (0 : ℝ) < N := by linarith
  have hzim : 0 < z.im := (hcs.domain.1 hz).1
  have hSig := hcs.sigma.posDef
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hN0).1 hcs.ratio_le
  have hcard : ((Finset.univ : Finset ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N))).card : ℝ) ≤
      (N : ℝ) ^ (3 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    have hMN : (M : ℝ) + N ≤ (τ⁻¹ + 1) * N := by linarith
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc ((M : ℝ) + N) * (M + N) ≤ ((τ⁻¹ + 1) * N) * ((τ⁻¹ + 1) * N) :=
          mul_le_mul hMN hMN (by positivity) (by positivity)
      _ = (τ⁻¹ + 1) ^ 2 * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hN' (by positivity)
      _ = N ^ 3 := by ring
  have hPsi : 0 ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 < (N : ℝ) * z.im := by positivity
    positivity
  have hset : {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤
      τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z} =
      ⋂ p ∈ (Finset.univ : Finset ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N))),
        {ω | ‖G Sig (X ω) z p.1 p.2 - PiZ N Sig z p.1 p.2‖ ≤
          τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z} := by
    ext ω
    simp [Prod.forall]
  rw [hset]
  refine HighProbAt.biInter Finset.univ hN1 hcard fun p _ => ?_
  rw [show Da - 3 + 3 = Da by ring]
  have hlaw := hX z hz (avgDefs_vec Sig p.1) (avgDefs_vec Sig p.2)
  unfold DomAt at hlaw
  unfold HighProbAt
  refine le_trans (measure_mono ?_) hlaw
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
  have hv := avgDefs_testNorm_vec hcs.sigma hτ hτ1 p.1 (N := N)
  have hw := avgDefs_testNorm_vec hcs.sigma hτ hτ1 p.2 (N := N)
  have hv0 : 0 ≤ testNorm (avgDefs_vec Sig p.1) := Real.sqrt_nonneg _
  have hw0 : 0 ≤ testNorm (avgDefs_vec Sig p.2) := Real.sqrt_nonneg _
  have hNe : 0 < (N : ℝ) ^ εa := Real.rpow_pos_of_pos hN0 _
  rw [← ent_vbar_eq_testBilin hSig, avgDefs_vbar_vec hSig, avgDefs_vbar_vec hSig, ent_eI_eI]
  calc (N : ℝ) ^ εa * (Psi N (specOf Sig) z * testNorm (avgDefs_vec Sig p.1) *
        testNorm (avgDefs_vec Sig p.2))
      ≤ (N : ℝ) ^ εa * (Psi N (specOf Sig) z * τ⁻¹ * τ⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hNe.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv hPsi) hw hw0 (by positivity)
    _ = τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z := by ring
    _ < _ := hω

/-- Assumption 2.1 at `τ` gives Assumption 2.1 at every `τ₂ ∈ (0, τ]`. -/
theorem IsModel.mono {Ω : Type*} [MeasureSpace Ω] {τ τ₂ : ℝ} {C : ℕ → ℝ} {M N : ℕ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) (h₀ : 0 < τ₂) (h₂ : τ₂ ≤ τ) : IsModel τ₂ C M N Sig X := by
  obtain ⟨r1, r2, he, hs⟩ := hm
  have hinv : τ⁻¹ ≤ τ₂⁻¹ := inv_anti₀ h₀ h₂
  refine ⟨h₂.trans r1, r2.trans hinv, he,
    ⟨hs.posDef, fun i => (hs.eigenvalues_le i).trans hinv, ?_⟩⟩
  have hsub : {i | hs.posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ₂} ⊆
      {i | hs.posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ} := fun i hi => ⟨hi.1, hi.2.trans h₂⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hg := hs.gap
  calc (({i | hs.posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ₂}.ncard : ℕ) : ℝ)
      ≤ ({i | hs.posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ}.ncard : ℝ) := by
        exact_mod_cast hc
    _ ≤ (1 - τ) * M := hg
    _ ≤ (1 - τ₂) * M := by nlinarith

/-- `averagedPhiLawAt_inv_iff` on the concrete Gaussian ensemble. -/
example (ε D : ℝ) (S : Set ℂ) :
    AveragedPhiLawAt 2 ε D (1 : Matrix (Fin 1) (Fin 1) ℝ) (gaussX 1 2) S
      (fun z => 1 / ((2 : ℕ) * z.im)) ↔
      AveragedLawAt 2 ε D (1 : Matrix (Fin 1) (Fin 1) ℝ) (gaussX 1 2) S :=
  averagedPhiLawAt_inv_iff

/-- `C_m(1/20) > 0`. -/
example : 0 < mBoundConst (1 / 20) := mBoundConst_pos (by norm_num)

/-- `c(1/20) > 0`. -/
example : 0 < phiConst (1 / 20) := phiConst_pos (by norm_num)

/-- `gauss_averaged'` on the Gaussian ensemble with `M = 1`, `N = 2`, `Σ = 1`, `S = {i}`,
`Φ = (Nη)⁻¹`; the Hermitian and Gaussian hypotheses are discharged, the averaged law for `D(Σ)`
stays a hypothesis (conditional example). -/
example (ε D : ℝ)
    (h : AveragedPhiLawAt 2 ε D (diagonal (specOf (1 : Matrix (Fin 1) (Fin 1) ℝ))) (gaussX 1 2)
      {Complex.I} (fun z => 1 / ((2 : ℕ) * z.im))) :
    AveragedPhiLawAt 2 ε D (1 : Matrix (Fin 1) (Fin 1) ℝ) (gaussX 1 2) {Complex.I}
      (fun z => 1 / ((2 : ℕ) * z.im)) :=
  gauss_averaged' Matrix.isHermitian_one (gaussX_isGaussianEnsemble 1 2) h

/-- `gauss_avg_input` at `τ = 1/20`, `c = 1/100`, `C₀ = C₁ = K₀ = ε = D = 1` (an `∃ N₀`
statement; its model, domain, (1+xm) and stability hypotheses stay hypotheses). -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      IsModel (1 / 20) gaussMoment M N Sig (gaussX M N) → SpectralDomain (1 / 20) N S →
      OneXmOn (1 / 100) N (specOf Sig) S → StableOn 1 1 1 N (specOf Sig) S →
      EntrywiseLawAt N 1 1 (diagonal (specOf Sig)) (gaussX M N) S ∧
        AveragedPhiLawAt N 1 1 (diagonal (specOf Sig)) (gaussX M N) S
          (fun z => 1 / (N * z.im)) :=
  gauss_avg_input (1 / 20) (1 / 100) 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- `avgCoeff_zero` at `M = 1`, `N = 2`, `Σ = 1`, `X = (1 0)`, `z = i`. -/
example : avgCoeff (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 0] Complex.I 0 0 0 =
    mN (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 0] Complex.I -
      mFun 2 (specOf (1 : Matrix (Fin 1) (Fin 1) ℝ)) Complex.I :=
  avgCoeff_zero _ _ _ _ _ (by norm_num)

/-- `fCoeff_avgCoeff_zero` at `p = 2` and the same data. -/
example : fCoeff 2 (avgCoeff (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 0] Complex.I 0 0) 0 =
    (Ft (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 0] Complex.I : ℂ) ^ 2 :=
  fCoeff_avgCoeff_zero ⟨1, rfl⟩ _ _ _ _ _ (by norm_num)

/-- `avg_entry_highProb` at `τ = 1/20`, `c = 1/100`, `εa = 1/400`, `Da = 10` (an `∃ N₀`
statement; the setting and the anisotropic law stay hypotheses). -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting (1 / 20) (1 / 100) M N Sig S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), AnisotropicLawAt N (1 / 400) 10 Sig X S →
        ∀ z ∈ S, HighProbAt N (10 - 3) {ω | ∀ s t,
          ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤
            (1 / 20 : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (1 / 400 : ℝ) * Psi N (specOf Sig) z} :=
  avg_entry_highProb (1 / 20) (1 / 100) (1 / 400) 10 (by norm_num) (by norm_num) (by norm_num)

end Anisotropic
