module

public import Anisotropic.Comparison.Notation
public import Anisotropic.LinAlg.Expansion
public import Anisotropic.LinAlg.OpBound

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical
set_option linter.unusedSectionVars false

namespace Anisotropic

variable {M N : ℕ}

/-! # Words, resolvent coefficients, the coefficients of `F_v^p` (Definition 7.19, Lemma 7.15's algebra) -/

/-- Definition 7.19: `𝒲_n ≅ Bool^n`; `w l = true` iff the `l`-th pair `t_l s_{l+1}` is `𝐢𝛍`. -/
abbrev Word (n : ℕ) : Type := Fin n → Bool

/-- The value `[t_l]` of the first letter of a pair. -/
def letterT (i : Fin M) (μ : Fin N) (b : Bool) : Fin M ⊕ Fin N := if b then Sum.inl i else Sum.inr μ

/-- The value `[s_{l+1}]` of the second letter of a pair. -/
def letterS (i : Fin M) (μ : Fin N) (b : Bool) : Fin M ⊕ Fin N := if b then Sum.inr μ else Sum.inl i

/-- (def_w_1): `A_{v,i,μ}(w)`; `A(∅) = G_{v̄v̄} − Π_{v̄v̄}`. -/
def wordA (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) : (n : ℕ) → Word n → ℂ
  | 0, _ => ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)
  | k + 1, w => ent (G Sig A z) (vbar Sig v) (eI (letterT i μ (w 0))) *
      (∏ l : Fin k, G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))) *
      ent (G Sig A z) (eI (letterS i μ (w (Fin.last k)))) (vbar Sig v)

/-- `a_k = (−1)^k (G (Δ¹ G)^k − δ_{k0} Π)_{v̄v̄}`: the coefficient of `t^k` in
`(G − Π)_{v̄v̄}` along the entry `(i, μ)` at the base matrix `A`. -/
def resCoeff (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) : ℂ :=
  (-1) ^ k * ent (G Sig A z * (Delta i μ 1 * G Sig A z) ^ k - if k = 0 then PiZ N Sig z else 0)
    (vbar Sig v) (vbar Sig v)

/-- `f_n`: the coefficient of `t^n` in `∏_{r < p/2} a(t) ∏_{r ≥ p/2} \bar a(t)`, where
`a(t) = ∑_k a_k t^k`; for `f = F_v^p`, `f^{(n)} = n! f_n`. -/
def fCoeff (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple p n,
    ∏ r : Fin p, if (r : ℕ) < p / 2 then a (k r) else starRingEnd ℂ (a (k r))

/-! ### Bilinear forms and the two-term structure of `Δ¹` -/

section Helpers

variable {ι : Type*} [Fintype ι]

private theorem words_ent_eq (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem words_ent_eI_right [DecidableEq ι] (B : Matrix ι ι ℂ) (x : ι → ℝ) (r : ι) :
    ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [words_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem words_ent_eI_left [DecidableEq ι] (B : Matrix ι ι ℂ) (y : ι → ℝ) (r : ι) :
    ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [words_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem words_ent_smul (c : ℂ) (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent (c • B) x y = c * ent B x y := by
  simp [ent, smul_mulVec, dotProduct_smul]

end Helpers

private theorem words_Delta_smul (i : Fin M) (μ : Fin N) (c : ℝ) :
    Delta i μ c = (c : ℂ) • Delta i μ 1 := by
  ext s t
  simp only [Delta, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `(B Δ¹ C)_{st} = B_{s i} C_{μ t} + B_{s μ} C_{i t}`. -/
private theorem words_mul_Delta_mul (B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    (B * Delta i μ 1 * C) s t = B s (Sum.inl i) * C (Sum.inr μ) t +
      B s (Sum.inr μ) * C (Sum.inl i) t := by
  have hBD : ∀ r, (B * Delta i μ 1) s r =
      (if r = Sum.inr μ then B s (Sum.inl i) else 0) +
        (if r = Sum.inl i then B s (Sum.inr μ) else 0) := by
    intro r
    rw [Matrix.mul_apply]
    rcases r with j | ν
    · by_cases hj : j = i <;> simp [Delta, hj]
    · by_cases hν : ν = μ <;> simp [Delta, hν]
  rw [Matrix.mul_apply]
  simp only [hBD, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `⟨x, B Δ¹ C y⟩ = ∑_b ⟨x, B e_{[t]}⟩ ⟨e_{[s]}, C y⟩` over the two pairs `𝐢𝛍`, `𝛍𝐢`. -/
private theorem words_ent_mul_Delta_mul (B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (B * Delta i μ 1 * C) x y =
      ∑ b : Bool, ent B x (eI (letterT i μ b)) * ent C (eI (letterS i μ b)) y := by
  simp only [Fintype.sum_bool, letterT, letterS, ite_true, Bool.false_eq_true, ite_false]
  rw [words_ent_eq, words_ent_eI_right, words_ent_eI_left, words_ent_eI_right, words_ent_eI_left]
  simp only [words_mul_Delta_mul, mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-- Expansion of `⟨x, B (Δ¹ B)^{k+1} y⟩` over the words of length `k + 1`. -/
private theorem words_expand (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (k : ℕ) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (B * (Delta i μ 1 * B) ^ (k + 1)) x y =
      ∑ w : Word (k + 1), ent B x (eI (letterT i μ (w 0))) *
        (∏ l : Fin k, B (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))) *
        ent B (eI (letterS i μ (w (Fin.last k)))) y := by
  induction k generalizing x with
  | zero =>
    change ent (B * (Delta i μ 1 * B) ^ 1) x y = _
    rw [pow_one, ← Matrix.mul_assoc, words_ent_mul_Delta_mul,
      ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    simp
  | succ k ih =>
    rw [pow_succ', show B * (Delta i μ 1 * B * (Delta i μ 1 * B) ^ (k + 1)) =
      B * Delta i μ 1 * (B * (Delta i μ 1 * B) ^ (k + 1)) by simp only [Matrix.mul_assoc],
      words_ent_mul_Delta_mul]
    simp_rw [ih]
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Finset.mul_sum, Fin.prod_univ_succ, ← Fin.succ_last]
    simp only [ent_eI_eI, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Fin.cons_one]
    simp [mul_assoc]

/-! ### The word identity and the finite expansion -/

/-- The word identity: `a_k = (−1)^k ∑_{w ∈ 𝒲_k} A_{v,i,μ}(w)` (the `λ^k` coefficient). -/
theorem resCoeff_eq_sum_wordA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (k : ℕ) :
    resCoeff Sig A z v i μ k = (-1) ^ k * ∑ w : Word k, wordA Sig A z v i μ k w := by
  cases k with
  | zero => simp [resCoeff, wordA]
  | succ k =>
    simp only [resCoeff, Nat.succ_ne_zero, ↓reduceIte, sub_zero, words_expand]
    rfl

/-! ### Derivatives along the entry `(i, μ)` -/

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def WordsMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private theorem words_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : WordsMD f f' x) (hg : WordsMD g g' x) :
    WordsMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private theorem words_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    WordsMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

private theorem words_MD_ent {ι : Type*} [Fintype ι] {f : ℝ → Matrix ι ι ℂ}
    {f' : Matrix ι ι ℂ} {x : ℝ} (hf : WordsMD f f' x) (a b : ι → ℝ) :
    HasDerivAt (fun y => ent (f y) a b) (ent f' a b) x := by
  simp only [words_ent_eq]
  exact HasDerivAt.fun_sum fun s _ => HasDerivAt.fun_sum fun t _ =>
    ((hf s t).const_mul _).mul_const _

/-- `y ↦ G(X^{y}_{(iμ)})` is continuous. -/
private theorem words_continuousAt_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ) :
    ContinuousAt (fun y => G Sig (Xupd A i μ y) z) x := by
  have hX : Continuous fun y : ℝ => cplx (Xupd A i μ y) := by
    refine continuous_matrix fun a b => ?_
    by_cases h : a = i ∧ b = μ
    · simpa [cplx, Xupd, h] using Complex.continuous_ofReal
    · simpa [cplx, Xupd, h] using continuous_const
  have hXt : Continuous fun y : ℝ => cplx (Xupd A i μ y)ᵀ := by
    refine continuous_matrix fun a b => ?_
    by_cases h : b = i ∧ a = μ
    · simpa [cplx, Xupd, h] using Complex.continuous_ofReal
    · simpa [cplx, Xupd, h] using continuous_const
  have hH : Continuous fun y => H Sig (Xupd A i μ y) z :=
    continuous_const.matrix_fromBlocks hX hXt continuous_const
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (H_isUnit hSig (Xupd A i μ x) hz)
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  change ContinuousAt (fun y => (H Sig (Xupd A i μ y) z)⁻¹) x
  exact hinv.comp (f := fun y => H Sig (Xupd A i μ y) z) hH.continuousAt

/-- `d/dy G(X^{y}_{(iμ)}) = −G Δ¹ G`. -/
private theorem words_MD_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ) :
    WordsMD (fun y => G Sig (Xupd A i μ y) z)
      (-(G Sig (Xupd A i μ x) z * Delta i μ 1 * G Sig (Xupd A i μ x) z)) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set G0 := G Sig (Xupd A i μ x) z with hG0
  have hid : ∀ h : ℝ, G Sig (Xupd A i μ (x + h)) z - G0 =
      (-(h : ℂ)) • (G Sig (Xupd A i μ (x + h)) z * Delta i μ 1 * G0) := by
    intro h
    have e := res_exp hSig A hz i μ x (x + h) 0
    rw [show x - (x + h) = -h by ring, words_Delta_smul] at e
    simp only [zero_add, pow_one, Finset.Icc_eq_empty_of_lt one_pos,
      Finset.sum_empty, add_zero] at e
    rw [show G Sig (Xupd A i μ (x + h)) z - G0 = G Sig (Xupd A i μ (x + h)) z *
      (((-h : ℝ) : ℂ) • Delta i μ 1 * G0) from sub_eq_iff_eq_add'.2 e]
    push_cast
    simp [Matrix.mul_assoc]
  have hc : ∀ r, ContinuousAt (fun h : ℝ => G Sig (Xupd A i μ (x + h)) z s r) 0 := fun r => by
    have h2 : ContinuousAt (fun h : ℝ => x + h) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have h3 : ContinuousAt ((fun y => G Sig (Xupd A i μ y) z) ∘ fun h : ℝ => x + h) 0 :=
      ContinuousAt.comp_of_eq (words_continuousAt_G hSig A hz i μ x) h2 (by simp)
    exact ((continuous_apply r).comp (continuous_apply s)).continuousAt.comp h3
  have hE : ContinuousAt
      (fun h : ℝ => (G Sig (Xupd A i μ (x + h)) z * Delta i μ 1 * G0) s t) 0 := by
    simp only [words_mul_Delta_mul]
    exact ((hc _).mul continuousAt_const).add ((hc _).mul continuousAt_const)
  have hlim := hE.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [add_zero] at hlim
  refine hlim.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℂ) ≠ 0 := by simpa using hh
  have := congrFun (congrFun (hid h) s) t
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this, Complex.real_smul]
  push_cast
  field_simp

/-- `d/dy (Δ¹ G)^k = −k (Δ¹ G)^{k+1}`. -/
private theorem words_MD_pow {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ)
    (k : ℕ) :
    WordsMD (fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k)
      (-(k : ℂ) • (Delta i μ 1 * G Sig (Xupd A i μ x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using words_MD_const (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) x
  | succ k ih =>
    have hDG := words_MD_mul (words_MD_const (Delta i μ 1) x) (words_MD_G hSig A hz i μ x)
    have h := words_MD_mul ih hDG
    have e : (fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ (k + 1)) =
        fun y => (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k *
          (Delta i μ 1 * G Sig (Xupd A i μ y) z) :=
      funext fun y => pow_succ _ _
    rw [e]
    convert h using 1
    have e2 : Delta i μ 1 * -(G Sig (Xupd A i μ x) z * Delta i μ 1 * G Sig (Xupd A i μ x) z) =
        -((Delta i μ 1 * G Sig (Xupd A i μ x) z) * (Delta i μ 1 * G Sig (Xupd A i μ x) z)) := by
      simp [Matrix.mul_assoc]
    rw [Matrix.zero_mul, zero_add, e2, smul_mul_assoc, ← pow_succ, Matrix.mul_neg,
      ← Matrix.mul_assoc, ← pow_succ, ← pow_succ, Nat.cast_succ, neg_add, add_smul, neg_one_smul]

/-- `d/dy G(Δ¹G)^k = −(k+1) G(Δ¹G)^{k+1}`. -/
private theorem words_MD_T {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (x : ℝ)
    (k : ℕ) :
    WordsMD (fun y => G Sig (Xupd A i μ y) z * (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k)
      (-((k : ℂ) + 1) • (G Sig (Xupd A i μ x) z * (Delta i μ 1 * G Sig (Xupd A i μ x) z) ^ (k + 1)))
      x := by
  have h := words_MD_mul (words_MD_G hSig A hz i μ x) (words_MD_pow hSig A hz i μ x k)
  convert h using 1
  rw [Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_assoc (G Sig (Xupd A i μ x) z) (Delta i μ 1),
    Matrix.mul_assoc (G Sig (Xupd A i μ x) z), ← pow_succ', neg_add, add_smul, neg_one_smul,
    add_comm]

/-- `d/dx a_k(x) = (k + 1) a_{k+1}(x)` along the entry `(i, μ)`. -/
theorem hasDerivAt_resCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => resCoeff Sig (Xupd A i μ y) z v i μ k)
      (((k : ℂ) + 1) * resCoeff Sig (Xupd A i μ x) z v i μ (k + 1)) x := by
  have hT := words_MD_T hSig A hz i μ x k
  have hC : WordsMD (fun y => G Sig (Xupd A i μ y) z * (Delta i μ 1 * G Sig (Xupd A i μ y) z) ^ k
      - if k = 0 then PiZ N Sig z else 0)
      (-((k : ℂ) + 1) • (G Sig (Xupd A i μ x) z * (Delta i μ 1 * G Sig (Xupd A i μ x) z) ^ (k + 1)))
      x := by
    intro s t
    simpa using (hT s t).sub_const ((if k = 0 then PiZ N Sig z else 0) s t)
  have h := (words_MD_ent hC (vbar Sig v) (vbar Sig v)).const_mul ((-1 : ℂ) ^ k)
  refine h.congr_deriv ?_
  simp only [resCoeff, words_ent_smul, Nat.succ_ne_zero, ↓reduceIte, sub_zero, pow_succ]
  ring

/-! ### The coefficients `f_n` -/

/-- The factor `a` (for `r < p/2`) or `\bar a` (for `r ≥ p/2`) in `fCoeff`. -/
private def wordsC (p : ℕ) (r : Fin p) (b : ℂ) : ℂ :=
  if (r : ℕ) < p / 2 then b else starRingEnd ℂ b

private theorem words_fCoeff_eq (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    fCoeff p a n = ∑ k ∈ Finset.Nat.antidiagonalTuple p n, ∏ r : Fin p, wordsC p r (a (k r)) :=
  rfl

private theorem words_norm_C (p : ℕ) (r : Fin p) (b : ℂ) : ‖wordsC p r b‖ = ‖b‖ := by
  unfold wordsC; split_ifs <;> simp

private theorem words_hasDerivAt_C (p : ℕ) (r : Fin p) {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) : HasDerivAt (fun y => wordsC p r (f y)) (wordsC p r f') x := by
  unfold wordsC
  split_ifs
  · exact hf
  · exact hf.star

private theorem words_C_mul (p : ℕ) (r : Fin p) (k : ℕ) (b : ℂ) :
    wordsC p r (((k : ℂ) + 1) * b) = ((k : ℂ) + 1) * wordsC p r b := by
  unfold wordsC
  split_ifs
  · rfl
  · rw [map_mul, map_add, map_natCast, map_one]

/-- Shifting one index: `∑_{κ ∈ T(p,n)} (κ_r + 1) g(κ + e_r) = ∑_{κ' ∈ T(p,n+1)} κ'_r g(κ')`. -/
private theorem words_sum_shift (p n : ℕ) (r : Fin p) (g : (Fin p → ℕ) → ℂ) :
    ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, (((κ r : ℕ) : ℂ) + 1) * g (κ + Pi.single r 1) =
      ∑ κ ∈ Finset.Nat.antidiagonalTuple p (n + 1), ((κ r : ℕ) : ℂ) * g κ := by
  conv_rhs => rw [← Finset.sum_filter_of_ne (p := fun κ : Fin p → ℕ => κ r ≠ 0)
    (fun κ _ h hκ => h (by simp [hκ]))]
  refine Finset.sum_nbij' (fun κ => κ + Pi.single r 1) (fun κ => κ - Pi.single r 1) ?_ ?_ ?_ ?_ ?_
  · intro κ hκ
    simp only [Finset.Nat.mem_antidiagonalTuple] at hκ
    simp [Finset.Nat.mem_antidiagonalTuple, Finset.sum_add_distrib, hκ]
  · intro κ hκ
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hκ
    simp only [Finset.Nat.mem_antidiagonalTuple]
    have e : κ = (κ - Pi.single r 1) + Pi.single r 1 := by
      funext j
      by_cases hj : j = r
      · subst hj; simp; omega
      · simp [hj]
    have := hκ.1
    rw [e] at this
    simp only [Pi.add_apply, Finset.sum_add_distrib] at this
    simp only [Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte] at this
    omega
  · intro κ _
    funext j
    simp
  · intro κ hκ
    simp only [Finset.mem_filter] at hκ
    funext j
    by_cases hj : j = r
    · subst hj; simp; omega
    · simp [hj]
  · intro κ _
    simp

/-- `d/dx f_n(x) = (n + 1) f_{n+1}(x)` for any family with `d/dx a_k = (k + 1) a_{k+1}`. -/
theorem hasDerivAt_fCoeff (p : ℕ) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => fCoeff p (a y) n) (((n : ℂ) + 1) * fCoeff p (a x) (n + 1)) x := by
  simp only [words_fCoeff_eq]
  have h := HasDerivAt.fun_sum (u := Finset.Nat.antidiagonalTuple p n) fun κ _ =>
    HasDerivAt.fun_finsetProd (u := Finset.univ) fun r _ =>
      words_hasDerivAt_C p r (ha (κ r) x)
  refine h.congr_deriv ?_
  set Q : (Fin p → ℕ) → ℂ := fun κ => ∏ r : Fin p, wordsC p r (a x (κ r)) with hQ
  have hterm : ∀ κ : Fin p → ℕ, ∀ r : Fin p,
      (∏ j ∈ Finset.univ.erase r, wordsC p j (a x (κ j))) •
          wordsC p r (((κ r : ℕ) + 1 : ℂ) * a x (κ r + 1)) =
        (((κ r : ℕ) : ℂ) + 1) * Q (κ + Pi.single r 1) := by
    intro κ r
    rw [smul_eq_mul, words_C_mul, hQ]
    simp only
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    have : ∏ j ∈ Finset.univ.erase r, wordsC p j (a x ((κ + Pi.single r 1 : Fin p → ℕ) j)) =
        ∏ j ∈ Finset.univ.erase r, wordsC p j (a x (κ j)) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [this]
    simp
    ring
  simp only [hterm]
  rw [Finset.sum_comm]
  simp only [words_sum_shift]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [← Finset.sum_mul]
  congr 1
  have := (Finset.Nat.mem_antidiagonalTuple.1 hκ)
  exact_mod_cast this

/-- `f_0 = |a_0|^p` for even `p`. -/
theorem fCoeff_zero {p : ℕ} (hp : Even p) (a : ℕ → ℂ) : fCoeff p a 0 = (‖a 0‖ : ℂ) ^ p := by
  obtain ⟨m, rfl⟩ := hp
  rw [words_fCoeff_eq, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton,
    Fin.prod_univ_add]
  have h1 : ∀ r : Fin m, wordsC (m + m) (Fin.castAdd m r) (a ((0 : Fin (m + m) → ℕ)
      (Fin.castAdd m r))) = a 0 := fun r => by
    simp only [wordsC, Fin.val_castAdd, Pi.zero_apply]
    simp only [show (r : ℕ) < (m + m) / 2 by omega, ↓reduceIte]
  have h2 : ∀ r : Fin m, wordsC (m + m) (Fin.natAdd m r) (a ((0 : Fin (m + m) → ℕ)
      (Fin.natAdd m r))) = starRingEnd ℂ (a 0) := fun r => by
    simp only [wordsC, Fin.val_natAdd, Pi.zero_apply]
    simp only [show ¬ (m + (r : ℕ) < (m + m) / 2) by omega, ↓reduceIte]
  simp only [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ### Re-expansion with remainder -/

/-- The remainder `R_{l,K}(s) = f_l(x + s) − ∑_{k ≤ K} C(l+k, l) s^k f_{l+k}(x)`. -/
private def wordsR (p : ℕ) (a : ℝ → ℕ → ℂ) (x : ℝ) (l K : ℕ) (s : ℝ) : ℂ :=
  fCoeff p (a (x + s)) l -
    ∑ k ∈ Finset.range (K + 1), ((l + k).choose l : ℂ) * (s : ℂ) ^ k * fCoeff p (a x) (l + k)

private theorem words_R_zero (p : ℕ) (a : ℝ → ℕ → ℂ) (x : ℝ) (l K : ℕ) :
    wordsR p a x l K 0 = 0 := by
  simp [wordsR, Finset.sum_range_succ']

/-- `R_{l,K}' = (l + 1)(f_{l+1}(x + s) − ∑_{j < K} C(l+1+j, l+1) s^j f_{l+1+j}(x))`. -/
private theorem words_hasDerivAt_R (p : ℕ) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x) (x : ℝ) (l K : ℕ)
    (s : ℝ) :
    HasDerivAt (wordsR p a x l K) (((l : ℂ) + 1) * (fCoeff p (a (x + s)) (l + 1) -
      ∑ j ∈ Finset.range K, ((l + 1 + j).choose (l + 1) : ℂ) * (s : ℂ) ^ j *
        fCoeff p (a x) (l + 1 + j))) s := by
  have h1 : HasDerivAt (fun s : ℝ => fCoeff p (a (x + s)) l)
      (((l : ℂ) + 1) * fCoeff p (a (x + s)) (l + 1)) s :=
    (hasDerivAt_fCoeff p ha l (x + s)).comp_const_add x s
  have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range (K + 1),
      ((l + k).choose l : ℂ) * (s : ℂ) ^ k * fCoeff p (a x) (l + k))
      (∑ k ∈ Finset.range (K + 1),
        ((l + k).choose l : ℂ) * ((k : ℂ) * (s : ℂ) ^ (k - 1)) * fCoeff p (a x) (l + k)) s :=
    HasDerivAt.fun_sum fun k _ =>
      (((hasDerivAt_pow k (s : ℂ)).comp_ofReal).const_mul _).mul_const _
  refine (h1.sub h2).congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, mul_sub,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : ((l + (j + 1)).choose l : ℂ) * ((j : ℂ) + 1) =
      ((l : ℂ) + 1) * ((l + 1 + j).choose (l + 1) : ℂ) := by
    have e := Nat.choose_succ_right_eq (l + (j + 1)) l
    rw [show l + (j + 1) - l = j + 1 by omega, show l + (j + 1) = l + 1 + j by omega] at e
    rw [show l + (j + 1) = l + 1 + j by omega]
    exact_mod_cast (by linarith [e] : (l + 1 + j).choose l * (j + 1) =
      (l + 1) * (l + 1 + j).choose (l + 1))
  rw [show l + (j + 1) = l + 1 + j by omega] at hc ⊢
  push_cast
  linear_combination ((s : ℂ) ^ j * fCoeff p (a x) (l + 1 + j)) * hc

private theorem words_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;>
    linarith [le_abs_self t, neg_abs_le t]

private theorem words_taylor_aux (p : ℕ) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x) (x B : ℝ) (K : ℕ) :
    ∀ (l : ℕ) (t : ℝ), (∀ s ∈ Set.uIcc 0 t, ‖fCoeff p (a (x + s)) (l + K + 1)‖ ≤ B) →
      ‖wordsR p a x l K t‖ ≤ ((l + K + 1).factorial / l.factorial : ℝ) * B * |t| ^ (K + 1) := by
  induction K with
  | zero =>
    intro l t hB
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := wordsR p a x l 0) (C := ((l : ℝ) + 1) * B)
      (fun s _ => (words_hasDerivAt_R p ha x l 0 s).hasDerivWithinAt)
      (fun s hs => by
        simp only [Finset.range_zero, Finset.sum_empty, sub_zero, norm_mul]
        have := hB s hs
        simp only [add_zero] at this
        rw [show ‖(l : ℂ) + 1‖ = (l : ℝ) + 1 by norm_cast]
        exact mul_le_mul_of_nonneg_left this (by positivity))
      (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
    rw [words_R_zero, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
    refine hmvt.trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  | succ K ih =>
    intro l t hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 Set.left_mem_uIcc)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := wordsR p a x l (K + 1))
      (C := ((l : ℝ) + 1) * (((l + 1 + K + 1).factorial / (l + 1).factorial : ℝ) * B *
        |t| ^ (K + 1)))
      (fun s _ => (words_hasDerivAt_R p ha x l (K + 1) s).hasDerivWithinAt)
      (fun s hs => by
        rw [norm_mul, show ‖(l : ℂ) + 1‖ = (l : ℝ) + 1 by norm_cast]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hR := ih (l + 1) s (fun s' hs' => by
          rw [show l + 1 + K + 1 = l + (K + 1) + 1 by omega]
          exact hB s' (Set.uIcc_subset_uIcc_left hs hs'))
        refine hR.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (abs_nonneg s) (words_abs_le_of_mem_uIcc hs) _)
      (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
    rw [words_R_zero, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
    refine hmvt.trans (le_of_eq ?_)
    rw [show l + 1 + K + 1 = l + (K + 1) + 1 by omega, Nat.factorial_succ l]
    push_cast
    field_simp
    ring

/-- Re-expansion with remainder: `f_l(x + t) = ∑_{k ≤ K} C(l+k, l) t^k f_{l+k}(x) + R`,
`|R| ≤ (l + K + 1)! B |t|^{K+1}` with `B` a bound for `f_{l+K+1}` on `[x, x + t]`. -/
theorem fCoeff_taylor (p : ℕ) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x) (l K : ℕ)
    (x t B : ℝ) (hB : ∀ s ∈ Set.uIcc 0 t, ‖fCoeff p (a (x + s)) (l + K + 1)‖ ≤ B) :
    ‖fCoeff p (a (x + t)) l -
        ∑ k ∈ Finset.range (K + 1), ((l + k).choose l : ℂ) * (t : ℂ) ^ k * fCoeff p (a x) (l + k)‖
      ≤ ((l + K + 1).factorial : ℝ) * B * |t| ^ (K + 1) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 Set.left_mem_uIcc)
  refine (words_taylor_aux p ha x B K l t hB).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hB0) (by positivity)
  exact div_le_self (by positivity)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero l))

/-! ### Norm bounds -/

/-- Coefficient bound from `|a_k| ≤ B^{k+1}`. -/
theorem norm_fCoeff_le (p : ℕ) {a : ℕ → ℂ} {B : ℝ} (hB1 : 1 ≤ B) (n : ℕ)
    (ha : ∀ k ≤ n, ‖a k‖ ≤ B ^ (k + 1)) :
    ‖fCoeff p a n‖ ≤ ((n : ℝ) + 1) ^ p * B ^ (n + p) := by
  have hB0 : 0 ≤ B := by linarith
  have hcard : ((Finset.Nat.antidiagonalTuple p n).card : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
    have hsub : Finset.Nat.antidiagonalTuple p n ⊆
        Fintype.piFinset fun _ : Fin p => Finset.range (n + 1) := by
      intro κ hκ
      rw [Finset.Nat.mem_antidiagonalTuple] at hκ
      simp only [Fintype.mem_piFinset, Finset.mem_range]
      intro r
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
      omega
    have := Finset.card_le_card hsub
    simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact_mod_cast this
  rw [words_fCoeff_eq]
  calc _ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ‖∏ r : Fin p, wordsC p r (a (κ r))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, B ^ (n + p) := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [norm_prod]
        calc _ ≤ ∏ r : Fin p, B ^ (κ r + 1) :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
                rw [words_norm_C]
                refine ha _ ?_
                have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
                omega
          _ = B ^ (n + p) := by
              rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, hκ]
              simp
    _ = ((Finset.Nat.antidiagonalTuple p n).card : ℝ) * B ^ (n + p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- (w_est): `|A(w)| ≤ B^{n(w)+1}` when all entries in the word are at most `B`. -/
theorem wordA_le {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {B : ℝ} (h0 : Fv Sig A z v ≤ B)
    (h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B)
    (h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) (n : ℕ) (w : Word n) :
    ‖wordA Sig A z v i μ n w‖ ≤ B ^ (n + 1) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans h0
  cases n with
  | zero => simpa [wordA, Fv] using h0
  | succ k =>
    simp only [wordA, norm_mul, norm_prod]
    have hp : ∏ l : Fin k, ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖ ≤
        B ^ k := by
      calc _ ≤ ∏ _l : Fin k, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => h3 _ _
        _ = B ^ k := by simp
    calc _ ≤ B * B ^ k * B :=
          mul_le_mul (mul_le_mul (h1 _) hp (by positivity) hB0) (h2 _) (norm_nonneg _)
            (by positivity)
      _ = B ^ (k + 1 + 1) := by ring

/-- (w_est) at the level of entries: `|a_k| ≤ 2^k B^{k+1}` when the entries
`G_{v̄[t]}`, `G_{[s]v̄}`, `G_{[s][t]}` and `F_v` are at most `B`. -/
theorem norm_resCoeff_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) {B : ℝ} (h0 : Fv Sig A z v ≤ B)
    (h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B)
    (h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) (k : ℕ) :
    ‖resCoeff Sig A z v i μ k‖ ≤ 2 ^ k * B ^ (k + 1) := by
  rw [resCoeff_eq_sum_wordA hSig A hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc _ ≤ ∑ w : Word k, ‖wordA Sig A z v i μ k w‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Word k, B ^ (k + 1) :=
        Finset.sum_le_sum fun w _ => wordA_le A z v i μ h0 h1 h2 h3 k w
    _ = 2 ^ k * B ^ (k + 1) := by simp

/-! ### Examples -/

/-- The word `𝐢𝛍` (`n = 1`, pair `true`): `A(𝐢𝛍) = G_{v̄ i} G_{μ v̄}`. -/
example (Sig : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (v : Fin 2 ⊕ Fin 2 → ℝ) :
    wordA Sig A z v 0 0 1 (fun _ => true) =
      ent (G Sig A z) (vbar Sig v) (eI (Sum.inl 0)) *
        ent (G Sig A z) (eI (Sum.inr 0)) (vbar Sig v) := by
  simp [wordA, letterT, letterS]

/-- `|𝒲_n| = 2^n`. -/
example (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by simp

/-! ### Instances at `M = N = 2`, `Σ = 1`, `z = i` -/

/-- The coefficient bound at `p = 2`, `n = 3`, `a_k = 2^k`, `B = 2`. -/
example : ‖fCoeff 2 (fun k => (2 : ℂ) ^ k) 3‖ ≤ ((3 : ℕ) + 1 : ℝ) ^ 2 * 2 ^ (3 + 2) :=
  norm_fCoeff_le 2 (by norm_num) 3 fun k _ => by
    rw [norm_pow, Complex.norm_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)

end Anisotropic
