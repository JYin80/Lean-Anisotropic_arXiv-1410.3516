module

public import Anisotropic.Comparison.Brackets

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Tagged words (Definition 8.7), `A⁰`, `A⁺`, (whA01), (wh_A_identity), `Â`, `Q_μ`, `Y_μ`, column replacement -/

/-- The scalar part `A(w₀, σ)` of the empty word: `G^{(μ)}_{v̄v̄} − Π^{(μ)}_{v̄v̄}`, `1`, `−1`. -/
def emptyScal (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (s : Fin 3) : ℂ :=
  if s = 0 then ent (Gmu Sig A z μ) (vbar Sig v) (vbar Sig v) -
      (ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v) -
        ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 * PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
  else if s = 1 then 1 else -1

/-- The linear forms of `A(w₀, σ)`: none, `(G^{(μ)}X)_{v̄μ}(X^*G^{(μ)})_{μv̄}`,
`(G^{(μ)}X)_{v̄μ} + (X^*G^{(μ)})_{μv̄}`. -/
def emptyForms (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (s : Fin 3) : List (Fin M → ℂ) :=
  if s = 0 then []
  else if s = 1 then [colC Sig A z (vbar Sig v) μ, rowC Sig A z (vbar Sig v) μ]
  else [colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ]

/-- Definition 8.7: `A_{v,i,μ}(w, σ)`, `σ ∈ ℤ₃^{n(w)+1}`. -/
def tagA (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) : (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → ℂ
  | 0, _, σ => emptyScal Sig A z v μ (σ 0) *
      ((emptyForms Sig A z v μ (σ 0)).map fun c => linForm c fun j => A j μ).prod
  | k + 1, w, σ => ∏ l : Fin (k + 2), brack Sig A z v i μ (factorX w l) (factorY w l) (σ l)

/-- `A⁰(w, σ)`: the `X^{(μ)}`-measurable factor of (whA01). -/
def tagScal (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → ℂ
  | 0, _, σ => emptyScal Sig A z v μ (σ 0)
  | k + 1, w, σ => ∏ l : Fin (k + 2), brackScal Sig A z v i μ (factorX w l) (factorY w l) (σ l)

/-- The coefficient vectors of the linear forms of `A⁺(w, σ)` (whA01), (A1_form). -/
def tagForms (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → List (Fin M → ℂ)
  | 0, _, σ => emptyForms Sig A z v μ (σ 0)
  | k + 1, w, σ =>
      (List.ofFn fun l : Fin (k + 2) => brackForms Sig A z v i μ (factorX w l) (factorY w l) (σ l)).flatten

/-- `deg A(w, σ)` (Definition 8.7 (iv)). -/
def tagDeg : (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → ℕ
  | 0, _, σ => if σ 0 = 0 then 0 else if σ 0 = 1 then 2 else 1
  | _k + 1, w, σ => ∑ l, degTab (factorX w l) (factorY w l) (σ l)

/-- `|σ|_μ = #{l : σ(l) ≥ 1}` (Definition 8.7 (iii)). -/
def tagMu {n : ℕ} (σ : Fin (n + 1) → Fin 3) : ℕ := ∑ l, if σ l = 0 then 0 else 1

/-- `|σ|_v = #{l : σ(l) = 2}` (Definition 8.7 (iii)). -/
def tagV {n : ℕ} (σ : Fin (n + 1) → Fin 3) : ℕ := ∑ l, if σ l = 2 then 1 else 0

/-- No factor of `A(w, σ)` is an identically vanishing bracket. -/
def tagNZ : (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → Bool
  | 0, _, _ => true
  | k + 1, w, σ => (List.finRange (k + 2)).all fun l => !zeroTab (factorX w l) (factorY w l) (σ l)

/-- `f_i` of one word: endpoint factors `[G_{v̄ i}]^0`, `[G_{i v̄}]^0`. -/
def tagF : (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → ℕ
  | 0, _, _ => 0
  | _k + 1, w, σ => (if σ 0 = 0 ∧ factorY w 0 = .I then 1 else 0) +
      (if σ (Fin.last _) = 0 ∧ factorX w (Fin.last _) = .I then 1 else 0)

section Helpers

private theorem taggedWords_ent_eq {p : Type*} [Fintype p] (B : Matrix p p ℂ) (x y : p → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem taggedWords_ent_eI_right {p : Type*} [Fintype p] [DecidableEq p]
    (B : Matrix p p ℂ) (x : p → ℝ) (r : p) : ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [taggedWords_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem taggedWords_ent_eI_left {p : Type*} [Fintype p] [DecidableEq p]
    (B : Matrix p p ℂ) (y : p → ℝ) (r : p) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [taggedWords_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem taggedWords_ent_sub {p : Type*} [Fintype p] (B C : Matrix p p ℂ) (x y : p → ℝ) :
    ent (B - C) x y = ent B x y - ent C x y := by
  simp only [ent, sub_mulVec, dotProduct_sub]

private theorem taggedWords_ent_GX (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    ent (G1 Sig A z (Sum.inr μ) * Xhat A) x (eI (Sum.inr μ))
      = linForm (colC Sig A z x μ) (fun j => A j μ) := by
  rw [taggedWords_ent_eI_right]
  have h : ∀ s, (G1 Sig A z (Sum.inr μ) * Xhat A) s (Sum.inr μ)
      = ∑ j, G1 Sig A z (Sum.inr μ) s (Sum.inl j) * (A j μ : ℂ) := by
    intro s; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  simp only [h, linForm, colC, Gmu, taggedWords_ent_eI_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

private theorem taggedWords_ent_XtG (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (y : Fin M ⊕ Fin N → ℝ) :
    ent ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (eI (Sum.inr μ)) y
      = linForm (rowC Sig A z y μ) (fun j => A j μ) := by
  rw [taggedWords_ent_eI_left]
  have h : ∀ t, ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (Sum.inr μ) t
      = ∑ j, (A j μ : ℂ) * G1 Sig A z (Sum.inr μ) (Sum.inl j) t := by
    intro t; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  simp only [h, linForm, rowC, Gmu, taggedWords_ent_eI_left, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

private theorem taggedWords_linForm_add (c d : Fin M → ℂ) (y : Fin M → ℝ) :
    linForm (c + d) y = linForm c y + linForm d y := by
  simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem taggedWords_letVec_ofT (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (b : Bool) :
    letVec Sig v i μ (Letter.ofT b) = eI (letterT i μ b) := by
  cases b <;> rfl

private theorem taggedWords_letVec_ofS (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (b : Bool) :
    letVec Sig v i μ (Letter.ofS b) = eI (letterS i μ b) := by
  cases b <;> rfl

private theorem taggedWords_ofT_ne (b : Bool) : Letter.ofT b ≠ .V := by
  cases b <;> simp [Letter.ofT]

private theorem taggedWords_ofS_ne (b : Bool) : Letter.ofS b ≠ .V := by
  cases b <;> simp [Letter.ofS]

private theorem taggedWords_not_VV {k : ℕ} (w : Word (k + 1)) (l : Fin (k + 2)) :
    ¬(factorX w l = .V ∧ factorY w l = .V) := by
  rintro ⟨hx, hy⟩
  unfold factorX at hx
  unfold factorY at hy
  split_ifs at hx hy with h1 h2
  · exact taggedWords_ofT_ne _ hy
  · omega
  · exact taggedWords_ofS_ne _ hx
  · exact taggedWords_ofS_ne _ hx

/-- `A(w)` for `n(w) ≥ 1` is the product of its factors `G_{x_l y_l}`. -/
private theorem taggedWords_wordA_eq_prod (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (k : ℕ) (w : Word (k + 1)) :
    wordA Sig A z v i μ (k + 1) w = ∏ l : Fin (k + 2),
      ent (G Sig A z) (letVec Sig v i μ (factorX w l)) (letVec Sig v i μ (factorY w l)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  have h0x : factorX w 0 = .V := by simp [factorX]
  have h0y : factorY w 0 = Letter.ofT (w 0) := by simp [factorY]
  have hlx : factorX w (Fin.last k).succ = Letter.ofS (w (Fin.last k)) := by
    simp [factorX]; try rfl
  have hly : factorY w (Fin.last k).succ = .V := by simp [factorY]
  have hmx : ∀ j : Fin k, factorX w j.castSucc.succ = Letter.ofS (w j.castSucc) := by
    intro j; simp [factorX]; try rfl
  have hmy : ∀ j : Fin k, factorY w j.castSucc.succ = Letter.ofT (w j.succ) := by
    intro j; simp [factorY]; try rfl
  simp only [wordA, h0x, h0y, hlx, hly, hmx, hmy, taggedWords_letVec_ofT, taggedWords_letVec_ofS,
    ent_eI_eI]
  have hV : letVec Sig v i μ .V = vbar Sig v := rfl
  rw [hV, mul_assoc]

/-- (G_split) as a sum over the three tags. -/
private theorem taggedWords_split_sum {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (x y : Letter) (hxy : ¬(x = .V ∧ y = .V)) :
    ent (G Sig A z) (letVec Sig v i μ x) (letVec Sig v i μ y) =
      ∑ s : Fin 3, brack Sig A z v i μ x y s * (![1, G Sig A z (Sum.inr μ) (Sum.inr μ),
        ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) * G Sig A z (Sum.inr μ) (Sum.inr μ)] : Fin 3 → ℂ) s := by
  rw [G_split hSig A hz v i μ x y hxy, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- A sum over `Fin 1 → Fin 3` is a sum over the three constant tags. -/
private theorem taggedWords_sum_fin_one (f : (Fin 1 → Fin 3) → ℂ) :
    ∑ σ, f σ = f (fun _ => 0) + f (fun _ => 1) + f (fun _ => 2) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 3)).symm.sum_comp, Fin.sum_univ_three]
  rfl

/-- `G^{(μ)}` with column `μ` replaced: the minor `H^{(μ)}` is unchanged. -/
private theorem taggedWords_minorH_updCol (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (y : Fin M → ℝ) :
    minorH Sig (fun j ν => if ν = μ then y j else A j ν) z {Sum.inr μ} =
      minorH Sig A z {Sum.inr μ} := by
  ext ⟨s, hs⟩ ⟨t, ht⟩
  simp only [Finset.mem_singleton] at hs ht
  rcases s with s | s <;> rcases t with t | t
  · simp [minorH, H, linH]
  · have : t ≠ μ := fun h => ht (by rw [h])
    simp only [minorH, H, linH, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, cplx]
    exact congrArg (algebraMap ℝ ℂ) (ite_eq_right this)
  · have : s ≠ μ := fun h => hs (by rw [h])
    simp only [minorH, H, linH, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, cplx,
      Matrix.map_apply]
    exact congrArg (algebraMap ℝ ℂ) (ite_eq_right this)
  · simp [minorH, H, linH]

end Helpers

/-- (whA01): `A(w, σ) = A⁰(w, σ) A⁺(w, σ)`, `A⁺` the product of the linear forms. -/
theorem tagA_eq_scal_mul (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) :
    tagA Sig A z v i μ n w σ = tagScal Sig A z v i μ n w σ *
      ((tagForms Sig A z v i μ n w σ).map fun c => linForm c fun j => A j μ).prod := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [tagA, tagScal, tagForms, brack, List.map_flatten, List.prod_flatten, List.map_ofFn,
      List.prod_ofFn, Function.comp_def, Finset.prod_mul_distrib]

/-- `A⁺(w, σ)` has `deg A(w, σ)` linear forms. -/
theorem tagForms_length (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) :
    (tagForms Sig A z v i μ n w σ).length = tagDeg n w σ := by
  cases n with
  | zero =>
    simp only [tagForms, tagDeg, emptyForms]
    split_ifs <;> simp
  | succ k =>
    simp only [tagForms, tagDeg, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_def, brackForms_length]

/-- The coefficient product of (wh_A_identity): `∏_l c_{σ(l)} = G_μμ^{|σ|_μ} v̄(μ)^{|σ|_v}` for
`c = (1, G_μμ, v̄(μ) G_μμ)`. -/
theorem coef_prod {n : ℕ} (g a : ℂ) (σ : Fin (n + 1) → Fin 3) :
    ∏ l, (![1, g, a * g] : Fin 3 → ℂ) (σ l) = g ^ tagMu σ * a ^ tagV σ := by
  have h : ∀ s : Fin 3, (![1, g, a * g] : Fin 3 → ℂ) s =
      g ^ (if s = 0 then 0 else 1) * a ^ (if s = 2 then 1 else 0) := by
    intro s; fin_cases s <;> simp [mul_comm]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, tagMu, tagV]

/-- `Â_{v,i,μ}(w)`: `G_{v̄v̄} − Π_{v̄v̄} − v̄(μ)²(G_μμ − Π_μμ)` for `n(w) = 0`, `A(w)` otherwise
(Section 8, before Lemma 8.5). -/
def hatA (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) : (n : ℕ) → Word n → ℂ
  | 0, w => wordA Sig A z v i μ 0 w - ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 *
      (G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
  | k + 1, w => wordA Sig A z v i μ (k + 1) w

/-- (wh_A_identity): `Â(w) = ∑_σ A(w, σ) G_μμ^{|σ|_μ} v̄(μ)^{|σ|_v}`. -/
theorem wh_A_identity {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (n : ℕ) (w : Word n) :
    hatA Sig A z v i μ n w = ∑ σ : Fin (n + 1) → Fin 3, tagA Sig A z v i μ n w σ *
      G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu σ * ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ tagV σ := by
  cases n with
  | zero =>
    rw [taggedWords_sum_fin_one]
    have hmain := main_identity hSig A hz μ (vbar Sig v) (vbar Sig v)
    rw [taggedWords_ent_GX, taggedWords_ent_XtG] at hmain
    simp only [hatA, wordA, tagA, emptyScal, emptyForms, tagMu, tagV, taggedWords_ent_sub]
    simp only [Fin.isValue, ↓reduceIte, List.map_nil, List.prod_nil, List.map_cons,
      List.prod_cons, mul_one, one_ne_zero, Fin.reduceEq, taggedWords_linForm_add] at *
    rw [hmain]
    push_cast
    ring
  | succ k =>
    rw [hatA, taggedWords_wordA_eq_prod]
    simp only [fun l => taggedWords_split_sum hSig A hz v i μ (factorX w l) (factorY w l)
      (taggedWords_not_VV w l)]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, coef_prod, mul_assoc]
    rfl

/-- `x ↦ x` or `x ↦ x̄` according to the flag. -/
def conjIf (b : Bool) (x : ℂ) : ℂ := if b then starRingEnd ℂ x else x

/-- `X` with column `μ` replaced by `y`. -/
def updCol (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (y : Fin M → ℝ) : Matrix (Fin M) (Fin N) ℝ :=
  fun j ν => if ν = μ then y j else A j ν

/-- `G^{(μ)}` does not depend on the column `μ`. -/
theorem Gmu_updCol (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (y : Fin M → ℝ) : Gmu Sig (updCol A μ y) z μ = Gmu Sig A z μ := by
  have h := taggedWords_minorH_updCol Sig A z μ y
  unfold Gmu G1 Gm minorG
  rw [show minorH Sig (updCol A μ y) z {Sum.inr μ} = minorH Sig A z {Sum.inr μ} from h]

/-- `A⁰(w, σ)` and the coefficient vectors of `A⁺(w, σ)` do not depend on the column `μ`. -/
theorem tagScal_updCol (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (y : Fin M → ℝ) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) :
    tagScal Sig (updCol A μ y) z v i μ n w σ = tagScal Sig A z v i μ n w σ ∧
      tagForms Sig (updCol A μ y) z v i μ n w σ = tagForms Sig A z v i μ n w σ := by
  have h := Gmu_updCol Sig A z μ y
  have hc : ∀ x, colC Sig (updCol A μ y) z x μ = colC Sig A z x μ := fun x => by
    funext j; simp only [colC, h]
  have hr : ∀ x, rowC Sig (updCol A μ y) z x μ = rowC Sig A z x μ := fun x => by
    funext j; simp only [rowC, h]
  cases n with
  | zero => simp only [tagScal, tagForms, emptyScal, emptyForms, hc, hr, h, and_self]
  | succ k =>
    simp only [tagScal, tagForms, brackScal, brackForms, hc, hr, h, and_self]

/-- `Q_μ = (X^* G^{(μ)} X)_{μμ}`. -/
def Qmu (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) : ℂ :=
  ((Xhat A)ᵀ * Gmu Sig A z μ * Xhat A) (Sum.inr μ) (Sum.inr μ)

/-- `Y_μ = E_μ Q_μ = N⁻¹ ∑_{j ∈ 𝓘_M} G^{(μ)}_{jj}`. -/
def Ymu (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j, Gmu Sig A z μ (Sum.inl j) (Sum.inl j)

/-- `Q_μ` at the column `y`: `∑_{j,j'} y_j G^{(μ)}_{jj'} y_{j'}`. -/
theorem Qmu_updCol (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (y : Fin M → ℝ) :
    Qmu Sig (updCol A μ y) z μ =
      ∑ j, ∑ j', (y j : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') * (y j' : ℂ) := by
  rw [Qmu, Gmu_updCol]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Xhat, cplx,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, updCol, ite_true,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- Tagged words of length `n` form a `Fintype` of cardinality `2^n 3^{n+1}`. -/
example (n : ℕ) : Fintype.card (Word n × (Fin (n + 1) → Fin 3)) = 2 ^ n * 3 ^ (n + 1) := by
  simp

/-- The word `𝐢𝛍` has 9 tags, of which exactly 6 avoid the zero bracket `[G_{μv̄}]^0`. -/
example : (Finset.univ.filter fun σ : Fin 2 → Fin 3 => tagNZ 1 (fun _ => true) σ = true).card = 6 := by
  decide

/-! ### Compiled instances at `M = N = 2`, `z = i`, `μ = 0`, `i = 0` -/

section Checks

open Complex

/-- The vector `v = (1, 1, 1, 1)` on `𝓘 = Fin 2 ⊕ Fin 2`; `v̄(μ) = 1`. -/
local notation "v1" => (fun _ => (1 : ℝ) : Fin 2 ⊕ Fin 2 → ℝ)

/-- (wh_A_identity) at `Σ = 1`, `X = 0`, `z = i`, `w = 𝐢𝛍`. -/
example :
    hatA (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I v1 0 0 1
        (fun _ => true) =
      ∑ σ : Fin 2 → Fin 3,
        tagA (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I v1 0 0 1
            (fun _ => true) σ *
          G (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I (Sum.inr 0)
              (Sum.inr 0) ^ tagMu σ *
          ((vbar (diagonal fun _ : Fin 2 => (1 : ℝ)) v1 (Sum.inr 0) : ℝ) : ℂ) ^ tagV σ :=
  wh_A_identity (posDef_diagonal_iff.2 fun _ => one_pos) 0 (by simp) v1 0 0 1 (fun _ => true)

end Checks

end Anisotropic
