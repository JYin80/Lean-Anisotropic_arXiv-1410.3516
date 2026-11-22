module

public import Anisotropic.Comparison.TaggedWords
public import Anisotropic.Comparison.RoughBound
public import Anisotropic.Probability.LDE.Conditional
public import Anisotropic.Probability.NormBound.Main
public import Anisotropic.LinAlg.ResolventId
public import Anisotropic.Framework.DominationUnion

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The constants of §8, the event `Θ` (§8.3), Lemma 8.9, (bound_sum_hat), the expansion of `G_μμ` -/

/-- The number `K_τ = ⌈24/τ⌉` of terms of the expansion (Gmumu_exp2) of `G_μμ`. -/
def kTau (τ : ℝ) : ℕ := ⌈24 / τ⌉₊

/-- The constant `C₀(τ) = ⌈2400/τ⌉` of (cond_delta), used for §7 and §8 alike. -/
def czero (τ : ℝ) : ℝ := (⌈2400 / τ⌉₊ : ℝ)

/-- `δ = min(ε, τ)/(4 C₀(τ))`. -/
def deltaTwo (ε τ : ℝ) : ℝ := min ε τ / (4 * czero τ)

/-- The level `D_{m−1}` of (A_{m−1}) needed for one step of §8 at moment `p`. -/
def dPrevTwo (τ : ℝ) (p : ℕ) : ℝ := dPrev p * ((kTau τ : ℝ) + 1)

/-- The levels counted from the top: `levelDTwo 0 = D + 1`, `levelDTwo (k+1) = dPrevTwo(p(levelDTwo k))`. -/
def levelDTwo (τ δ D : ℝ) : ℕ → ℝ
  | 0 => D + 1
  | k + 1 => dPrevTwo τ (markovPow δ (levelDTwo τ δ D k))

/-- The `X^{(μ)}`-measurable part of the event `Θ` (§8.3): `|A(w₀, 0)| ≤ K` for the empty word,
the entries of `G^{(μ)}` other than `(v̄, v̄)` at most `K`, Ward sums at most `N b²`,
`|Y_μ| ≤ K`, `|−z − Y_μ|⁻¹ ≤ 2K`. -/
structure GoodMinor (K b : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) : Prop where
  ent_vv : ‖emptyScal Sig A z v μ 0‖ ≤ K
  ent_vj : ∀ j, ‖colC Sig A z (vbar Sig v) μ j‖ ≤ K ∧ ‖rowC Sig A z (vbar Sig v) μ j‖ ≤ K
  ent_jk : ∀ j k, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ≤ K
  ward_v : ∑ j, ‖colC Sig A z (vbar Sig v) μ j‖ ^ 2 ≤ N * b ^ 2 ∧
    ∑ j, ‖rowC Sig A z (vbar Sig v) μ j‖ ^ 2 ≤ N * b ^ 2
  ward_j : ∀ j, ∑ k, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ^ 2 ≤ N * b ^ 2 ∧
    ∑ k, ‖Gmu Sig A z μ (Sum.inl k) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2
  y_le : ‖Ymu Sig A z μ‖ ≤ K
  zy_le : ‖(-z - Ymu Sig A z μ)⁻¹‖ ≤ 2 * K

/-- The event `Θ` of §8.3 at one `μ`: `GoodMinor`, the column forms at most `b`,
`|Z_μ| ≤ K N^{−τ/2}`, `|G_μμ| ≤ K`, and the rough bound `‖XᵀX‖ ≤ Cn`. -/
structure GoodSec8 (τ K b Cn : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) : Prop extends GoodMinor K b Sig A z v μ where
  col_v : ‖linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ‖ ≤ b ∧
    ‖linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ‖ ≤ b
  col_j : ∀ j, ‖linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤ b ∧
    ‖linForm (rowC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤ b
  z_le : ‖Qmu Sig A z μ - Ymu Sig A z μ‖ ≤ K * (N : ℝ) ^ (-τ / 2)
  gmumu_le : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K
  norm_le : ‖Aᵀ * A‖ ≤ Cn

section Brackets

private theorem prelimBounds_ent_eq {p : Type*} [Fintype p] (B : Matrix p p ℂ) (x y : p → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem prelimBounds_ent_eI_right {p : Type*} [Fintype p] [DecidableEq p]
    (B : Matrix p p ℂ) (x : p → ℝ) (r : p) : ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [prelimBounds_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem prelimBounds_ent_eI_left {p : Type*} [Fintype p] [DecidableEq p]
    (B : Matrix p p ℂ) (y : p → ℝ) (r : p) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [prelimBounds_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem prelimBounds_ent_sub {p : Type*} [Fintype p] (B C : Matrix p p ℂ) (x y : p → ℝ) :
    ent (B - C) x y = ent B x y - ent C x y := by
  simp only [ent, sub_mulVec, dotProduct_sub]

private theorem prelimBounds_ent_transpose {p : Type*} [Fintype p] (B : Matrix p p ℂ)
    (x y : p → ℝ) : ent Bᵀ x y = ent B y x := by
  rw [prelimBounds_ent_eq, prelimBounds_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem prelimBounds_linForm_add (c d : Fin M → ℂ) (y : Fin M → ℝ) :
    linForm (c + d) y = linForm c y + linForm d y := by
  simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `(G^{(μ)} X)_{xμ} = ∑_j G^{(μ)}_{xj} X_{jμ}`. -/
private theorem prelimBounds_ent_GX (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    ent (G1 Sig A z (Sum.inr μ) * Xhat A) x (eI (Sum.inr μ))
      = linForm (colC Sig A z x μ) (fun j => A j μ) := by
  rw [prelimBounds_ent_eI_right]
  have h : ∀ s, (G1 Sig A z (Sum.inr μ) * Xhat A) s (Sum.inr μ)
      = ∑ j, G1 Sig A z (Sum.inr μ) s (Sum.inl j) * (A j μ : ℂ) := by
    intro s; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  simp only [h, linForm, colC, Gmu, prelimBounds_ent_eI_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `(X^* G^{(μ)})_{μy} = ∑_j X_{jμ} G^{(μ)}_{jy}`. -/
private theorem prelimBounds_ent_XtG (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (y : Fin M ⊕ Fin N → ℝ) :
    ent ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (eI (Sum.inr μ)) y
      = linForm (rowC Sig A z y μ) (fun j => A j μ) := by
  rw [prelimBounds_ent_eI_left]
  have h : ∀ t, ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (Sum.inr μ) t
      = ∑ j, (A j μ : ℂ) * G1 Sig A z (Sum.inr μ) (Sum.inl j) t := by
    intro t; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  simp only [h, linForm, rowC, Gmu, prelimBounds_ent_eI_left, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- (main_identity) with the column forms `a_x = (G^{(μ)}X)_{xμ}`, `b_y = (X^*G^{(μ)})_{μy}`. -/
private theorem prelimBounds_main {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N)
    (x y : Fin M ⊕ Fin N → ℝ) :
    ent (G Sig A z) x y
      = (x (Sum.inr μ) * y (Sum.inr μ) : ℝ) * G Sig A z (Sum.inr μ) (Sum.inr μ) +
        ent (Gmu Sig A z μ) x y
        + G Sig A z (Sum.inr μ) (Sum.inr μ) * linForm (colC Sig A z x μ) (fun j => A j μ)
            * linForm (rowC Sig A z y μ) (fun j => A j μ)
        - (x (Sum.inr μ) : ℂ) * G Sig A z (Sum.inr μ) (Sum.inr μ)
            * linForm (rowC Sig A z y μ) (fun j => A j μ)
        - (y (Sum.inr μ) : ℂ) * G Sig A z (Sum.inr μ) (Sum.inr μ)
            * linForm (colC Sig A z x μ) (fun j => A j μ) := by
  have h := main_identity hSig A hz μ x y
  rw [prelimBounds_ent_GX, prelimBounds_ent_XtG] at h
  exact h

/-- `G^{(μ)}` is symmetric, so the row and column coefficient vectors agree. -/
private theorem prelimBounds_rowC_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (y : Fin M ⊕ Fin N → ℝ) :
    rowC Sig A z y μ = colC Sig A z y μ := by
  funext j
  rw [rowC, colC, ← prelimBounds_ent_transpose, Gmu_transpose hSig A hz μ]

/-- Row `μ` of `G^{(μ)}` vanishes. -/
private theorem prelimBounds_ent_M_left (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (y : Fin M ⊕ Fin N → ℝ) :
    ent (Gmu Sig A z μ) (eI (Sum.inr μ)) y = 0 := by
  rw [prelimBounds_ent_eI_left]; simp [Gmu, G1, Gm]

/-- Column `μ` of `G^{(μ)}` vanishes. -/
private theorem prelimBounds_ent_M_right (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    ent (Gmu Sig A z μ) x (eI (Sum.inr μ)) = 0 := by
  rw [prelimBounds_ent_eI_right]; simp [Gmu, G1, Gm]

private theorem prelimBounds_ofT_ne (b : Bool) : Letter.ofT b ≠ .V := by
  cases b <;> simp [Letter.ofT]

private theorem prelimBounds_ofS_ne (b : Bool) : Letter.ofS b ≠ .V := by
  cases b <;> simp [Letter.ofS]

/-- No factor of a nonempty word is `G_{v̄v̄}`. -/
private theorem prelimBounds_not_VV {k : ℕ} (w : Word (k + 1)) (l : Fin (k + 2)) :
    ¬(factorX w l = .V ∧ factorY w l = .V) := by
  rintro ⟨hx, hy⟩
  unfold factorX at hx
  unfold factorY at hy
  split_ifs at hx hy with h1 h2
  · exact prelimBounds_ofT_ne _ hy
  · omega
  · exact prelimBounds_ofS_ne _ hx
  · exact prelimBounds_ofS_ne _ hx

/-- A product of factors of norm at most `1`. -/
private theorem prelimBounds_prod_le_one {α : Type*} (l : List α) (f : α → ℂ)
    (h : ∀ c ∈ l, ‖f c‖ ≤ 1) : ‖(l.map f).prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, norm_mul]
    have h1 := h a (by simp)
    have h2 := ih fun c hc => h c (by simp [hc])
    calc ‖f a‖ * ‖(List.map f l).prod‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- On `Θ`, every bracket `[G_{xy}]^s` with `(x, y) ≠ (V, V)` is at most `K`. -/
private theorem prelimBounds_brack_le {τ K b Cn : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K)
    (hb : b ≤ 1) (h : GoodSec8 τ K b Cn Sig A z v μ) (i : Fin M) (x y : Letter) (s : Fin 3)
    (hxy : ¬(x = .V ∧ y = .V)) : ‖brack Sig A z v i μ x y s‖ ≤ K := by
  have hK0 : 0 ≤ K := by linarith
  have hforms : ∀ c ∈ brackForms Sig A z v i μ x y s,
      ‖linForm c (fun j => A j μ)‖ ≤ 1 := by
    intro c hc
    have hcV := (h.col_v.1).trans hb
    have hrV := (h.col_v.2).trans hb
    have hcI := (h.col_j i).1.trans hb
    have hrI := (h.col_j i).2.trans hb
    fin_cases s <;> cases x <;> cases y <;>
      simp [brackForms, letVec] at hc <;> (try rcases hc with rfl | rfl) <;>
      assumption
  unfold brack
  rw [norm_mul]
  have hp := prelimBounds_prod_le_one _ (fun c => linForm c fun j => A j μ) hforms
  by_cases hs : s = 0
  · subst hs
    have hnil : brackForms Sig A z v i μ x y 0 = [] := by simp [brackForms]
    rw [hnil, List.map_nil, List.prod_nil, norm_one, mul_one]
    cases x <;> cases y
    · exact absurd ⟨rfl, rfl⟩ hxy
    · simpa [brackScal, letVec, colC] using (h.ent_vj i).1
    · simp [brackScal, letVec, prelimBounds_ent_M_right, hK0]
    · simpa [brackScal, letVec, rowC] using (h.ent_vj i).2
    · simpa [brackScal, letVec, ent_eI_eI] using h.ent_jk i i
    · simp [brackScal, letVec, prelimBounds_ent_M_right, hK0]
    · simp [brackScal, letVec, prelimBounds_ent_M_left, hK0]
    · simp [brackScal, letVec, prelimBounds_ent_M_left, hK0]
    · simp [brackScal, letVec, prelimBounds_ent_M_left, hK0]
  · have hsc : ‖brackScal Sig A z v i μ x y s‖ ≤ 1 := by
      unfold brackScal
      simp only [hs, ite_false]
      split_ifs <;> simp
    calc ‖brackScal Sig A z v i μ x y s‖ * _ ≤ 1 * 1 :=
          mul_le_mul hsc hp (norm_nonneg _) zero_le_one
      _ ≤ K := by linarith

/-- `v̄ = v` for `v = e_μ`. -/
private theorem prelimBounds_vbar_eI_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (μ : Fin N) :
    vbar Sig (eI (Sum.inr μ)) = eI (Sum.inr μ) := by
  funext s
  rcases s with i | ν
  · have h : (eI (Sum.inr μ) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl = 0 := by
      funext k; simp [eI]
    simp only [vbar, Sum.elim_inl]
    rw [h, mulVec_zero]
    simp [eI]
  · simp [vbar]

/-- `A(w₀, 0) = (G − Π)_{v̄v̄} − v̄(μ)² (G − Π)_{μμ} − G_μμ (a b − v̄(μ)(a + b))`
(main_identity). -/
private theorem prelimBounds_emptyScal_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) :
    emptyScal Sig A z v μ 0 =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v) -
        ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 *
          (G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)) -
        G Sig A z (Sum.inr μ) (Sum.inr μ) *
          (linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ) *
              linForm (rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) -
            ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) *
              (linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ) +
                linForm (rowC Sig A z (vbar Sig v) μ) (fun j => A j μ))) := by
  have hm := prelimBounds_main hSig A hz μ (vbar Sig v) (vbar Sig v)
  simp only [emptyScal, ↓reduceIte, prelimBounds_ent_sub]
  rw [hm]
  push_cast
  ring

end Brackets


/-- Cauchy–Schwarz for a positive semidefinite real form. -/
private theorem prelimBounds_cs {ι : Type*} [Fintype ι] {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    (x y : ι → ℝ) : (x ⬝ᵥ P *ᵥ y) ^ 2 ≤ (x ⬝ᵥ P *ᵥ x) * (y ⬝ᵥ P *ᵥ y) := by
  have hT : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.1.eq
  have hsym : y ⬝ᵥ P *ᵥ x = x ⬝ᵥ P *ᵥ y := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]
  have h : ∀ r : ℝ, 0 ≤ (y ⬝ᵥ P *ᵥ y) * (r * r) + (2 * (x ⬝ᵥ P *ᵥ y)) * r + (x ⬝ᵥ P *ᵥ x) := by
    intro r
    have := hP.dotProduct_mulVec_nonneg (x + r • y)
    simp only [star_trivial, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
    rw [hsym] at this
    nlinarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

/-- `|Σ_{jj}| ≤ ‖Σ‖`. -/
private theorem prelimBounds_diag_le_norm (Sig : Matrix (Fin M) (Fin M) ℝ) (j : Fin M) :
    |Sig j j| ≤ ‖Sig‖ := by
  have h := Matrix.l2_opNorm_mulVec Sig (EuclideanSpace.single j 1)
  rw [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin M) ℝ).symm
    (Sig *ᵥ (PiLp.single 2 j (1 : ℝ)).ofLp)) j
  convert this using 1
  simp

private theorem prelimBounds_last {t η s Z Q : ℝ} (ht : 0 ≤ t) (hη : 0 < η) (hs : 0 < s)
    (hZ : 0 ≤ Z) (h1 : t ^ 2 ≤ s * Q) (h2 : η * Q ≤ Z * t) : t * η ≤ Z * s := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; positivity
  · have h3 : η * t ^ 2 ≤ s * (Z * t) := by
      calc η * t ^ 2 ≤ η * (s * Q) := mul_le_mul_of_nonneg_left h1 hη.le
        _ = s * (η * Q) := by ring
        _ ≤ s * (Z * t) := mul_le_mul_of_nonneg_left h2 hs.le
    have h4 : (t * η) * t ≤ (Z * s) * t := by nlinarith
    exact le_of_mul_le_mul_right h4 h0

/-- The `𝓘_M` diagonal of `G`: `|G_{jj}| ≤ |z| Σ_{jj}/η` (from `H G = 1`). -/
private theorem prelimBounds_G_inl_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (j : m) :
    ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ ≤ ‖z‖ * Sig j j / z.im := by
  set P := Sig⁻¹ with hPdef
  set u : m → ℝ := fun k => (G Sig X z (Sum.inl k) (Sum.inl j)).re
  set w : m → ℝ := fun k => (G Sig X z (Sum.inl k) (Sum.inl j)).im
  set sr : n → ℝ := fun ν => (G Sig X z (Sum.inr ν) (Sum.inl j)).re
  set si : n → ℝ := fun ν => (G Sig X z (Sum.inr ν) (Sum.inl j)).im
  have hHG := H_mul_G hSig X hz
  have hA : ∀ i, -(∑ k, (P i k : ℂ) * G Sig X z (Sum.inl k) (Sum.inl j)) +
      ∑ ν, (X i ν : ℂ) * G Sig X z (Sum.inr ν) (Sum.inl j) = if i = j then 1 else 0 := by
    intro i
    have h := congrFun (congrFun hHG (Sum.inl i)) (Sum.inl j)
    simp only [H, linH, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, Matrix.neg_apply, cplx, Matrix.map_apply, Matrix.one_apply,
      Sum.inl.injEq, neg_mul, Finset.sum_neg_distrib] at h
    rw [← h, hPdef]
    rfl
  have hB : ∀ ν, ∑ k, (X k ν : ℂ) * G Sig X z (Sum.inl k) (Sum.inl j) =
      z * G Sig X z (Sum.inr ν) (Sum.inl j) := by
    intro ν
    have h := congrFun (congrFun hHG (Sum.inr ν)) (Sum.inl j)
    simp only [H, linH, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.neg_apply, cplx, Matrix.map_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, reduceCtorEq, ite_false,
      neg_mul] at h
    have e : ∑ x, -(z * (if ν = x then 1 else 0) * G Sig X z (Sum.inr x) (Sum.inl j)) =
        -(z * G Sig X z (Sum.inr ν) (Sum.inl j)) := by
      simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    rw [e] at h
    have h' : ∑ k, (X k ν : ℂ) * G Sig X z (Sum.inl k) (Sum.inl j) -
        z * G Sig X z (Sum.inr ν) (Sum.inl j) = 0 := by
      rw [← h]; simp [sub_eq_add_neg]
    exact sub_eq_zero.1 h'
  have hAre : ∀ i, -(∑ k, P i k * u k) + ∑ ν, X i ν * sr ν = if i = j then 1 else 0 := by
    intro i
    have h := congrArg Complex.re (hA i)
    simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.re_ofReal_mul] at h
    rw [h]; split_ifs <;> simp
  have hAim : ∀ i, -(∑ k, P i k * w k) + ∑ ν, X i ν * si ν = 0 := by
    intro i
    have h := congrArg Complex.im (hA i)
    simp only [Complex.add_im, Complex.neg_im, Complex.im_sum, Complex.im_ofReal_mul] at h
    rw [h]; split_ifs <;> simp
  have hBre : ∀ ν, ∑ k, X k ν * u k = z.re * sr ν - z.im * si ν := by
    intro ν
    have h := congrArg Complex.re (hB ν)
    rw [Complex.re_sum, Complex.mul_re] at h
    simp only [Complex.re_ofReal_mul] at h
    exact h
  have hBim : ∀ ν, ∑ k, X k ν * w k = z.re * si ν + z.im * sr ν := by
    intro ν
    have h := congrArg Complex.im (hB ν)
    rw [Complex.im_sum, Complex.mul_im] at h
    simp only [Complex.im_ofReal_mul] at h
    rw [h]
  -- the two real identities
  set Q : ℝ := u ⬝ᵥ P *ᵥ u + w ⬝ᵥ P *ᵥ w with hQ
  set Ssq : ℝ := ∑ ν, (sr ν ^ 2 + si ν ^ 2) with hS
  have hXs : ∀ (a : m → ℝ) (b : n → ℝ), ∑ i, a i * ∑ ν, X i ν * b ν =
      ∑ ν, b ν * ∑ k, X k ν * a k := by
    intro a b
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hPd : ∀ a b : m → ℝ, a ⬝ᵥ P *ᵥ b = ∑ i, a i * ∑ k, P i k * b k := by
    intro a b; simp [dotProduct, mulVec]
  have hT : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.inv.1.eq
  have hsym : w ⬝ᵥ P *ᵥ u = u ⬝ᵥ P *ᵥ w := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]
  have hT1 : ∑ i, u i * ∑ ν, X i ν * sr ν = ∑ ν, sr ν * (z.re * sr ν - z.im * si ν) := by
    rw [hXs]; exact Finset.sum_congr rfl fun ν _ => by rw [hBre]
  have hT2 : ∑ i, w i * ∑ ν, X i ν * si ν = ∑ ν, si ν * (z.re * si ν + z.im * sr ν) := by
    rw [hXs]; exact Finset.sum_congr rfl fun ν _ => by rw [hBim]
  have hT3 : ∑ i, w i * ∑ ν, X i ν * sr ν = ∑ ν, sr ν * (z.re * si ν + z.im * sr ν) := by
    rw [hXs]; exact Finset.sum_congr rfl fun ν _ => by rw [hBim]
  have hT4 : ∑ i, u i * ∑ ν, X i ν * si ν = ∑ ν, si ν * (z.re * sr ν - z.im * si ν) := by
    rw [hXs]; exact Finset.sum_congr rfl fun ν _ => by rw [hBre]
  have hT12 : ∑ ν, sr ν * (z.re * sr ν - z.im * si ν) + ∑ ν, si ν * (z.re * si ν + z.im * sr ν)
      = z.re * Ssq := by
    rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hT34 : ∑ ν, sr ν * (z.re * si ν + z.im * sr ν) - ∑ ν, si ν * (z.re * sr ν - z.im * si ν)
      = z.im * Ssq := by
    rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hU : ∑ i, u i * (-(∑ k, P i k * u k) + ∑ ν, X i ν * sr ν) =
      -(u ⬝ᵥ P *ᵥ u) + ∑ i, u i * ∑ ν, X i ν * sr ν := by
    rw [hPd, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hW : ∑ i, w i * (-(∑ k, P i k * w k) + ∑ ν, X i ν * si ν) =
      -(w ⬝ᵥ P *ᵥ w) + ∑ i, w i * ∑ ν, X i ν * si ν := by
    rw [hPd, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hW' : ∑ i, w i * (-(∑ k, P i k * u k) + ∑ ν, X i ν * sr ν) =
      -(w ⬝ᵥ P *ᵥ u) + ∑ i, w i * ∑ ν, X i ν * sr ν := by
    rw [hPd, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hU' : ∑ i, u i * (-(∑ k, P i k * w k) + ∑ ν, X i ν * si ν) =
      -(u ⬝ᵥ P *ᵥ w) + ∑ i, u i * ∑ ν, X i ν * si ν := by
    rw [hPd, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hU0 : ∑ i, u i * (-(∑ k, P i k * u k) + ∑ ν, X i ν * sr ν) = u j := by
    simp only [hAre, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hW0 : ∑ i, w i * (-(∑ k, P i k * w k) + ∑ ν, X i ν * si ν) = 0 := by
    simp only [hAim, mul_zero, Finset.sum_const_zero]
  have hW0' : ∑ i, w i * (-(∑ k, P i k * u k) + ∑ ν, X i ν * sr ν) = w j := by
    simp only [hAre, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hU0' : ∑ i, u i * (-(∑ k, P i k * w k) + ∑ ν, X i ν * si ν) = 0 := by
    simp only [hAim, mul_zero, Finset.sum_const_zero]
  have hE1 : -Q + z.re * Ssq = u j := by
    rw [hQ]; linarith
  have hE2 : z.im * Ssq = w j := by
    linarith
  -- Cauchy–Schwarz with `a = Σ e_j`
  set a : m → ℝ := fun i => Sig j i
  have hSP : Sig * P = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hrow : ∀ b : m → ℝ, a ⬝ᵥ P *ᵥ b = b j := by
    intro b
    have h := congrFun (congrArg (· *ᵥ b) hSP) j
    simp only [← mulVec_mulVec, one_mulVec] at h
    rw [← h]; rfl
  have hPS := hSig.inv.posSemidef
  have hcu := prelimBounds_cs hPS a u
  have hcw := prelimBounds_cs hPS a w
  rw [hrow u, hrow a] at hcu
  rw [hrow w, hrow a] at hcw
  have hnorm : ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ ^ 2 = u j ^ 2 + w j ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hQ' : z.im * Q = z.re * w j - z.im * u j := by
    linear_combination (-z.im) * hE1 + z.re * hE2
  have hzn : (z.re * w j - z.im * u j) ^ 2 ≤ ‖z‖ ^ 2 * ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ ^ 2 := by
    rw [hnorm, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re * u j + z.im * w j)]
  have hzQ : z.im * Q ≤ ‖z‖ * ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ := by
    rw [hQ']
    have h0 : 0 ≤ ‖z‖ * ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ := by positivity
    rw [← mul_pow] at hzn
    nlinarith
  have hjj : 0 < Sig j j := hSig.diag_pos
  have hQS : ‖G Sig X z (Sum.inl j) (Sum.inl j)‖ ^ 2 ≤ Sig j j * Q := by
    rw [hnorm, hQ, mul_add]; linarith
  rw [le_div_iff₀ hz]
  exact prelimBounds_last (norm_nonneg _) hz hjj (norm_nonneg z) hQS hzQ

/-- The `𝓘_M` diagonal of the minor: `|G^{(μ)}_{jj}| ≤ |z| Σ_{jj}/η`. -/
private theorem prelimBounds_Gmu_inl_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (j : Fin M) :
    ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖ ≤ ‖z‖ * Sig j j / z.im := by
  set S : Finset (Fin M ⊕ Fin N) := {Sum.inr μ} with hSdef
  have hS : ∀ i, Sum.inl i ∉ S := by simp [hSdef]
  have hG : Gmu Sig A z μ = extend S (G (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val)
      (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) z) :=
    Gm_eq_extend_G_of_subset_N Sig A z S hS
  rw [hG]
  simp only [extend, hS j, dite_false]
  exact prelimBounds_G_inl_le (hSig.submatrix Subtype.val_injective) _ hz ⟨j, hS j⟩

/-- `Im G^{(μ)}_{jj} ≥ 0`. -/
private theorem prelimBounds_Gmu_im_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    0 ≤ (ent (Gmu Sig A z μ) x x).im := by
  have h := GMaa4_minor hSig A hz {Sum.inr μ} x
  have h0 : 0 ≤ (ent (Gm Sig A z {Sum.inr μ}) x x).im / z.im := by
    rw [← h]; positivity
  have := mul_nonneg h0 hz.le
  rwa [div_mul_cancel₀ _ hz.ne'] at this


section Measurability

/-- The determinant of a complex matrix with measurable entries is measurable. -/
private theorem prelimBounds_measurable_det {α : Type*} [MeasurableSpace α] {n : Type*}
    [Fintype n] [DecidableEq n] {B : α → Matrix n n ℂ} (hB : ∀ i j, Measurable fun a => B a i j) :
    Measurable fun a => (B a).det := by
  have hc : Continuous fun f : n → n → ℂ => (Matrix.of f).det :=
    Continuous.matrix_det (A := fun f : n → n → ℂ => Matrix.of f) continuous_id
  exact hc.measurable.comp (Measurable.of_eval fun i => Measurable.of_eval fun j => hB i j)

/-- The entries of the inverse of a complex matrix with measurable entries are measurable. -/
private theorem prelimBounds_measurable_inv {α : Type*} [MeasurableSpace α] {n : Type*}
    [Fintype n] [DecidableEq n] {B : α → Matrix n n ℂ} (hB : ∀ i j, Measurable fun a => B a i j)
    (i j : n) : Measurable fun a => (B a)⁻¹ i j := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine (prelimBounds_measurable_det hB).inv.mul ?_
  have hc : Continuous fun f : n → n → ℂ => (Matrix.of f).adjugate i j :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Continuous.matrix_adjugate (A := fun f : n → n → ℂ => Matrix.of f) continuous_id))
  exact hc.measurable.comp (Measurable.of_eval fun i => Measurable.of_eval fun j => hB i j)

/-- The entries of `G^{(T)}` are measurable functions of the matrix. -/
private theorem prelimBounds_measurable_Gm (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (s t : Fin M ⊕ Fin N) :
    Measurable fun B : Matrix (Fin M) (Fin N) ℝ => Gm Sig B z T s t := by
  have hX : ∀ i μ, Measurable fun B : Matrix (Fin M) (Fin N) ℝ => B i μ := fun i μ =>
    (measurable_pi_apply μ).comp (measurable_pi_apply i)
  simp only [Gm, minorG]
  by_cases hs : s ∈ T
  · simp only [hs, dite_true]
    exact measurable_const
  · by_cases ht : t ∈ T
    · simp only [hs, ht, dite_true, dite_false]
      exact measurable_const
    · simp only [hs, ht, dite_false]
      refine prelimBounds_measurable_inv (fun u v => ?_) _ _
      rcases u with ⟨u | u, hu⟩ <;> rcases v with ⟨v | v, hv⟩ <;>
        simp only [minorH, H, linH, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
          fromBlocks_apply₂₁, fromBlocks_apply₂₂, cplx, map_apply, transpose_apply] <;>
        first
        | exact measurable_const
        | exact Complex.measurable_ofReal.comp (hX _ _)

/-- The column `μ` of `X` is a row family. -/
private theorem prelimBounds_rowAssumption {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N) :
    RowAssumption C N (fun j ω => X ω j μ) where
  measurable j := hX.measurable j μ
  indep := hX.indep.precomp (g := fun j : Fin M => (j, μ)) fun a b h => by
    simpa using congrArg Prod.fst h
  mean j := hX.mean j μ
  var j := hX.var j μ
  integrable_moment p j := hX.integrable_moment p j μ
  moment p j := hX.moment p j μ

private theorem prelimBounds_measurable_updCol {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N) :
    Measurable fun ω => updCol (X ω) μ 0 := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun ν => ?_
  by_cases h : ν = μ
  · simp only [updCol, h, ite_true]; exact measurable_const
  · simp only [updCol, h, ite_false]; exact hX.measurable i ν

/-- The column `μ` of `X` is independent of `X^{(μ)}` (column `μ` replaced by `0`). -/
private theorem prelimBounds_indep {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N) :
    IndepFun (fun ω j => X ω j μ) (fun ω => updCol (X ω) μ 0) ℙ := by
  set P : Finset (Fin M × Fin N) := Finset.univ.filter (fun p => p.2 = μ) with hPdef
  set Q : Finset (Fin M × Fin N) := Finset.univ.filter (fun p => p.2 ≠ μ) with hQdef
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [hPdef, hQdef, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hq hp
  have hind := hX.indep.indepFun_finset P Q hdisj (fun p => hX.measurable p.1 p.2)
  let φ : (P → ℝ) → (Fin M → ℝ) := fun y j => y ⟨(j, μ), by simp [hPdef]⟩
  let ψ : (Q → ℝ) → Matrix (Fin M) (Fin N) ℝ :=
    fun y i ν => if h : ν = μ then 0 else y ⟨(i, ν), by simp [hQdef, h]⟩
  have hφ : Measurable φ := Measurable.of_eval fun j => measurable_pi_apply _
  have hψ : Measurable ψ := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun ν => ?_
    by_cases h : ν = μ
    · simp only [ψ, h, dite_true]; exact measurable_const
    · simp only [ψ, h, dite_false]; exact measurable_pi_apply _
  have e1 : (fun ω j => X ω j μ) = φ ∘ fun ω (p : P) => X ω p.1.1 p.1.2 := rfl
  have e2 : (fun ω => updCol (X ω) μ 0) = ψ ∘ fun ω (q : Q) => X ω q.1.1 q.1.2 := by
    funext ω i ν
    show updCol (X ω) μ 0 i ν = ψ (fun q => X ω q.1.1 q.1.2) i ν
    by_cases h : ν = μ
    · simp [ψ, updCol, h]
    · simp [ψ, updCol, h]
  rw [e1, e2]
  exact hind.comp hφ hψ

end Measurability


/-! ### `Σ̲`, `v̄`, `Π` -/

private theorem prelimBounds_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ∃ U : Matrix (Fin M) (Fin M) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      Sig = U * diagonal (specOf Sig) * Uᵀ ∧ ∀ i, 0 < specOf Sig i := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hSig.1
  have h₁ : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h₂ : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  refine ⟨U, h₂, h₁, ?_, fun i => ?_⟩
  · rw [← hD]
    simp only [← Matrix.mul_assoc]
    rw [h₂, Matrix.one_mul, Matrix.mul_assoc, h₂, Matrix.mul_one]
  · rw [specOf_eq hSig.1]
    exact hSig.eigenvalues_pos i

private theorem prelimBounds_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem prelimBounds_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem prelimBounds_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := prelimBounds_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, prelimBounds_sum_sq_UT hUU, ← prelimBounds_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem prelimBounds_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := prelimBounds_sumsq_Sig hS (y ∘ Sum.inl)
  have h2 : 0 ≤ ∑ ν, y (Sum.inr ν) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ l, y (Sum.inl l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold testNorm
  rw [← Real.sqrt_sq (inv_pos.2 hτ).le, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  simp only [Function.comp_def] at h1
  have h4 : ∑ ν, y (Sum.inr ν) ^ 2 ≤ τ⁻¹ ^ 2 * ∑ ν, y (Sum.inr ν) ^ 2 :=
    le_mul_of_one_le_left h2 (one_le_pow₀ hτi)
  rw [mul_add]
  exact add_le_add h1 h4

/-- `v̄` of `Σ̲ y` is `y`. -/
private theorem prelimBounds_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]


/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem prelimBounds_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (l i : Fin M) :
    (1 + w • cplx Sig)⁻¹ l i = ∑ k, (U l k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
    have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
      simp only [cplx]
      rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
        diagonal_map (map_zero _)]
      rfl
    have e2 : diagonal (fun i => 1 + (σ i : ℂ) * w) =
        1 + w • diagonal (fun i => (σ i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_smul, diagonal_add]
      congr 1
      funext i
      simp [mul_comm]
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, c₂, Matrix.mul_smul,
      Matrix.smul_mul, e1]
  have hinv : (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hT]
    have hd : diagonal (fun i => 1 + (σ i : ℂ) * w) *
        diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hw i)
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => 1 + (σ i : ℂ) * w) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [c₁, Matrix.mul_one, hd, Matrix.mul_one, c₂]
  rw [hinv]
  simp [Matrix.mul_apply, cplx, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

private theorem prelimBounds_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem prelimBounds_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem prelimBounds_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [prelimBounds_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := prelimBounds_diag hSig
    have hw0 : ∀ k, 1 + (specOf Sig k : ℂ) * w ≠ 0 := fun k h0 => by
      have := hOne k
      rw [h0, norm_zero] at this
      linarith
    set xM : Fin M → ℝ := fun j => x (Sum.inl j) with hxM
    have hSS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
    have hy : Sig *ᵥ (Sig⁻¹ *ᵥ xM) = xM := by rw [mulVec_mulVec, hSS, one_mulVec]
    have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
    have hsym : ∀ j l, Sig j l = Sig l j := fun j l => by
      conv_lhs => rw [← hT]
      rfl
    have e1 : ∑ j, ((vbar Sig x (Sum.inl j) : ℝ) : ℂ) * (cplx Sig * (1 + w • cplx Sig)⁻¹) j i =
        ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : xM l = ∑ j, Sig l j * (Sig⁻¹ *ᵥ xM) j := by
        conv_lhs => rw [← hy]
        rfl
      rw [e, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [vbar, Sum.elim_inl, Function.comp_def, cplx, Matrix.map_apply,
        Complex.ofReal_mul, hsym l j, Complex.coe_algebraMap, ← hxM]
      ring
    have e2 : ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i =
        ∑ k, (((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
      simp only [prelimBounds_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mulVec, dotProduct, transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2]
    have hb : ∀ k, ‖(((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ)‖ ≤
        c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) := by
      intro k
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_inv]
      have hinv : ‖1 + (specOf Sig k : ℂ) * w‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne k)
      have := mul_le_mul_of_nonneg_left hinv (abs_nonneg ((Uᵀ *ᵥ xM) k))
      nlinarith [abs_nonneg (U i k), abs_nonneg ((Uᵀ *ᵥ xM) k)]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |(Uᵀ *ᵥ xM) k|)
      (fun k => |U i k|)
    simp only [sq_abs] at hcs
    rw [prelimBounds_sum_sq_UT h₂, prelimBounds_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (prelimBounds_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (prelimBounds_abs_le_testNorm x _)
      (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))


/-- `|⟨v̄, G e_p⟩| ≤ |⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ (Σ̲ e_p)⟩| + max(c⁻¹, K) |v|`. -/
private theorem prelimBounds_G_left {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {z : ℂ} (hwK : ‖mFun N (specOf Sig) z‖ ≤ K)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ + max c⁻¹ K * testNorm x := by
  have e : ent (G Sig A z) (vbar Sig x) (eI p) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig x) (vbar Sig (SigU (n := Fin N) Sig *ᵥ eI p)) +
        ent (PiZ N Sig z) (vbar Sig x) (eI p) := by
    rw [prelimBounds_vbar_SigU hSig, prelimBounds_ent_sub]; ring
  rw [e, ent_vbar_eq_testBilin hSig]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (prelimBounds_pi_bound hSig hc hwK hOne x p))

private theorem prelimBounds_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem prelimBounds_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

private theorem prelimBounds_testNorm_smul {ι : Type*} [Fintype ι] (r : ℝ) (v : ι → ℝ) :
    testNorm (r • v) = |r| * testNorm v := by
  unfold testNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

private theorem prelimBounds_testNorm_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℝ}
    (h : testNorm v = 0) : v = 0 := by
  unfold testNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
  funext s
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h s (Finset.mem_univ _))

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma). -/
private theorem prelimBounds_norm_Sig_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) : ‖Sig‖ ≤ τ⁻¹ := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_pos.2 hτ).le fun x => ?_
  have h := prelimBounds_sumsq_Sig hS (x : Fin M → ℝ)
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (mul_nonneg (inv_pos.2 hτ).le (norm_nonneg x))]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- `Π_μμ = m`. -/
private theorem prelimBounds_PiZ_mu (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (μ : Fin N) :
    PiZ N Sig z (Sum.inr μ) (Sum.inr μ) = mFun N (specOf Sig) z := by
  simp [PiZ, piMat]

/-- `Im G_{xx} ≥ 0`. -/
private theorem prelimBounds_im_G_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ) :
    0 ≤ (ent (G Sig A z) x x).im := by
  have h := GMaa4_unified hSig A hz x
  have h0 : 0 ≤ (ent (G Sig A z) x x).im / z.im := by
    rw [← h]; positivity
  have := mul_nonneg h0 hz.le
  rwa [div_mul_cancel₀ _ hz.ne'] at this

/-! ### The absorption step of (im_BGB) -/

/-- (im_BGB) absorption: from `W ≤ α I + β`, `a² ≤ L W/n` (BGX_est) and
`I ≤ P' + g(a² + 2a)` (main_identity), with `g L α/n ≤ 1/4`, the product term and the root term
are absorbed into `I/2`. -/
private theorem prelimBounds_chain {W I a g g₁ P' α β L n : ℝ} (hn : 0 < n) (hα : 0 < α)
    (hL : 0 < L) (hg0 : 0 ≤ g) (hg : g ≤ g₁) (hI0 : 0 ≤ I) (hW : W ≤ α * I + β)
    (ha : a ^ 2 ≤ L * W / n) (hIm : I ≤ P' + g * (a ^ 2 + 2 * a))
    (hs : g₁ * L * α / n ≤ 1 / 4) :
    I ≤ 2 * P' + 2 * g₁ * L * β / n + β / (2 * α) + 8 * L * α * g₁ ^ 2 / n := by
  have hLn : 0 ≤ L / n := (div_pos hL hn).le
  have ha2 : a ^ 2 ≤ L * (α * I + β) / n := by
    refine ha.trans ?_
    rw [mul_div_right_comm, mul_div_right_comm L]
    exact mul_le_mul_of_nonneg_left hW hLn
  have hg₁ : 0 ≤ g₁ := hg0.trans hg
  have h1 : g * a ^ 2 ≤ I / 4 + g₁ * L * β / n := by
    have e : g₁ * (L * (α * I + β) / n) = (g₁ * L * α / n) * I + g₁ * L * β / n := by
      field_simp
    calc g * a ^ 2 ≤ g₁ * a ^ 2 := mul_le_mul_of_nonneg_right hg (sq_nonneg _)
      _ ≤ g₁ * (L * (α * I + β) / n) := mul_le_mul_of_nonneg_left ha2 hg₁
      _ = (g₁ * L * α / n) * I + g₁ * L * β / n := e
      _ ≤ (1 / 4) * I + g₁ * L * β / n := by gcongr
      _ = I / 4 + g₁ * L * β / n := by ring
  set s := 4 * L * α / n with hsdef
  have hs0 : 0 < s := by positivity
  have h2 : 2 * (g * a) ≤ a ^ 2 / s + s * g ^ 2 := by
    rw [div_add' _ _ _ hs0.ne', le_div_iff₀ hs0]
    nlinarith [sq_nonneg (a - s * g)]
  have h3 : a ^ 2 / s ≤ I / 4 + β / (4 * α) := by
    calc a ^ 2 / s ≤ (L * (α * I + β) / n) / s := div_le_div_of_nonneg_right ha2 hs0.le
      _ = I / 4 + β / (4 * α) := by rw [hsdef]; field_simp
  have h4 : s * g ^ 2 ≤ 4 * L * α * g₁ ^ 2 / n := by
    rw [hsdef, div_mul_eq_mul_div]
    gcongr
  have hI : I ≤ P' + (I / 4 + g₁ * L * β / n) + (I / 4 + β / (4 * α)) +
      4 * L * α * g₁ ^ 2 / n := by
    have : g * (a ^ 2 + 2 * a) = g * a ^ 2 + 2 * (g * a) := by ring
    rw [this] at hIm
    linarith
  have e1 : 2 * g₁ * L * β / n = 2 * (g₁ * L * β / n) := by ring
  have e2 : β / (2 * α) = 2 * (β / (4 * α)) := by field_simp; ring
  have e3 : 8 * L * α * g₁ ^ 2 / n = 2 * (4 * L * α * g₁ ^ 2 / n) := by ring
  rw [e1, e2, e3]
  linarith

/-! ### The deterministic consequences on `Θ` -/

/-- Ward identity for the minor at `x`, with `‖Σ‖ ≤ τ⁻¹`, `‖XᵀX‖ ≤ C_n` and
`x_Mᵀ Σ² x_M ≤ τ⁻²`: `∑_j |G^{(μ)}_{xj}|² ≤ 2τ⁻² C_n Im G^{(μ)}_{xx}/η + 2τ⁻²`. -/
private theorem prelimBounds_ward {τ Cn : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hSn : ‖Sig‖ ≤ τ⁻¹) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N)
    (x : Fin M ⊕ Fin N → ℝ) (hCn : ‖Aᵀ * A‖ ≤ Cn)
    (hq : (x ∘ Sum.inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ Sum.inl) ≤ τ⁻¹ ^ 2) :
    ∑ j, ‖colC Sig A z x μ j‖ ^ 2 ≤
      2 * τ⁻¹ ^ 2 * Cn / z.im * (ent (Gmu Sig A z μ) x x).im + 2 * τ⁻¹ ^ 2 := by
  have h := ward_minor_M hSig A hz μ x
  have hI := prelimBounds_Gmu_im_nonneg hSig A hz μ x
  have hS2 : ‖Sig‖ ^ 2 ≤ τ⁻¹ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hSn 2
  refine h.trans (add_le_add ?_ (by linarith))
  refine mul_le_mul_of_nonneg_right ?_ hI
  refine div_le_div_of_nonneg_right ?_ hz.le
  have := mul_le_mul hS2 hCn (norm_nonneg _) (by positivity)
  linarith

/-- (im_BGB) before absorption: `Im G^{(μ)}_{xx} ≤ Im G_{xx} + |G_μμ| (|a_x|² + 2|a_x|)` for
`|x(μ)| ≤ 1`, from (main_identity) and `Im G_μμ ≥ 0`. -/
private theorem prelimBounds_Ibound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N)
    (x : Fin M ⊕ Fin N → ℝ) (hxμ : |x (Sum.inr μ)| ≤ 1) :
    (ent (Gmu Sig A z μ) x x).im ≤ (ent (G Sig A z) x x).im +
      ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ *
        (‖linForm (colC Sig A z x μ) (fun j => A j μ)‖ ^ 2 +
          2 * ‖linForm (colC Sig A z x μ) (fun j => A j μ)‖) := by
  have hm := prelimBounds_main hSig A hz μ x x
  rw [prelimBounds_rowC_eq hSig A hz μ x] at hm
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ) with hg
  set a := linForm (colC Sig A z x μ) (fun j => A j μ) with ha
  set r := x (Sum.inr μ) with hr
  have e : ent (Gmu Sig A z μ) x x = ent (G Sig A z) x x - ((r * r : ℝ) : ℂ) * g - g * a * a +
      ((2 * r : ℝ) : ℂ) * (g * a) := by
    rw [hm]; push_cast; ring
  have hgim : 0 ≤ g.im := by
    have := prelimBounds_im_G_nonneg hSig A hz (eI (Sum.inr μ))
    rwa [ent_eI_eI] at this
  rw [e, Complex.add_im, Complex.sub_im, Complex.sub_im, Complex.im_ofReal_mul,
    Complex.im_ofReal_mul]
  have t1 : 0 ≤ r * r * g.im := mul_nonneg (mul_self_nonneg r) hgim
  have t2 : -(g * a * a).im ≤ ‖g‖ * ‖a‖ ^ 2 := by
    have := Complex.abs_im_le_norm (g * a * a)
    rw [norm_mul, norm_mul] at this
    nlinarith [neg_abs_le (g * a * a).im]
  have t3 : 2 * r * (g * a).im ≤ ‖g‖ * (2 * ‖a‖) := by
    have h1 := Complex.abs_im_le_norm (g * a)
    rw [norm_mul] at h1
    have h2 : |2 * r * (g * a).im| ≤ 2 * 1 * (‖g‖ * ‖a‖) := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hxμ (by norm_num)) h1 (abs_nonneg _)
        (by norm_num)
    have := le_abs_self (2 * r * (g * a).im)
    linarith
  nlinarith

/-- (BGX_est) and (im_BGB) for one vector `x`: `∑_j |G^{(μ)}_{xj}|² ≤ N b²` and `|a_x| ≤ b`. -/
private theorem prelimBounds_xbound {τ Cn lam P BI g₁ b : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (hSn : ‖Sig‖ ≤ τ⁻¹) (hτ : 0 < τ) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) (hN : (0 : ℝ) < N) (hCn0 : 0 < Cn)
    (hCn : ‖Aᵀ * A‖ ≤ Cn) (hlam : 0 < lam)
    (hq : (x ∘ Sum.inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ Sum.inl) ≤ τ⁻¹ ^ 2)
    (hxμ : |x (Sum.inr μ)| ≤ 1) (hP : (ent (G Sig A z) x x).im ≤ P)
    (hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ g₁)
    (ha : ‖linForm (colC Sig A z x μ) (fun j => A j μ)‖ ≤ lam * ldeLinBound N (colC Sig A z x μ))
    (hs : g₁ * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im) / N ≤ 1 / 4)
    (hBI : BI = 2 * P + 2 * g₁ * lam ^ 2 * (2 * τ⁻¹ ^ 2) / N +
      2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / z.im)) +
      8 * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im) * g₁ ^ 2 / N)
    (n2a : 2 * τ⁻¹ ^ 2 * Cn / z.im * BI + 2 * τ⁻¹ ^ 2 ≤ N * b ^ 2)
    (n2b : lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im * BI + 2 * τ⁻¹ ^ 2) / N ≤ b ^ 2) (hb0 : 0 ≤ b) :
    ∑ j, ‖colC Sig A z x μ j‖ ^ 2 ≤ N * b ^ 2 ∧
      ‖linForm (colC Sig A z x μ) (fun j => A j μ)‖ ≤ b := by
  set α := 2 * τ⁻¹ ^ 2 * Cn / z.im with hα
  set β := 2 * τ⁻¹ ^ 2 with hβ
  set W := ∑ j, ‖colC Sig A z x μ j‖ ^ 2 with hW
  set I := (ent (Gmu Sig A z μ) x x).im with hIdef
  set a := ‖linForm (colC Sig A z x μ) (fun j => A j μ)‖ with hadef
  have hα0 : 0 < α := by positivity
  have hWb := prelimBounds_ward hSig hSn A hz μ x hCn hq
  have hI0 : 0 ≤ I := prelimBounds_Gmu_im_nonneg hSig A hz μ x
  have ha2 : a ^ 2 ≤ lam ^ 2 * W / N := by
    have h0 : 0 ≤ a := norm_nonneg _
    have hsq : (lam * ldeLinBound N (colC Sig A z x μ)) ^ 2 = lam ^ 2 * W / N := by
      rw [mul_pow, ldeLinBound, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity),
        ← Finset.sum_div, mul_div_assoc]
    rw [← hsq]
    exact pow_le_pow_left₀ h0 ha 2
  have hIm := prelimBounds_Ibound hSig A hz μ x hxμ
  have hIm' : I ≤ P + ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ * (a ^ 2 + 2 * a) := by
    have := hIm; rw [← hIdef, ← hadef] at this; linarith
  have hch := prelimBounds_chain hN hα0 (by positivity : 0 < lam ^ 2) (norm_nonneg _) hg hI0 hWb
    ha2 hIm' hs
  rw [← hBI] at hch
  have hWB : W ≤ α * BI + β := hWb.trans (by gcongr)
  refine ⟨hWB.trans n2a, ?_⟩
  have : a ^ 2 ≤ b ^ 2 := by
    refine ha2.trans (le_trans ?_ n2b)
    rw [mul_div_assoc, mul_div_assoc]
    gcongr
  have h0 : 0 ≤ a := norm_nonneg _
  nlinarith

/-- `Z_μ = Q_μ − Y_μ` splits into its off-diagonal and diagonal parts. -/
private theorem prelimBounds_Z_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) :
    Qmu Sig A z μ - Ymu Sig A z μ =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
          ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl j) * ((A j μ : ℝ) : ℂ) +
        ∑ i, Gmu Sig A z μ (Sum.inl i) (Sum.inl i) *
          (((A i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ)) := by
  have hA : updCol A μ (fun j => A j μ) = A := by
    funext j ν
    by_cases h : ν = μ
    · subst h; simp [updCol]
    · simp [updCol, h]
  have hQ := Qmu_updCol Sig A z μ (fun j => A j μ)
  rw [hA] at hQ
  rw [hQ, Ymu]
  have e : ∀ i, ∑ j, ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl j) *
      ((A j μ : ℝ) : ℂ) = ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl i) *
        ((A i μ : ℝ) : ℂ) + ∑ j ∈ Finset.univ.erase i, ((A i μ : ℝ) : ℂ) *
          Gmu Sig A z μ (Sum.inl i) (Sum.inl j) * ((A j μ : ℝ) : ℂ) := fun i =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have e3 : ∀ i, ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl i) * ((A i μ : ℝ) : ℂ) =
      Gmu Sig A z μ (Sum.inl i) (Sum.inl i) * ((A i μ : ℝ) : ℂ) ^ 2 := fun i => by ring
  have e2 : ∀ i, Gmu Sig A z μ (Sum.inl i) (Sum.inl i) * (1 / ((N : ℝ) : ℂ)) =
      (N : ℂ)⁻¹ * Gmu Sig A z μ (Sum.inl i) (Sum.inl i) := fun i => by push_cast; ring
  simp only [e, e3, Finset.sum_add_distrib, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, e2]
  abel

/-- `|G_μμ − Π_μμ| ≤ E` and `|G_μμ| ≤ E + K_m` from (a_priori_1) at `e_μ`. -/
private theorem prelimBounds_g_le {Km E : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N)
    (hmK : ‖mFun N (specOf Sig) z‖ ≤ Km)
    (h4 : ‖testBilin (eI (Sum.inr μ)) (lawMat Sig A z) (eI (Sum.inr μ))‖ ≤ E) :
    ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ E ∧
      ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ E + Km := by
  have hGP : G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ) =
      testBilin (eI (Sum.inr μ)) (lawMat Sig A z) (eI (Sum.inr μ)) := by
    have := ent_vbar_eq_testBilin hSig A z (eI (Sum.inr μ)) (eI (Sum.inr μ))
    rwa [prelimBounds_vbar_eI_inr, ent_eI_eI, Matrix.sub_apply] at this
  have hPi : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km := by
    rw [prelimBounds_PiZ_mu]; exact hmK
  refine ⟨hGP ▸ h4, ?_⟩
  have := norm_add_le (G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
    (PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
  rw [sub_add_cancel, hGP] at this
  linarith

/-- `v̄_Mᵀ Σ² v̄_M = |v_M|² ≤ τ⁻²` (no lower bound on `Σ` enters). -/
private theorem prelimBounds_qv {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hτi : 1 ≤ τ⁻¹) (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    (vbar Sig v ∘ Sum.inl) ⬝ᵥ (Sig * Sig) *ᵥ (vbar Sig v ∘ Sum.inl) ≤ τ⁻¹ ^ 2 := by
  have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hSS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have e1 : vbar Sig v ∘ Sum.inl = Sig⁻¹ *ᵥ (v ∘ Sum.inl) := by funext i; simp [vbar]
  have e2 : (Sig * Sig) *ᵥ (Sig⁻¹ *ᵥ (v ∘ Sum.inl)) = Sig *ᵥ (v ∘ Sum.inl) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, hSS, Matrix.mul_one]
  have e3 : (Sig⁻¹ *ᵥ (v ∘ Sum.inl)) ⬝ᵥ (Sig *ᵥ (v ∘ Sum.inl)) =
      (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, mulVec_mulVec, hSS, one_mulVec,
      dotProduct_comm]
  rw [e1, e2, e3]
  have h0 : (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) ≤ 1 := by
    have := prelimBounds_sqrt_inl_le v
    rw [hv] at this
    have h1 : (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) = ∑ j, v (Sum.inl j) ^ 2 := by
      simp [dotProduct, sq]
    rw [h1]
    exact Real.sqrt_le_one.mp this
  have : (1 : ℝ) ≤ τ⁻¹ ^ 2 := one_le_pow₀ hτi
  linarith

/-- `(Σ²)_{jj} = |Σ e_j|² ≤ τ⁻²`. -/
private theorem prelimBounds_qe {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (j : Fin M) :
    ((eI (Sum.inl j : Fin M ⊕ Fin N)) ∘ Sum.inl : Fin M → ℝ) ⬝ᵥ (Sig * Sig) *ᵥ
      ((eI (Sum.inl j : Fin M ⊕ Fin N)) ∘ Sum.inl) ≤ τ⁻¹ ^ 2 := by
  have hT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hS.posDef.1.eq
  set e : Fin M → ℝ := (eI (Sum.inl j : Fin M ⊕ Fin N)) ∘ Sum.inl with hedef
  have e1 : e ⬝ᵥ (Sig * Sig) *ᵥ e = (Sig *ᵥ e) ⬝ᵥ (Sig *ᵥ e) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hT]
  rw [e1]
  have h := prelimBounds_sumsq_Sig hS e
  have h1 : ∑ l, e l ^ 2 = 1 := by
    simp [hedef, eI, Pi.single_apply, Finset.sum_ite_eq']
  rw [h1, mul_one] at h
  simpa [dotProduct, sq] using h

/-- The bracket `[G_{v̄j}]^0` of (G_sigma_bound):
`|G^{(μ)}_{v̄j}| ≤ τ⁻¹E + max(c⁻¹, K_m) + 2(E + K_m)`. -/
private theorem prelimBounds_entvj {τ c Km E : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (hc : 0 < c) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (μ : Fin N) (j : Fin M)
    (hmK : ‖mFun N (specOf Sig) z‖ ≤ Km)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖) (hE0 : 0 ≤ E)
    (h2 : ‖testBilin v (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))‖ ≤
      E * testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))
    (hSe : testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) ≤ τ⁻¹)
    (hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ E + Km)
    (hav : ‖linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)‖ ≤ 1)
    (haj : ‖linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤ 1)
    (hxv : |vbar Sig v (Sum.inr μ)| ≤ 1) :
    ‖colC Sig A z (vbar Sig v) μ j‖ ≤ τ⁻¹ * E + max c⁻¹ Km + 2 * (E + Km) := by
  have hGvj : ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl j))‖ ≤ τ⁻¹ * E + max c⁻¹ Km := by
    have h := prelimBounds_G_left hSig hc hmK hOne A v (Sum.inl j)
    rw [hv, mul_one] at h
    refine h.trans (add_le_add (h2.trans ?_) le_rfl)
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hSe hE0
  have hm := prelimBounds_main hSig A hz μ (vbar Sig v) (eI (Sum.inl j))
  rw [prelimBounds_rowC_eq hSig A hz μ] at hm
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ)
  set a := linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)
  set aj := linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)
  set ν : ℂ := ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ)
  have e : colC Sig A z (vbar Sig v) μ j =
      ent (G Sig A z) (vbar Sig v) (eI (Sum.inl j)) - g * a * aj + ν * g * aj := by
    rw [hm, colC]; simp [eI]; ring
  rw [e]
  have hν : ‖ν‖ ≤ 1 := by rw [Complex.norm_real]; exact hxv
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have t1 : ‖g * a * aj‖ ≤ ‖g‖ := by
    rw [norm_mul, norm_mul]
    calc ‖g‖ * ‖a‖ * ‖aj‖ ≤ ‖g‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hav hg0) haj (norm_nonneg _) (by positivity)
      _ = ‖g‖ := by ring
  have t2 : ‖ν * g * aj‖ ≤ ‖g‖ := by
    rw [norm_mul, norm_mul]
    calc ‖ν‖ * ‖g‖ * ‖aj‖ ≤ 1 * ‖g‖ * 1 :=
          mul_le_mul (mul_le_mul hν le_rfl hg0 zero_le_one) haj (norm_nonneg _) (by positivity)
      _ = ‖g‖ := by ring
  have := norm_add_le (ent (G Sig A z) (vbar Sig v) (eI (Sum.inl j)) - g * a * aj) (ν * g * aj)
  have := norm_sub_le (ent (G Sig A z) (vbar Sig v) (eI (Sum.inl j))) (g * a * aj)
  linarith

/-- `|G^{(μ)}_{jk}| ≤ τ⁻²E + τ⁻¹ max(c⁻¹, K_m) + (E + K_m)` (main_identity). -/
private theorem prelimBounds_entjk {τ c Km E : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (hc : 0 < c) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im)
    (μ : Fin N) (j k : Fin M) (hmK : ‖mFun N (specOf Sig) z‖ ≤ Km) (hKm : 0 ≤ Km)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖) (hE0 : 0 ≤ E)
    (hτ0 : 0 ≤ τ⁻¹)
    (h3 : ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) (lawMat Sig A z)
      (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k))‖ ≤
      E * testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k)))
    (hSej : testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) ≤ τ⁻¹)
    (hSek : testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k)) ≤ τ⁻¹)
    (hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ E + Km)
    (haj : ‖linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤ 1)
    (hak : ‖linForm (colC Sig A z (eI (Sum.inl k)) μ) (fun k => A k μ)‖ ≤ 1) :
    ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ≤
      τ⁻¹ ^ 2 * E + τ⁻¹ * max c⁻¹ Km + (E + Km) := by
  have hmx : 0 ≤ max c⁻¹ Km := le_trans hKm (le_max_right _ _)
  have hk0 : 0 ≤ testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k)) := Real.sqrt_nonneg _
  have hGjk : ‖ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl k))‖ ≤
      τ⁻¹ ^ 2 * E + τ⁻¹ * max c⁻¹ Km := by
    have h := prelimBounds_G_left hSig hc hmK hOne A (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))
      (Sum.inl k)
    rw [prelimBounds_vbar_SigU hSig] at h
    refine h.trans (add_le_add (h3.trans ?_) ?_)
    · have := mul_le_mul hSej hSek hk0 hτ0
      calc E * testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) *
            testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k))
          = E * (testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) *
            testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k))) := by ring
        _ ≤ E * (τ⁻¹ * τ⁻¹) := mul_le_mul_of_nonneg_left this hE0
        _ = τ⁻¹ ^ 2 * E := by ring
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right hSej hmx
  have hm := prelimBounds_main hSig A hz μ (eI (Sum.inl j)) (eI (Sum.inl k))
  rw [prelimBounds_rowC_eq hSig A hz μ, ent_eI_eI (Gmu Sig A z μ)] at hm
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ)
  set aj := linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)
  set ak := linForm (colC Sig A z (eI (Sum.inl k)) μ) (fun k => A k μ)
  have e : Gmu Sig A z μ (Sum.inl j) (Sum.inl k) =
      ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl k)) - g * aj * ak := by
    rw [hm]; simp [eI]
  rw [e]
  have t1 : ‖g * aj * ak‖ ≤ ‖g‖ := by
    rw [norm_mul, norm_mul]
    calc ‖g‖ * ‖aj‖ * ‖ak‖ ≤ ‖g‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left haj (norm_nonneg _)) hak (norm_nonneg _)
            (by positivity)
      _ = ‖g‖ := by ring
  have := norm_sub_le (ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl k))) (g * aj * ak)
  linarith

/-- (whA_rough3) at `n = 0`, `σ = 0`: `|A(w₀, 0)| ≤ 2E + 3(E + K_m)`. -/
private theorem prelimBounds_entvv {Km E b : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (hb : b ≤ 1)
    (h1 : ‖testBilin v (lawMat Sig A z) v‖ ≤ E)
    (hGP : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ E)
    (hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ E + Km)
    (hav : ‖linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)‖ ≤ b)
    (hxv : |vbar Sig v (Sum.inr μ)| ≤ 1) :
    ‖emptyScal Sig A z v μ 0‖ ≤ 2 * E + 3 * (E + Km) := by
  rw [prelimBounds_emptyScal_eq hSig A hz v μ, prelimBounds_rowC_eq hSig A hz μ,
    ent_vbar_eq_testBilin hSig]
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ)
  set a := linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)
  set ν : ℂ := ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ)
  have hν : ‖ν‖ ≤ 1 := by rw [Complex.norm_real]; exact hxv
  have ha1 : ‖a‖ ≤ 1 := hav.trans hb
  have hE : 0 ≤ E := (norm_nonneg _).trans h1
  have t1 : ‖ν ^ 2 * (g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))‖ ≤ E := by
    rw [norm_mul, norm_pow]
    have : ‖ν‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hν
    calc ‖ν‖ ^ 2 * ‖g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ 1 * E :=
          mul_le_mul this hGP (norm_nonneg _) zero_le_one
      _ = E := one_mul E
  have t2 : ‖a * a - ν * (a + a)‖ ≤ 3 := by
    have h1' : ‖a * a‖ ≤ 1 := by
      rw [norm_mul]
      calc ‖a‖ * ‖a‖ ≤ 1 * 1 := mul_le_mul ha1 ha1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h2' : ‖ν * (a + a)‖ ≤ 2 := by
      rw [norm_mul]
      have : ‖a + a‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
      calc ‖ν‖ * ‖a + a‖ ≤ 1 * 2 := mul_le_mul hν this (norm_nonneg _) zero_le_one
        _ = 2 := one_mul 2
    have := norm_sub_le (a * a) (ν * (a + a))
    linarith
  have t3 : ‖g * (a * a - ν * (a + a))‖ ≤ 3 * (E + Km) := by
    rw [norm_mul]
    calc ‖g‖ * ‖a * a - ν * (a + a)‖ ≤ (E + Km) * 3 :=
          mul_le_mul hg t2 (norm_nonneg _) ((norm_nonneg _).trans hg)
      _ = 3 * (E + Km) := by ring
  have := norm_sub_le (testBilin v (lawMat Sig A z) v -
    ν ^ 2 * (g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))) (g * (a * a - ν * (a + a)))
  have := norm_sub_le (testBilin v (lawMat Sig A z) v)
    (ν ^ 2 * (g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)))
  linarith

/-- `|Y_μ| ≤ τ⁻¹ K₁` when `|G^{(μ)}_{jj}| ≤ K₁`. -/
private theorem prelimBounds_Ybound {τ K₁ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (hN : (0 : ℝ) < N)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (hK₁ : 0 ≤ K₁)
    (hjj : ∀ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖ ≤ K₁) :
    ‖Ymu Sig A z μ‖ ≤ τ⁻¹ * K₁ := by
  unfold Ymu
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖
      ≤ (N : ℝ)⁻¹ * ∑ _j : Fin M, K₁ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hjj j))
          (inv_nonneg.2 hN.le)
    _ = (N : ℝ)⁻¹ * (M * K₁) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (N : ℝ)⁻¹ * (τ⁻¹ * N * K₁) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hK₁) (inv_nonneg.2 hN.le)
    _ = τ⁻¹ * K₁ := by field_simp

/-- The bound on `Z_μ` before (z-Y_bound): `|Z_μ| ≤ 2L (τ⁻¹ N W)^{1/2}/N` from the large
deviation bounds, when every row sum
`∑_k |G^{(μ)}_{jk}|²` is at most `W`. -/
private theorem prelimBounds_Zbound {τ lam Wb : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (hN : (0 : ℝ) < N)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (hlam : 0 < lam) (hWb : 0 ≤ Wb)
    (hW : ∀ j, ∑ k, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ^ 2 ≤ Wb)
    (h10 : ‖∑ i, ∑ j ∈ Finset.univ.erase i,
      ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl j) * ((A j μ : ℝ) : ℂ)‖ ≤
      lam * ldeOffBound N (fun i j => Gmu Sig A z μ (Sum.inl i) (Sum.inl j)))
    (h11 : ‖∑ i, Gmu Sig A z μ (Sum.inl i) (Sum.inl i) *
      (((A i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ ≤
      lam * ldeDiagBound N (fun i => Gmu Sig A z μ (Sum.inl i) (Sum.inl i))) :
    ‖Qmu Sig A z μ - Ymu Sig A z μ‖ ≤ 2 * lam * √(τ⁻¹ * N * Wb) / N := by
  set T := ∑ i, ∑ k, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl k)‖ ^ 2 with hT
  have hT1 : T ≤ τ⁻¹ * N * Wb := by
    calc T ≤ ∑ _i : Fin M, Wb := Finset.sum_le_sum fun i _ => hW i
      _ = M * Wb := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ τ⁻¹ * N * Wb := mul_le_mul_of_nonneg_right hM hWb
  have hoff : ldeOffBound N (fun i j => Gmu Sig A z μ (Sum.inl i) (Sum.inl j)) ≤
      √(τ⁻¹ * N * Wb) / N := by
    unfold ldeOffBound
    refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (le_trans ?_ hT1)) hN.le
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => by positivity)
  have hdiag : ldeDiagBound N (fun i => Gmu Sig A z μ (Sum.inl i) (Sum.inl i)) ≤
      √(τ⁻¹ * N * Wb) / N := by
    unfold ldeDiagBound
    refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (le_trans ?_ hT1)) hN.le
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum (f := fun k => ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl k)‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  rw [prelimBounds_Z_eq]
  calc _ ≤ lam * ldeOffBound N (fun i j => Gmu Sig A z μ (Sum.inl i) (Sum.inl j)) +
        lam * ldeDiagBound N (fun i => Gmu Sig A z μ (Sum.inl i) (Sum.inl i)) :=
        (norm_add_le _ _).trans (add_le_add h10 h11)
    _ ≤ lam * (√(τ⁻¹ * N * Wb) / N) + lam * (√(τ⁻¹ * N * Wb) / N) :=
        add_le_add (mul_le_mul_of_nonneg_left hoff hlam.le)
          (mul_le_mul_of_nonneg_left hdiag hlam.le)
    _ = 2 * lam * √(τ⁻¹ * N * Wb) / N := by ring

/-- (z-Y_bound): `−z − Y = G_μμ⁻¹ + Z`, so `|(−z − Y)⁻¹| ≤ 2K` when `|G_μμ| ≤ K` and
`|Z| ≤ 1/(2K)`. -/
private theorem prelimBounds_zy {K : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (hK0 : 0 < K)
    (hgK : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K)
    (hZ : ‖Qmu Sig A z μ - Ymu Sig A z μ‖ ≤ 1 / (2 * K)) :
    ‖(-z - Ymu Sig A z μ)⁻¹‖ ≤ 2 * K := by
  have hii := Gii hSig A hz μ
  have hg0 := G_diag_ne_zero hSig A hz (Sum.inr μ)
  have hQ : ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ) * Xhat A) (Sum.inr μ) (Sum.inr μ) =
      Qmu Sig A z μ := rfl
  rw [hQ] at hii
  have e : -z - Ymu Sig A z μ = 1 / G Sig A z (Sum.inr μ) (Sum.inr μ) +
      (Qmu Sig A z μ - Ymu Sig A z μ) := by rw [hii]; ring
  have hgpos : 0 < ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := norm_pos_iff.2 hg0
  have h1 : K⁻¹ ≤ ‖1 / G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := by
    rw [one_div, norm_inv]; exact inv_anti₀ hgpos hgK
  have h2 : 1 / (2 * K) ≤ ‖-z - Ymu Sig A z μ‖ := by
    rw [e]
    have := norm_sub_norm_le (1 / G Sig A z (Sum.inr μ) (Sum.inr μ))
      (-(Qmu Sig A z μ - Ymu Sig A z μ))
    rw [norm_neg, sub_neg_eq_add] at this
    have e2 : K⁻¹ - 1 / (2 * K) = 1 / (2 * K) := by field_simp; ring
    linarith
  have h3 : 0 < 1 / (2 * K) := by positivity
  rw [norm_inv]
  calc ‖-z - Ymu Sig A z μ‖⁻¹ ≤ (1 / (2 * K))⁻¹ := inv_anti₀ h3 h2
    _ = 2 * K := by rw [one_div, inv_inv]

/-- The inputs of Lemma 8.9 on `Θ` (§8.3), deterministically: under the bounds of (a_priori_1)
at `v`, `Σ̲e_j`, `e_ν`, of (a_priori_2) at `v`, `Σ̲e_j`, `‖XᵀX‖ ≤ C_n`, the large deviation
bounds for the column `μ`, and numerical conditions on `E`, `L`, `K`, `b`, every field of
`GoodSec8` holds at `μ`. -/
private theorem prelimBounds_det {τ c Km Cn E P lam K b BI : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (hv : testNorm v = 1) (hN : (0 : ℝ) < N) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (hmK : ‖mFun N (specOf Sig) z‖ ≤ Km) (hKm : 1 ≤ Km) (hCn0 : 0 < Cn) (hE0 : 0 ≤ E)
    (hlam : 0 < lam)
    (h1 : ‖testBilin v (lawMat Sig A z) v‖ ≤ E)
    (h2 : ∀ j, ‖testBilin v (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))‖ ≤
      E * testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))
    (h3 : ∀ j k, ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) (lawMat Sig A z)
      (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k))‖ ≤
      E * testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k)))
    (h4 : ∀ ν, ‖testBilin (eI (Sum.inr ν)) (lawMat Sig A z) (eI (Sum.inr ν))‖ ≤ E)
    (h5 : ImGvv Sig A z v ≤ P)
    (h6 : ∀ j, (ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl j))).im ≤ τ⁻¹ ^ 2 * P)
    (h7 : ‖Aᵀ * A‖ ≤ Cn)
    (h8 : ∀ μ, ‖linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)‖ ≤
      lam * ldeLinBound N (colC Sig A z (vbar Sig v) μ))
    (h9 : ∀ μ j, ‖linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤
      lam * ldeLinBound N (colC Sig A z (eI (Sum.inl j)) μ))
    (h10 : ∀ μ, ‖∑ i, ∑ j ∈ Finset.univ.erase i,
      ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl j) * ((A j μ : ℝ) : ℂ)‖ ≤
      lam * ldeOffBound N (fun i j => Gmu Sig A z μ (Sum.inl i) (Sum.inl j)))
    (h11 : ∀ μ, ‖∑ i, Gmu Sig A z μ (Sum.inl i) (Sum.inl i) *
      (((A i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ ≤
      lam * ldeDiagBound N (fun i => Gmu Sig A z μ (Sum.inl i) (Sum.inl i)))
    (n1 : (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im) / N ≤ 1 / 4)
    (hBI : BI = 2 * (τ⁻¹ ^ 2 * P) + 2 * (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2) / N +
      2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / z.im)) +
      8 * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im) * (E + Km) ^ 2 / N)
    (n2a : 2 * τ⁻¹ ^ 2 * Cn / z.im * BI + 2 * τ⁻¹ ^ 2 ≤ N * b ^ 2)
    (n2b : lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / z.im * BI + 2 * τ⁻¹ ^ 2) / N ≤ b ^ 2)
    (n3 : 0 ≤ b) (n3' : b ≤ 1)
    (n4 : τ⁻¹ * (τ⁻¹ ^ 2 * (E + max c⁻¹ Km) + 3 * (E + Km) + 2 * E) ≤ K)
    (n5 : 2 * lam * √(τ⁻¹ * N * (2 * τ⁻¹ ^ 2 * Cn / z.im * K + 2 * τ⁻¹ ^ 2)) / N ≤
      K * (N : ℝ) ^ (-τ / 2))
    (n6 : K * (N : ℝ) ^ (-τ / 2) ≤ 1 / (2 * K)) (μ : Fin N) :
    GoodSec8 τ K b Cn Sig A z v μ := by
  have hSig := hS.posDef
  have hSn := prelimBounds_norm_Sig_le hS hτ
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hτ0 : 0 ≤ τ⁻¹ := by linarith
  have hτ2 : τ⁻¹ ≤ τ⁻¹ ^ 2 := le_self_pow₀ hτi (by norm_num)
  have hKm0 : 0 ≤ Km := by linarith
  have hmx : 0 ≤ max c⁻¹ Km := le_trans hKm0 (le_max_right _ _)
  set K₁ := τ⁻¹ ^ 2 * (E + max c⁻¹ Km) + 3 * (E + Km) + 2 * E with hK₁
  have hA1 : 0 ≤ τ⁻¹ ^ 2 * (E + max c⁻¹ Km) := by positivity
  have hK₁0 : 0 ≤ K₁ := by linarith
  have hK₁K : K₁ ≤ K := (le_mul_of_one_le_left hK₁0 hτi).trans n4
  have hK0 : 0 < K := by linarith
  obtain ⟨hGP, hg⟩ := prelimBounds_g_le hSig A z μ hmK (h4 μ)
  have hxv : |vbar Sig v (Sum.inr μ)| ≤ 1 := by
    have := prelimBounds_abs_le_testNorm v (Sum.inr μ)
    simpa [vbar, hv] using this
  have hxe : ∀ j, |(eI (Sum.inl j) : Fin M ⊕ Fin N → ℝ) (Sum.inr μ)| ≤ 1 := by
    intro j; simp [eI]
  have hP0 : 0 ≤ P := (prelimBounds_im_G_nonneg hSig A hz (vbar Sig v)).trans h5
  have hPv : (ent (G Sig A z) (vbar Sig v) (vbar Sig v)).im ≤ τ⁻¹ ^ 2 * P :=
    (show (ent (G Sig A z) (vbar Sig v) (vbar Sig v)).im ≤ P from h5).trans
      (le_mul_of_one_le_left hP0 (one_le_pow₀ hτi))
  obtain ⟨hWv, hav⟩ := prelimBounds_xbound hSig hSn hτ A hz μ (vbar Sig v) hN hCn0 h7 hlam
    (prelimBounds_qv hSig hτi v hv) hxv hPv hg (h8 μ) n1 hBI n2a n2b n3
  have hxj := fun j => prelimBounds_xbound hSig hSn hτ A hz μ (eI (Sum.inl j)) hN hCn0 h7 hlam
    (prelimBounds_qe hS j) (hxe j) (h6 j) hg (h9 μ j) n1 hBI n2a n2b n3
  have hrow := prelimBounds_rowC_eq hSig A hz μ
  have hcolI : ∀ j k, colC Sig A z (eI (Sum.inl j)) μ k = Gmu Sig A z μ (Sum.inl j) (Sum.inl k) :=
    fun j k => by rw [colC, ent_eI_eI]
  have hsymm : ∀ j k, Gmu Sig A z μ (Sum.inl k) (Sum.inl j) =
      Gmu Sig A z μ (Sum.inl j) (Sum.inl k) := fun j k => by
    have := congrFun (congrFun (Gmu_transpose hSig A hz μ) (Sum.inl j)) (Sum.inl k)
    rw [Matrix.transpose_apply] at this
    exact this
  have hSe : ∀ j, testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) ≤ τ⁻¹ := by
    intro j
    have := prelimBounds_testNorm_SigU hS hτ hτ1 (eI (Sum.inl j) : Fin M ⊕ Fin N → ℝ)
    rwa [prelimBounds_testNorm_eI, mul_one] at this
  have hab : ∀ j, ‖linForm (colC Sig A z (eI (Sum.inl j)) μ) (fun k => A k μ)‖ ≤ 1 :=
    fun j => ((hxj j).2).trans n3'
  have hentvj : ∀ j, ‖colC Sig A z (vbar Sig v) μ j‖ ≤ K₁ := by
    intro j
    refine (prelimBounds_entvj hSig hc A hz v hv μ j hmK hOne hE0 (h2 j) (hSe j) hg
      (hav.trans n3') (hab j) hxv).trans ?_
    have : τ⁻¹ * E ≤ τ⁻¹ ^ 2 * E := mul_le_mul_of_nonneg_right hτ2 hE0
    have : max c⁻¹ Km ≤ τ⁻¹ ^ 2 * max c⁻¹ Km := le_mul_of_one_le_left hmx (one_le_pow₀ hτi)
    have e : τ⁻¹ ^ 2 * (E + max c⁻¹ Km) = τ⁻¹ ^ 2 * E + τ⁻¹ ^ 2 * max c⁻¹ Km := by ring
    linarith
  have hentjk : ∀ j k, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ≤ K₁ := by
    intro j k
    refine (prelimBounds_entjk hSig hc A hz μ j k hmK hKm0 hOne hE0 hτ0 (h3 j k) (hSe j) (hSe k)
      hg (hab j) (hab k)).trans ?_
    have : τ⁻¹ * max c⁻¹ Km ≤ τ⁻¹ ^ 2 * max c⁻¹ Km := mul_le_mul_of_nonneg_right hτ2 hmx
    have e : τ⁻¹ ^ 2 * (E + max c⁻¹ Km) = τ⁻¹ ^ 2 * E + τ⁻¹ ^ 2 * max c⁻¹ Km := by ring
    linarith
  -- the bound on `Z_μ`
  have hWj : ∀ j, ∑ k, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ^ 2 ≤
      2 * τ⁻¹ ^ 2 * Cn / z.im * K + 2 * τ⁻¹ ^ 2 := by
    intro j
    have h := prelimBounds_ward hSig hSn A hz μ (eI (Sum.inl j)) h7 (prelimBounds_qe hS j)
    simp only [hcolI] at h
    have hα : 0 ≤ 2 * τ⁻¹ ^ 2 * Cn / z.im := by positivity
    have hI : (ent (Gmu Sig A z μ) (eI (Sum.inl j)) (eI (Sum.inl j))).im ≤ K := by
      rw [ent_eI_eI]
      exact (Complex.im_le_norm _).trans ((hentjk j j).trans hK₁K)
    have := mul_le_mul_of_nonneg_left hI hα
    linarith
  have hZ := prelimBounds_Zbound A z μ hN hM hlam (by positivity) hWj (h10 μ) (h11 μ)
  have hZK : ‖Qmu Sig A z μ - Ymu Sig A z μ‖ ≤ K * (N : ℝ) ^ (-τ / 2) := hZ.trans n5
  have hgK : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K := by linarith
  refine
    { ent_vv := ?_
      ent_vj := fun j => ⟨(hentvj j).trans hK₁K, by rw [hrow]; exact (hentvj j).trans hK₁K⟩
      ent_jk := fun j k => (hentjk j k).trans hK₁K
      ward_v := ⟨hWv, by rw [hrow]; exact hWv⟩
      ward_j := fun j => ⟨by simpa only [hcolI] using (hxj j).1, by
        simpa only [hcolI, hsymm j] using (hxj j).1⟩
      y_le := (prelimBounds_Ybound A z μ hN hM hK₁0 fun j => hentjk j j).trans n4
      zy_le := prelimBounds_zy hSig A hz μ hK0 hgK (hZK.trans n6)
      col_v := ⟨hav, by rw [hrow]; exact hav⟩
      col_j := fun j => ⟨(hxj j).2, by rw [hrow]; exact (hxj j).2⟩
      z_le := hZK
      gmumu_le := hgK
      norm_le := h7 }
  refine (prelimBounds_entvv hSig A hz v μ n3' h1 hGP hg hav hxv).trans ?_
  linarith

/-! ### The numerical conditions for large `N` -/

private theorem prelimBounds_rpow_mul {n : ℝ} (hn : 0 < n) (a b : ℝ) :
    n ^ a * n ^ b = n ^ (a + b) := (Real.rpow_add hn a b).symm

private theorem prelimBounds_rpow_sq {n : ℝ} (hn : 0 < n) (a : ℝ) : (n ^ a) ^ 2 = n ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num; ring_nf

/-- `C N^r ≤ N^s` for all large `N` when `r < s`. -/
private theorem prelimBounds_eventually (C r s : ℝ) (hrs : r < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C * (N : ℝ) ^ r ≤ (N : ℝ) ^ s := by
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  refine ⟨⌈C' ^ (s - r)⁻¹⌉₊ + 1, fun N hN => ?_⟩
  have hsr : 0 < s - r := by linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
    exact_mod_cast this
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : C' ^ (s - r)⁻¹ ≤ (N : ℝ) := by
    have := Nat.le_ceil (C' ^ (s - r)⁻¹)
    have h2 : (⌈C' ^ (s - r)⁻¹⌉₊ : ℝ) ≤ N := by
      have : ⌈C' ^ (s - r)⁻¹⌉₊ ≤ N := by omega
      exact_mod_cast this
    linarith
  have h3 : C' ≤ (N : ℝ) ^ (s - r) := by
    calc C' = (C' ^ (s - r)⁻¹) ^ (s - r) :=
          (Real.rpow_inv_rpow (by linarith) hsr.ne').symm
      _ ≤ (N : ℝ) ^ (s - r) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 hsr.le
  have h4 : 0 ≤ (N : ℝ) ^ r := Real.rpow_nonneg hNp.le _
  calc C * (N : ℝ) ^ r ≤ C' * (N : ℝ) ^ r := mul_le_mul_of_nonneg_right (le_max_left _ _) h4
    _ ≤ (N : ℝ) ^ (s - r) * (N : ℝ) ^ r := mul_le_mul_of_nonneg_right h3 h4
    _ = (N : ℝ) ^ s := by rw [prelimBounds_rpow_mul hNp]; ring_nf

/-- Elementary facts on `Ψ` on `𝐃(τ, N)`: `1/(Nη) ≤ N^{−τ}`, `1/(Nη) ≤ Ψ`, `Im m/(Nη) ≤ Ψ²`,
`1 ≤ K_m N Ψ²`, `Ψ ≤ τ⁻¹ N Ψ²`, `Ψ ≤ (K_m^{1/2} + 1) N^{−τ/2}`. -/
private theorem prelimBounds_psi {τ Km η mI Ψ n : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hKm : 1 ≤ Km)
    (hn : 1 ≤ n) (hη0 : 0 < η) (hη1 : n ^ (-1 + τ) ≤ η) (hη2 : η ≤ τ⁻¹) (hmI0 : 0 < mI)
    (hmIK : mI ≤ Km) (hmIlow : Km⁻¹ * η ≤ mI) (hΨ : Ψ = √(mI / (n * η)) + 1 / (n * η)) :
    1 / (n * η) ≤ n ^ (-τ) ∧ 1 / (n * η) ≤ Ψ ∧ mI / (n * η) ≤ Ψ ^ 2 ∧ 1 ≤ Km * n * Ψ ^ 2 ∧
      Ψ ≤ τ⁻¹ * n * Ψ ^ 2 ∧ Ψ ≤ (√Km + 1) * n ^ (-τ / 2) ∧ 0 < Ψ ∧ 1 / n ≤ n ^ (-τ) := by
  have hn0 : 0 < n := by linarith
  have hnη : 0 < n * η := mul_pos hn0 hη0
  have hnτ : n ^ τ ≤ n * η := by
    have e : n ^ τ = n * n ^ (-1 + τ) := by
      rw [← Real.rpow_one_add' hn0.le (by linarith)]; ring_nf
    rw [e]; exact mul_le_mul_of_nonneg_left hη1 hn0.le
  have hX : 1 / (n * η) ≤ n ^ (-τ) := by
    rw [Real.rpow_neg hn0.le, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hn0 _) hnτ
  have hs0 : 0 ≤ √(mI / (n * η)) := Real.sqrt_nonneg _
  have hXΨ : 1 / (n * η) ≤ Ψ := by rw [hΨ]; linarith
  have hX0 : 0 < 1 / (n * η) := by positivity
  have hΨ0 : 0 < Ψ := lt_of_lt_of_le hX0 hXΨ
  have hmΨ : mI / (n * η) ≤ Ψ ^ 2 := by
    have h1 : √(mI / (n * η)) ≤ Ψ := by rw [hΨ]; linarith
    calc mI / (n * η) = √(mI / (n * η)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ Ψ ^ 2 := pow_le_pow_left₀ hs0 h1 2
  have hKm0 : 0 < Km := by linarith
  have h1K : 1 ≤ Km * n * Ψ ^ 2 := by
    have e : Km * n * (mI / (n * η)) = Km * mI / η := by field_simp
    have h2 : 1 ≤ Km * mI / η := by
      rw [le_div_iff₀ hη0]
      have := mul_le_mul_of_nonneg_left hmIlow hKm0.le
      rw [← mul_assoc, mul_inv_cancel₀ hKm0.ne', one_mul] at this
      linarith
    calc (1 : ℝ) ≤ Km * n * (mI / (n * η)) := by rw [e]; exact h2
      _ ≤ Km * n * Ψ ^ 2 := mul_le_mul_of_nonneg_left hmΨ (by positivity)
  have hΨn : Ψ ≤ τ⁻¹ * n * Ψ ^ 2 := by
    have h2 : n * Ψ * (1 / (n * η)) = Ψ / η := by field_simp
    have h3 : τ * Ψ ≤ Ψ / η := by
      rw [le_div_iff₀ hη0]
      have : η * τ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hη2 hτ.le
        rwa [inv_mul_cancel₀ hτ.ne'] at this
      nlinarith
    have h4 : Ψ / η ≤ n * Ψ ^ 2 := by
      rw [← h2, sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hXΨ (by positivity)
    have h5 : τ * Ψ ≤ n * Ψ ^ 2 := h3.trans h4
    calc Ψ = τ⁻¹ * (τ * Ψ) := by field_simp
      _ ≤ τ⁻¹ * (n * Ψ ^ 2) := mul_le_mul_of_nonneg_left h5 (inv_pos.2 hτ).le
      _ = τ⁻¹ * n * Ψ ^ 2 := by ring
  have hΨup : Ψ ≤ (√Km + 1) * n ^ (-τ / 2) := by
    have hh : n ^ (-τ) = (n ^ (-τ / 2)) ^ 2 := by
      rw [prelimBounds_rpow_sq hn0]; ring_nf
    have hq0 : 0 ≤ n ^ (-τ / 2) := Real.rpow_nonneg hn0.le _
    have h1 : √(mI / (n * η)) ≤ √Km * n ^ (-τ / 2) := by
      rw [show √Km * n ^ (-τ / 2) = √(Km * (n ^ (-τ / 2)) ^ 2) by
        rw [Real.sqrt_mul hKm0.le, Real.sqrt_sq hq0]]
      apply Real.sqrt_le_sqrt
      rw [← hh, div_eq_mul_one_div]
      exact mul_le_mul hmIK hX hX0.le hKm0.le
    have h2 : 1 / (n * η) ≤ n ^ (-τ / 2) :=
      hX.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
    rw [hΨ]; nlinarith
  have hn1 : 1 / n ≤ n ^ (-τ) := by
    have : n ^ (-1 : ℝ) ≤ n ^ (-τ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  exact ⟨hX, hXΨ, hmΨ, h1K, hΨn, hΨup, hΨ0, hn1⟩

/-- The absorption condition of (im_BGB): `(E + K_m) L² α/N ≤ 1/4`, `α = 2τ⁻²C_n/η`. -/
private theorem prelimBounds_num1 {τ Cn δ Km η E lam n : ℝ} (hτ : 0 < τ)
    (hCn : 0 < Cn) (hn : 1 ≤ n) (hη0 : 0 < η) (hX : 1 / (n * η) ≤ n ^ (-τ))
    (hE : E = n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (hlam : lam = n ^ (δ / 8))
    (R1 : Km ≤ n ^ (5 / 2 * δ)) (R3 : 16 * τ⁻¹ ^ 2 * Cn * n ^ (11 / 4 * δ) ≤ n ^ τ) :
    (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) / n ≤ 1 / 4 := by
  have hn0 : 0 < n := by linarith
  have pw := prelimBounds_rpow_mul hn0
  have hp0 : ∀ r : ℝ, 0 < n ^ r := fun r => Real.rpow_pos_of_pos hn0 r
  have hE' : E = n ^ (5 / 2 * δ) := by rw [hE, pw]; ring_nf
  have hlam2 : lam ^ 2 = n ^ (δ / 4) := by rw [hlam, prelimBounds_rpow_sq hn0]; ring_nf
  have hEK : E + Km ≤ 2 * E := by rw [hE']; linarith
  have hEl : (E + Km) * lam ^ 2 ≤ 2 * n ^ (11 / 4 * δ) := by
    rw [hlam2]
    calc (E + Km) * n ^ (δ / 4) ≤ 2 * E * n ^ (δ / 4) :=
          mul_le_mul_of_nonneg_right hEK (hp0 _).le
      _ = 2 * n ^ (11 / 4 * δ) := by rw [hE', mul_assoc, pw]; ring_nf
  have e : (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) / n =
      (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn * (1 / (n * η))) := by field_simp
  rw [e]
  have h1 : (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn * (1 / (n * η))) ≤
      2 * n ^ (11 / 4 * δ) * (2 * τ⁻¹ ^ 2 * Cn * n ^ (-τ)) :=
    mul_le_mul hEl (mul_le_mul_of_nonneg_left hX (by positivity)) (by positivity)
      (by positivity)
  have h2 : 2 * n ^ (11 / 4 * δ) * (2 * τ⁻¹ ^ 2 * Cn * n ^ (-τ)) =
      (16 * τ⁻¹ ^ 2 * Cn * n ^ (11 / 4 * δ)) * n ^ (-τ) / 4 := by ring
  have h3 : n ^ τ * n ^ (-τ) = 1 := by rw [pw]; simp
  have h4 := mul_le_mul_of_nonneg_right R3 (hp0 (-τ)).le
  rw [h3] at h4
  linarith

/-- `P/(Nη) ≤ 2 N^{(C₀+9/4)δ} Ψ²` for `P = N^{9δ/4}(Im m + N^{C₀δ}Ψ)`. -/
private theorem prelimBounds_numPX {C₀ δ mI Ψ P X n : ℝ} (hδ : 0 < δ) (hC₀ : 3 ≤ C₀)
    (hn : 1 ≤ n) (hP : P = n ^ (δ / 4) * (n ^ (2 * δ) * (mI + n ^ (C₀ * δ) * Ψ)))
    (h1 : mI * X ≤ Ψ ^ 2) (h2 : Ψ * X ≤ Ψ ^ 2) :
    P * X ≤ 2 * n ^ ((C₀ + 9 / 4) * δ) * Ψ ^ 2 := by
  have hn0 : 0 < n := by linarith
  have pw := prelimBounds_rpow_mul hn0
  have hc : n ^ (δ / 4) * n ^ (2 * δ) = n ^ (9 / 4 * δ) := by rw [pw]; ring_nf
  have hc2 : n ^ (9 / 4 * δ) * n ^ (C₀ * δ) = n ^ ((C₀ + 9 / 4) * δ) := by rw [pw]; ring_nf
  have e : P * X = n ^ (9 / 4 * δ) * (mI * X + n ^ (C₀ * δ) * (Ψ * X)) := by
    rw [hP, ← hc]; ring
  have h3 : 1 ≤ n ^ (C₀ * δ) := Real.one_le_rpow hn (by nlinarith)
  have h4 : mI * X ≤ n ^ (C₀ * δ) * Ψ ^ 2 := h1.trans (le_mul_of_one_le_left (sq_nonneg _) h3)
  have h5 : n ^ (C₀ * δ) * (Ψ * X) ≤ n ^ (C₀ * δ) * Ψ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : 0 ≤ n ^ (9 / 4 * δ) := Real.rpow_nonneg hn0.le _
  rw [e]
  calc n ^ (9 / 4 * δ) * (mI * X + n ^ (C₀ * δ) * (Ψ * X))
      ≤ n ^ (9 / 4 * δ) * (n ^ (C₀ * δ) * Ψ ^ 2 + n ^ (C₀ * δ) * Ψ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h4 h5) h6
    _ = 2 * (n ^ (9 / 4 * δ) * n ^ (C₀ * δ)) * Ψ ^ 2 := by ring
    _ = 2 * n ^ ((C₀ + 9 / 4) * δ) * Ψ ^ 2 := by rw [hc2]

/-- `L² (E + K_m)² ≤ 4 N^{(C₀+9/4)δ}` and `(E + K_m) L² ≤ 2 N^{(C₀+9/4)δ}`. -/
private theorem prelimBounds_numEL {C₀ δ Km E lam n : ℝ} (hδ : 0 < δ) (hC₀ : 3 ≤ C₀)
    (hn : 1 ≤ n) (hE : E = n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (hlam : lam = n ^ (δ / 8))
    (R1 : Km ≤ n ^ (5 / 2 * δ)) (hKm : 0 ≤ Km) :
    lam ^ 2 * (E + Km) ^ 2 ≤ 4 * n ^ ((C₀ + 9 / 4) * δ) ∧
      (E + Km) * lam ^ 2 ≤ 2 * n ^ ((C₀ + 9 / 4) * δ) ∧ E + Km ≤ 2 * E ∧ 0 ≤ E := by
  have hn0 : 0 < n := by linarith
  have pw := prelimBounds_rpow_mul hn0
  have hmono : ∀ r s : ℝ, r ≤ s → n ^ r ≤ n ^ s := fun r s h =>
    Real.rpow_le_rpow_of_exponent_le hn h
  have hE' : E = n ^ (5 / 2 * δ) := by rw [hE, pw]; ring_nf
  have hlam2 : lam ^ 2 = n ^ (δ / 4) := by rw [hlam, prelimBounds_rpow_sq hn0]; ring_nf
  have hEK : E + Km ≤ 2 * E := by rw [hE']; linarith
  have hE0 : 0 ≤ E := by rw [hE']; exact Real.rpow_nonneg hn0.le _
  have hl0 : 0 ≤ lam ^ 2 := sq_nonneg _
  have h1 : lam ^ 2 * E ^ 2 = n ^ (21 / 4 * δ) := by
    rw [hlam2, hE', prelimBounds_rpow_sq hn0, pw]; ring_nf
  have h2 : E * lam ^ 2 = n ^ (11 / 4 * δ) := by rw [hlam2, hE', pw]; ring_nf
  have h3 : n ^ (21 / 4 * δ) ≤ n ^ ((C₀ + 9 / 4) * δ) := hmono _ _ (by nlinarith)
  have h4 : n ^ (11 / 4 * δ) ≤ n ^ ((C₀ + 9 / 4) * δ) := hmono _ _ (by nlinarith)
  have hEK2 : (E + Km) ^ 2 ≤ 4 * E ^ 2 := by nlinarith
  refine ⟨?_, ?_, hEK, hE0⟩
  · calc lam ^ 2 * (E + Km) ^ 2 ≤ lam ^ 2 * (4 * E ^ 2) := mul_le_mul_of_nonneg_left hEK2 hl0
      _ = 4 * (lam ^ 2 * E ^ 2) := by ring
      _ ≤ 4 * n ^ ((C₀ + 9 / 4) * δ) := by rw [h1]; linarith
  · calc (E + Km) * lam ^ 2 ≤ 2 * E * lam ^ 2 := mul_le_mul_of_nonneg_right hEK hl0
      _ = 2 * (E * lam ^ 2) := by ring
      _ ≤ 2 * n ^ ((C₀ + 9 / 4) * δ) := by rw [h2]; linarith

/-- (BGX_est), (im_BGB): `α B_I + β ≤ N^{(C₀+15/4)δ} N Ψ²`. -/
private theorem prelimBounds_num2 {τ Cn Km η Ψ E P lam n Q Q' X : ℝ} (hτ : 0 < τ)
    (hCn : 0 < Cn) (hKm : 1 ≤ Km) (hn : 1 ≤ n) (hη0 : 0 < η) (hX : X = 1 / (n * η))
    (hXΨ : X ≤ Ψ) (h1K : 1 ≤ Km * n * Ψ ^ 2) (hΨn : Ψ ≤ τ⁻¹ * n * Ψ ^ 2) (hQ1 : 1 ≤ Q)
    (hPX : P * X ≤ 2 * Q * Ψ ^ 2) (hEL2 : lam ^ 2 * (E + Km) ^ 2 ≤ 4 * Q)
    (hEL : (E + Km) * lam ^ 2 ≤ 2 * Q)
    (R4 : (8 * τ⁻¹ ^ 4 * Cn + 16 * τ⁻¹ ^ 5 * Cn + 128 * τ⁻¹ ^ 4 * Cn ^ 2 + 3 * τ⁻¹ ^ 2 * Km) *
      Q ≤ Q') :
    2 * τ⁻¹ ^ 2 * Cn / η * (2 * (τ⁻¹ ^ 2 * P) + 2 * (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2) / n +
      2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / η)) +
      8 * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) * (E + Km) ^ 2 / n) + 2 * τ⁻¹ ^ 2 ≤
      Q' * (n * Ψ ^ 2) := by
  have hn0 : 0 < n := by linarith
  have hτ0 : 0 < τ⁻¹ := inv_pos.2 hτ
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hnΨ : 0 ≤ n * Ψ ^ 2 := by positivity
  have hα0 : 0 < 2 * τ⁻¹ ^ 2 * Cn / η := by positivity
  have e1 : 2 * τ⁻¹ ^ 2 * Cn / η * (2 * (τ⁻¹ ^ 2 * P)) = 4 * τ⁻¹ ^ 4 * Cn * n * (P * X) := by
    rw [hX]; field_simp; ring
  have e2 : 2 * τ⁻¹ ^ 2 * Cn / η * (2 * (E + Km) * lam ^ 2 * (2 * τ⁻¹ ^ 2) / n) =
      8 * τ⁻¹ ^ 4 * Cn * ((E + Km) * lam ^ 2) * X := by
    rw [hX]; field_simp; ring
  have e3 : 2 * τ⁻¹ ^ 2 * Cn / η * (2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / η))) = τ⁻¹ ^ 2 := by
    field_simp
  have e4 : 2 * τ⁻¹ ^ 2 * Cn / η * (8 * lam ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) * (E + Km) ^ 2 / n) =
      32 * τ⁻¹ ^ 4 * Cn ^ 2 * (lam ^ 2 * (E + Km) ^ 2) * (n * X ^ 2) := by
    rw [hX]; field_simp; ring
  have t1 : 4 * τ⁻¹ ^ 4 * Cn * n * (P * X) ≤ 8 * τ⁻¹ ^ 4 * Cn * Q * (n * Ψ ^ 2) := by
    calc 4 * τ⁻¹ ^ 4 * Cn * n * (P * X) ≤ 4 * τ⁻¹ ^ 4 * Cn * n * (2 * Q * Ψ ^ 2) :=
          mul_le_mul_of_nonneg_left hPX (by positivity)
      _ = 8 * τ⁻¹ ^ 4 * Cn * Q * (n * Ψ ^ 2) := by ring
  have t2 : 8 * τ⁻¹ ^ 4 * Cn * ((E + Km) * lam ^ 2) * X ≤
      16 * τ⁻¹ ^ 5 * Cn * Q * (n * Ψ ^ 2) := by
    have h1 : X ≤ τ⁻¹ * (n * Ψ ^ 2) := hXΨ.trans (by linarith)
    calc 8 * τ⁻¹ ^ 4 * Cn * ((E + Km) * lam ^ 2) * X
        ≤ 8 * τ⁻¹ ^ 4 * Cn * (2 * Q) * (τ⁻¹ * (n * Ψ ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEL (by positivity)) h1 hX0 (by positivity)
      _ = 16 * τ⁻¹ ^ 5 * Cn * Q * (n * Ψ ^ 2) := by ring
  have t4 : 32 * τ⁻¹ ^ 4 * Cn ^ 2 * (lam ^ 2 * (E + Km) ^ 2) * (n * X ^ 2) ≤
      128 * τ⁻¹ ^ 4 * Cn ^ 2 * Q * (n * Ψ ^ 2) := by
    have hXΨ2 : n * X ^ 2 ≤ n * Ψ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hXΨ 2) hn0.le
    calc 32 * τ⁻¹ ^ 4 * Cn ^ 2 * (lam ^ 2 * (E + Km) ^ 2) * (n * X ^ 2)
        ≤ 32 * τ⁻¹ ^ 4 * Cn ^ 2 * (4 * Q) * (n * Ψ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEL2 (by positivity)) hXΨ2 (by positivity)
            (by positivity)
      _ = 128 * τ⁻¹ ^ 4 * Cn ^ 2 * Q * (n * Ψ ^ 2) := by ring
  have t5 : 3 * τ⁻¹ ^ 2 ≤ 3 * τ⁻¹ ^ 2 * Km * Q * (n * Ψ ^ 2) := by
    have h1 : 1 ≤ Km * Q * (n * Ψ ^ 2) := by
      have : Km * n * Ψ ^ 2 ≤ Km * Q * (n * Ψ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hQ1 (by positivity : 0 ≤ Km * (n * Ψ ^ 2))
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 3 * τ⁻¹ ^ 2)
    linarith
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4]
  have h4 := mul_le_mul_of_nonneg_right R4 hnΨ
  calc _ ≤ 8 * τ⁻¹ ^ 4 * Cn * Q * (n * Ψ ^ 2) + 16 * τ⁻¹ ^ 5 * Cn * Q * (n * Ψ ^ 2) +
        128 * τ⁻¹ ^ 4 * Cn ^ 2 * Q * (n * Ψ ^ 2) + 3 * τ⁻¹ ^ 2 * Km * Q * (n * Ψ ^ 2) := by
        linarith
    _ = (8 * τ⁻¹ ^ 4 * Cn + 16 * τ⁻¹ ^ 5 * Cn + 128 * τ⁻¹ ^ 4 * Cn ^ 2 + 3 * τ⁻¹ ^ 2 * Km) *
        Q * (n * Ψ ^ 2) := by ring
    _ ≤ Q' * (n * Ψ ^ 2) := h4

/-- `b = N^{(C₀/2+2)δ} Ψ ≤ 1`. -/
private theorem prelimBounds_num3 {τ C₀ δ Km Ψ b n : ℝ} (hn : 1 ≤ n)
    (hb : b = n ^ ((C₀ / 2 + 2) * δ) * Ψ) (hΨup : Ψ ≤ (√Km + 1) * n ^ (-τ / 2)) (hΨ0 : 0 < Ψ)
    (R5 : (√Km + 1) * n ^ ((C₀ / 2 + 2) * δ) ≤ n ^ (τ / 2)) : 0 ≤ b ∧ b ≤ 1 := by
  have hn0 : 0 < n := by linarith
  have h0 : 0 < n ^ ((C₀ / 2 + 2) * δ) := Real.rpow_pos_of_pos hn0 _
  refine ⟨by rw [hb]; positivity, ?_⟩
  have h1 : n ^ (τ / 2) * n ^ (-τ / 2) = 1 := by
    rw [prelimBounds_rpow_mul hn0]; ring_nf; simp
  rw [hb]
  calc n ^ ((C₀ / 2 + 2) * δ) * Ψ ≤ n ^ ((C₀ / 2 + 2) * δ) * ((√Km + 1) * n ^ (-τ / 2)) :=
        mul_le_mul_of_nonneg_left hΨup h0.le
    _ = ((√Km + 1) * n ^ ((C₀ / 2 + 2) * δ)) * n ^ (-τ / 2) := by ring
    _ ≤ n ^ (τ / 2) * n ^ (-τ / 2) :=
        mul_le_mul_of_nonneg_right R5 (Real.rpow_nonneg hn0.le _)
    _ = 1 := h1

/-- The level of (G_sigma_bound): `τ⁻¹ K₁ ≤ K = N^{3δ}`. -/
private theorem prelimBounds_num4 {τ c δ Km E K n : ℝ} (hτ : 0 < τ) (hKm : 1 ≤ Km)
    (hδ : 0 < δ) (hn : 1 ≤ n) (hE : E = n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (hK : K = n ^ (3 * δ))
    (R1 : Km ≤ n ^ (5 / 2 * δ))
    (R6 : τ⁻¹ * (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ Km + 8) * n ^ (5 / 2 * δ) ≤ n ^ (3 * δ)) :
    τ⁻¹ * (τ⁻¹ ^ 2 * (E + max c⁻¹ Km) + 3 * (E + Km) + 2 * E) ≤ K := by
  have hn0 : 0 < n := by linarith
  have hE' : E = n ^ (5 / 2 * δ) := by rw [hE, prelimBounds_rpow_mul hn0]; ring_nf
  have hE1 : 1 ≤ E := by rw [hE']; exact Real.one_le_rpow hn (by positivity)
  have hmx : 0 ≤ max c⁻¹ Km := le_trans (by linarith) (le_max_right _ _)
  have hτ0 : 0 < τ⁻¹ := inv_pos.2 hτ
  have h1 : max c⁻¹ Km ≤ max c⁻¹ Km * E := le_mul_of_one_le_right hmx hE1
  have h2 : Km ≤ E := by rw [hE']; exact R1
  have h3 : τ⁻¹ ^ 2 * (E + max c⁻¹ Km) + 3 * (E + Km) + 2 * E ≤
      (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ Km + 8) * E := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ τ⁻¹ ^ 2)
    nlinarith
  rw [hK]
  calc τ⁻¹ * (τ⁻¹ ^ 2 * (E + max c⁻¹ Km) + 3 * (E + Km) + 2 * E)
      ≤ τ⁻¹ * ((τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ Km + 8) * E) :=
        mul_le_mul_of_nonneg_left h3 hτ0.le
    _ = τ⁻¹ * (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ Km + 8) * n ^ (5 / 2 * δ) := by rw [hE']; ring
    _ ≤ n ^ (3 * δ) := R6

/-- The level of `Z_μ`: `2L (τ⁻¹ N (αK + β))^{1/2}/N ≤ K N^{−τ/2}`. -/
private theorem prelimBounds_num5 {τ Cn δ η lam K n : ℝ} (hτ : 0 < τ) (hCn : 0 < Cn)
    (hδ : 0 < δ) (hn : 1 ≤ n) (hη0 : 0 < η) (hlam : lam = n ^ (δ / 8)) (hK : K = n ^ (3 * δ))
    (hX : 1 / (n * η) ≤ n ^ (-τ)) (hn1 : 1 / n ≤ n ^ (-τ))
    (R7 : 8 * τ⁻¹ ^ 3 * (Cn + 1) * n ^ (δ / 4) ≤ n ^ (3 * δ)) :
    2 * lam * √(τ⁻¹ * n * (2 * τ⁻¹ ^ 2 * Cn / η * K + 2 * τ⁻¹ ^ 2)) / n ≤
      K * n ^ (-τ / 2) := by
  have hn0 : 0 < n := by linarith
  have pw := prelimBounds_rpow_mul hn0
  have hτ0 : 0 < τ⁻¹ := inv_pos.2 hτ
  have hK1 : 1 ≤ K := by rw [hK]; exact Real.one_le_rpow hn (by positivity)
  have hlam2 : lam ^ 2 = n ^ (δ / 4) := by rw [hlam, prelimBounds_rpow_sq hn0]; ring_nf
  set Y := τ⁻¹ * n * (2 * τ⁻¹ ^ 2 * Cn / η * K + 2 * τ⁻¹ ^ 2) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hL0 : 0 ≤ 2 * lam * √Y / n := by rw [hlam]; positivity
  have hR0 : 0 ≤ K * n ^ (-τ / 2) := by positivity
  have hm : n ^ (-τ) ≥ 0 := Real.rpow_nonneg hn0.le _
  have hYn : Y / n ^ 2 ≤ τ⁻¹ * (2 * τ⁻¹ ^ 2 * (Cn + 1) * K * n ^ (-τ)) := by
    have e : Y / n ^ 2 = τ⁻¹ * (2 * τ⁻¹ ^ 2 * Cn * K * (1 / (n * η)) + 2 * τ⁻¹ ^ 2 * (1 / n)) := by
      rw [hY]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hτ0.le
    have h1 : 2 * τ⁻¹ ^ 2 * Cn * K * (1 / (n * η)) ≤ 2 * τ⁻¹ ^ 2 * Cn * K * n ^ (-τ) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have h2 : 2 * τ⁻¹ ^ 2 * (1 / n) ≤ 2 * τ⁻¹ ^ 2 * K * n ^ (-τ) := by
      calc 2 * τ⁻¹ ^ 2 * (1 / n) ≤ 2 * τ⁻¹ ^ 2 * n ^ (-τ) :=
            mul_le_mul_of_nonneg_left hn1 (by positivity)
        _ = 2 * τ⁻¹ ^ 2 * 1 * n ^ (-τ) := by ring
        _ ≤ 2 * τ⁻¹ ^ 2 * K * n ^ (-τ) := by gcongr
    have e2 : 2 * τ⁻¹ ^ 2 * (Cn + 1) * K * n ^ (-τ) =
        2 * τ⁻¹ ^ 2 * Cn * K * n ^ (-τ) + 2 * τ⁻¹ ^ 2 * K * n ^ (-τ) := by ring
    linarith
  have hsq : (2 * lam * √Y / n) ^ 2 ≤ (K * n ^ (-τ / 2)) ^ 2 := by
    have e1 : (2 * lam * √Y / n) ^ 2 = 4 * lam ^ 2 * (Y / n ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hY0]; ring
    have e2 : (K * n ^ (-τ / 2)) ^ 2 = K * K * n ^ (-τ) := by
      rw [mul_pow, prelimBounds_rpow_sq hn0]; ring_nf
    rw [e1, e2, hlam2]
    calc 4 * n ^ (δ / 4) * (Y / n ^ 2)
        ≤ 4 * n ^ (δ / 4) * (τ⁻¹ * (2 * τ⁻¹ ^ 2 * (Cn + 1) * K * n ^ (-τ))) :=
          mul_le_mul_of_nonneg_left hYn (by positivity)
      _ = (8 * τ⁻¹ ^ 3 * (Cn + 1) * n ^ (δ / 4)) * (K * n ^ (-τ)) := by ring
      _ ≤ n ^ (3 * δ) * (K * n ^ (-τ)) := mul_le_mul_of_nonneg_right R7 (by positivity)
      _ = K * K * n ^ (-τ) := by rw [hK]; ring
  exact (pow_le_pow_iff_left₀ hL0 hR0 two_ne_zero).1 hsq

/-- The level of (z-Y_bound): `K N^{−τ/2} ≤ 1/(2K)`. -/
private theorem prelimBounds_num6 {τ δ K n : ℝ} (hn : 1 ≤ n) (hK : K = n ^ (3 * δ))
    (R8 : 2 * n ^ (6 * δ) ≤ n ^ (τ / 2)) : K * n ^ (-τ / 2) ≤ 1 / (2 * K) := by
  have hn0 : 0 < n := by linarith
  have pw := prelimBounds_rpow_mul hn0
  have hK0 : 0 < K := by rw [hK]; exact Real.rpow_pos_of_pos hn0 _
  rw [le_div_iff₀ (by positivity)]
  have h1 : n ^ (τ / 2) * n ^ (-τ / 2) = 1 := by rw [pw]; ring_nf; simp
  have h2 : K * K = n ^ (6 * δ) := by rw [hK, pw]; ring_nf
  calc K * n ^ (-τ / 2) * (2 * K) = 2 * (K * K) * n ^ (-τ / 2) := by ring
    _ = 2 * n ^ (6 * δ) * n ^ (-τ / 2) := by rw [h2]
    _ ≤ n ^ (τ / 2) * n ^ (-τ / 2) :=
        mul_le_mul_of_nonneg_right R8 (Real.rpow_nonneg hn0.le _)
    _ = 1 := h1


/-! ### The events -/

/-- `x ↦ G^{(μ)}_{xy}` is a measurable function of the matrix. -/
private theorem prelimBounds_measurable_ent (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (μ : Fin N)
    (x y : Fin M ⊕ Fin N → ℝ) :
    Measurable fun B : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig B z μ) x y := by
  simp only [prelimBounds_ent_eq]
  refine Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun t _ => ?_
  exact (measurable_const.mul (prelimBounds_measurable_Gm Sig z _ s t)).mul measurable_const

/-- `ent B (r x) (r x) = r² ent B x x`. -/
private theorem prelimBounds_ent_smul {p : Type*} [Fintype p] (B : Matrix p p ℂ) (r : ℝ)
    (x : p → ℝ) : ent B (r • x) (r • x) = ((r ^ 2 : ℝ) : ℂ) * ent B x x := by
  simp only [prelimBounds_ent_eq, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  push_cast; ring

/-- `v̄` is linear. -/
private theorem prelimBounds_vbar_smul (Sig : Matrix (Fin M) (Fin M) ℝ) (r : ℝ)
    (x : Fin M ⊕ Fin N → ℝ) : vbar Sig (r • x) = r • vbar Sig x := by
  funext s
  rcases s with i | μ
  · have e : (r • x) ∘ Sum.inl = r • (x ∘ Sum.inl) := by funext k; simp
    simp only [vbar, Sum.elim_inl, Pi.smul_apply, e, mulVec_smul]
  · simp [vbar]

/-- The unit vector `w_j = Σ̲ e_j/|Σ̲ e_j|` and `Im G_{jj} = |Σ̲ e_j|² Im G_{w̄_j w̄_j}`. -/
private theorem prelimBounds_wj {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (j : Fin M) :
    testNorm ((testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))⁻¹ •
        (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))) = 1 ∧
      (ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl j))).im =
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) ^ 2 *
          ImGvv Sig A z ((testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))⁻¹ •
            (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))) := by
  set u := SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j) with hu
  have hvu : vbar Sig u = eI (Sum.inl j) := prelimBounds_vbar_SigU hSig _
  have hne : testNorm u ≠ 0 := by
    intro h0
    have h := prelimBounds_testNorm_eq_zero h0
    have : vbar Sig u = 0 := by rw [h]; funext s; rcases s with i | μ <;> simp [vbar]
    rw [hvu] at this
    have := congrFun this (Sum.inl j)
    simp [eI] at this
  have hpos : 0 < testNorm u := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)
  refine ⟨?_, ?_⟩
  · rw [prelimBounds_testNorm_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hne]
  · unfold ImGvv
    rw [prelimBounds_vbar_smul, hvu, prelimBounds_ent_smul, Complex.im_ofReal_mul, ← mul_assoc,
      ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]

/-- (BGX_est) and the bound on `Z_μ`: the large deviation estimates for the column `μ` with the
coefficients of
`G^{(μ)}`, which are independent of the column (`Gmu_updCol`, `EntryAssumption.indep`). -/
private theorem prelimBounds_lde (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      EntryAssumption C X → ∀ μ : Fin N,
        (∀ x : Fin M ⊕ Fin N → ℝ, DomAt N ε D
          (fun ω => ‖linForm (colC Sig (X ω) z x μ) (fun j => X ω j μ)‖)
          (fun ω => ldeLinBound N (colC Sig (X ω) z x μ))) ∧
        DomAt N ε D
          (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i,
            ((X ω i μ : ℝ) : ℂ) * Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl j) * ((X ω j μ : ℝ) : ℂ)‖)
          (fun ω => ldeOffBound N (fun i j => Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl j))) ∧
        DomAt N ε D
          (fun ω => ‖∑ i, Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl i) *
            (((X ω i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖)
          (fun ω => ldeDiagBound N (fun i => Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl i))) := by
  obtain ⟨N₁, h₁⟩ := lde_linear_cond C hε D
  obtain ⟨N₂, h₂⟩ := lde_offdiag_cond C hε D
  obtain ⟨N₃, h₃⟩ := lde_diag_cond C hε D
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M Sig z X hX μ => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hrow := prelimBounds_rowAssumption hX μ
  have hY := prelimBounds_measurable_updCol hX μ
  have hind := prelimBounds_indep hX μ
  have hG : ∀ ω, Gmu Sig (updCol (X ω) μ 0) z μ = Gmu Sig (X ω) z μ := fun ω =>
    Gmu_updCol Sig (X ω) z μ 0
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have h := h₁ N hN₁ (fun j ω => X ω j μ) (fun ω => updCol (X ω) μ 0)
      (fun B j => colC Sig B z x μ j) hrow hY
      (fun j => prelimBounds_measurable_ent Sig z μ x _) hind
    have e : ∀ ω, colC Sig (updCol (X ω) μ 0) z x μ = colC Sig (X ω) z x μ := fun ω => by
      funext j; simp only [colC, hG]
    simp only [e] at h
    exact h
  · have h := h₂ N hN₂ (fun j ω => X ω j μ) (fun ω => updCol (X ω) μ 0)
      (fun B i j => Gmu Sig B z μ (Sum.inl i) (Sum.inl j)) hrow hY
      (fun i j => prelimBounds_measurable_Gm Sig z _ _ _) hind
    simp only [hG] at h
    exact h
  · have h := h₃ N hN₃ (fun j ω => X ω j μ) (fun ω => updCol (X ω) μ 0)
      (fun B i => Gmu Sig B z μ (Sum.inl i) (Sum.inl i)) hrow hY
      (fun i => prelimBounds_measurable_Gm Sig z _ _ _) hind
    simp only [hG] at h
    exact h

/-- `C₀(τ) ≥ 2400`. -/
private theorem prelimBounds_czero_ge {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 2400 ≤ czero τ := by
  have h2 : 2400 / τ ≤ czero τ := Nat.le_ceil _
  have h3 : 2400 ≤ 2400 / τ := by rw [le_div_iff₀ hτ]; nlinarith
  linarith

/-- `K_m ≥ 1`. -/
private theorem prelimBounds_Km_ge {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 1 ≤ mBoundConst τ := by
  unfold mBoundConst genPropConst
  have h1 : 0 < (τ / 2) ^ 4 := by positivity
  rw [le_div_iff₀ h1, one_mul]
  have h2 : (τ / 2) ^ 4 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  nlinarith

/-- A family of at most `N^{5/2}` dominated variables at level `D + 5/2` has its union of bad
events of probability at most `N^{−D}`. -/
private theorem prelimBounds_family {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {ι : Type*} [Fintype ι]
    {N : ℕ} {ε D D' : ℝ} (hN : 1 ≤ N) (hcard : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ (5 / 2 : ℝ))
    {ξ ζ : ι → Ω → ℝ} (hζ : ∀ i ω, 0 ≤ ζ i ω) (hD : D + 5 / 2 ≤ D')
    (h : ∀ i, DomAt N ε D' (ξ i) (ζ i)) :
    ℙ {ω | ∃ i, (N : ℝ) ^ ε * ζ i ω < ξ i ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have h' : ∀ i ∈ (Finset.univ : Finset ι), DomAt N ε (D + 5 / 2) (ξ i) (ζ i) := fun i _ =>
    DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) (hζ i) le_rfl hD (h i)
  have := DomAt.measure_exists_lt (Finset.univ : Finset ι) hN (by simpa using hcard) h'
  simpa using this

/-- A single dominated variable at level `D' ≥ D`. -/
private theorem prelimBounds_single {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} {ε D D' : ℝ}
    (hN : 1 ≤ N) {ξ ζ : Ω → ℝ} (hζ : ∀ ω, 0 ≤ ζ ω) (hD : D ≤ D') (h : DomAt N ε D' ξ ζ) :
    ℙ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) hζ le_rfl hD h


private theorem prelimBounds_div_step {T L Q' Ψ n B : ℝ} (hn : 0 < n) (hL : 0 ≤ L)
    (hT : T ≤ Q' * (n * Ψ ^ 2)) (hB : L * (Q' * Ψ ^ 2) ≤ B) : L * T / n ≤ B := by
  rw [mul_div_assoc]
  have h1 : T / n ≤ Q' * Ψ ^ 2 := by
    rw [div_le_iff₀ hn]
    calc T ≤ Q' * (n * Ψ ^ 2) := hT
      _ = Q' * Ψ ^ 2 * n := by ring
  exact (mul_le_mul_of_nonneg_left h1 hL).trans hB

/-- The numerical conditions of the deterministic step at `E = N^{5δ/2}`, `L = N^{δ/8}`,
`K = N^{3δ}`, `b = N^{(C₀/2+2)δ}Ψ` on `𝐃(τ, N)`, under the hypotheses `R1`–`R8` on `N`. -/
private theorem prelimBounds_goodNum {τ c Cn C₀ δ η mI Ψ n : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hC₀ : 3 ≤ C₀) (hCn : 0 < Cn) (hn : 1 ≤ n) (hη0 : 0 < η)
    (hη1 : n ^ (-1 + τ) ≤ η) (hη2 : η ≤ τ⁻¹) (hmI0 : 0 < mI) (hmIK : mI ≤ mBoundConst τ)
    (hmlow : (mBoundConst τ)⁻¹ * η ≤ mI) (hΨ : Ψ = √(mI / (n * η)) + 1 / (n * η))
    (R1 : mBoundConst τ ≤ n ^ (5 / 2 * δ))
    (R3 : 16 * τ⁻¹ ^ 2 * Cn * n ^ (11 / 4 * δ) ≤ n ^ τ)
    (R4 : (8 * τ⁻¹ ^ 4 * Cn + 16 * τ⁻¹ ^ 5 * Cn + 128 * τ⁻¹ ^ 4 * Cn ^ 2 +
      3 * τ⁻¹ ^ 2 * mBoundConst τ) * n ^ ((C₀ + 9 / 4) * δ) ≤ n ^ ((C₀ + 15 / 4) * δ))
    (R5 : (√(mBoundConst τ) + 1) * n ^ ((C₀ / 2 + 2) * δ) ≤ n ^ (τ / 2))
    (R6 : τ⁻¹ * (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ (mBoundConst τ) + 8) * n ^ (5 / 2 * δ) ≤
      n ^ (3 * δ))
    (R7 : 8 * τ⁻¹ ^ 3 * (Cn + 1) * n ^ (δ / 4) ≤ n ^ (3 * δ))
    (R8 : 2 * n ^ (6 * δ) ≤ n ^ (τ / 2)) :
    (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) * (n ^ (δ / 8)) ^ 2 *
        (2 * τ⁻¹ ^ 2 * Cn / η) / n ≤ 1 / 4 ∧
    2 * τ⁻¹ ^ 2 * Cn / η *
      (2 * (τ⁻¹ ^ 2 * (n ^ (δ / 4) * (n ^ (2 * δ) * (mI + n ^ (C₀ * δ) * Ψ)))) +
        2 * (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) * (n ^ (δ / 8)) ^ 2 *
          (2 * τ⁻¹ ^ 2) / n + 2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / η)) +
        8 * (n ^ (δ / 8)) ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) *
          (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) ^ 2 / n) + 2 * τ⁻¹ ^ 2 ≤
      n * (n ^ ((C₀ / 2 + 2) * δ) * Ψ) ^ 2 ∧
    (n ^ (δ / 8)) ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η *
        (2 * (τ⁻¹ ^ 2 * (n ^ (δ / 4) * (n ^ (2 * δ) * (mI + n ^ (C₀ * δ) * Ψ)))) +
        2 * (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) * (n ^ (δ / 8)) ^ 2 *
          (2 * τ⁻¹ ^ 2) / n + 2 * τ⁻¹ ^ 2 / (2 * (2 * τ⁻¹ ^ 2 * Cn / η)) +
        8 * (n ^ (δ / 8)) ^ 2 * (2 * τ⁻¹ ^ 2 * Cn / η) *
          (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) ^ 2 / n) + 2 * τ⁻¹ ^ 2) / n ≤
      (n ^ ((C₀ / 2 + 2) * δ) * Ψ) ^ 2 ∧
    0 ≤ n ^ ((C₀ / 2 + 2) * δ) * Ψ ∧ n ^ ((C₀ / 2 + 2) * δ) * Ψ ≤ 1 ∧
    τ⁻¹ * (τ⁻¹ ^ 2 * (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + max c⁻¹ (mBoundConst τ)) +
        3 * (n ^ (2 * (δ / 4)) * n ^ (2 * δ) + mBoundConst τ) +
        2 * (n ^ (2 * (δ / 4)) * n ^ (2 * δ))) ≤ n ^ (3 * δ) ∧
    2 * n ^ (δ / 8) * √(τ⁻¹ * n * (2 * τ⁻¹ ^ 2 * Cn / η * n ^ (3 * δ) + 2 * τ⁻¹ ^ 2)) / n ≤
      n ^ (3 * δ) * n ^ (-τ / 2) ∧
    n ^ (3 * δ) * n ^ (-τ / 2) ≤ 1 / (2 * n ^ (3 * δ)) := by
  have hn0 : 0 < n := by linarith
  have hKm := prelimBounds_Km_ge hτ hτ1
  obtain ⟨hX, hXΨ, hmΨ, h1K, hΨn, hΨup, hΨ0, hn1⟩ :=
    prelimBounds_psi hτ hτ1 hKm hn hη0 hη1 hη2 hmI0 hmIK hmlow hΨ
  obtain ⟨hEL2, hEL, -, -⟩ := prelimBounds_numEL (C₀ := C₀) (δ := δ) (Km := mBoundConst τ)
    (E := n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (lam := n ^ (δ / 8)) (n := n) hδ hC₀ hn rfl rfl R1
    (by linarith)
  have h1PX : mI * (1 / (n * η)) ≤ Ψ ^ 2 := by rw [← div_eq_mul_one_div]; exact hmΨ
  have h2PX : Ψ * (1 / (n * η)) ≤ Ψ ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hXΨ hΨ0.le
  have hPX := prelimBounds_numPX (C₀ := C₀) (δ := δ) (mI := mI) (Ψ := Ψ)
    (P := n ^ (δ / 4) * (n ^ (2 * δ) * (mI + n ^ (C₀ * δ) * Ψ))) (X := 1 / (n * η)) (n := n)
    hδ hC₀ hn rfl h1PX h2PX
  have hQ1 : 1 ≤ n ^ ((C₀ + 9 / 4) * δ) :=
    Real.one_le_rpow hn (mul_nonneg (by linarith) hδ.le)
  have hS2 := prelimBounds_num2 (τ := τ) (Cn := Cn) (Km := mBoundConst τ) (η := η) (Ψ := Ψ)
    (E := n ^ (2 * (δ / 4)) * n ^ (2 * δ))
    (P := n ^ (δ / 4) * (n ^ (2 * δ) * (mI + n ^ (C₀ * δ) * Ψ))) (lam := n ^ (δ / 8)) (n := n)
    (Q := n ^ ((C₀ + 9 / 4) * δ)) (Q' := n ^ ((C₀ + 15 / 4) * δ)) (X := 1 / (n * η))
    hτ hCn hKm hn hη0 rfl hXΨ h1K hΨn hQ1 hPX hEL2 hEL R4
  have hb2 : (n ^ ((C₀ / 2 + 2) * δ) * Ψ) ^ 2 = n ^ ((C₀ + 4) * δ) * Ψ ^ 2 := by
    rw [mul_pow, prelimBounds_rpow_sq hn0]; ring_nf
  have hlam2 : (n ^ (δ / 8)) ^ 2 = n ^ (δ / 4) := by rw [prelimBounds_rpow_sq hn0]; ring_nf
  have hmono : n ^ ((C₀ + 15 / 4) * δ) ≤ n ^ ((C₀ + 4) * δ) :=
    Real.rpow_le_rpow_of_exponent_le hn (mul_le_mul_of_nonneg_right (by linarith) hδ.le)
  have hΨsq0 : 0 ≤ n * Ψ ^ 2 := by positivity
  have n1 := prelimBounds_num1 (τ := τ) (Cn := Cn) (δ := δ) (Km := mBoundConst τ) (η := η)
    (E := n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (lam := n ^ (δ / 8)) (n := n) hτ hCn hn hη0 hX rfl rfl
    R1 R3
  have n3 := prelimBounds_num3 (τ := τ) (C₀ := C₀) (δ := δ) (Km := mBoundConst τ) (Ψ := Ψ)
    (b := n ^ ((C₀ / 2 + 2) * δ) * Ψ) (n := n) hn rfl hΨup hΨ0 R5
  have n4 := prelimBounds_num4 (τ := τ) (c := c) (δ := δ) (Km := mBoundConst τ)
    (E := n ^ (2 * (δ / 4)) * n ^ (2 * δ)) (K := n ^ (3 * δ)) (n := n) hτ hKm hδ hn rfl rfl R1 R6
  have n5 := prelimBounds_num5 (τ := τ) (Cn := Cn) (δ := δ) (η := η) (lam := n ^ (δ / 8))
    (K := n ^ (3 * δ)) (n := n) hτ hCn hδ hn hη0 rfl rfl hX hn1 R7
  have n6 := prelimBounds_num6 (τ := τ) (δ := δ) (K := n ^ (3 * δ)) (n := n) hn rfl R8
  refine ⟨n1, ?_, ?_, n3.1, n3.2, n4, n5, n6⟩
  · rw [hb2]
    refine hS2.trans ?_
    calc n ^ ((C₀ + 15 / 4) * δ) * (n * Ψ ^ 2) ≤ n ^ ((C₀ + 4) * δ) * (n * Ψ ^ 2) :=
          mul_le_mul_of_nonneg_right hmono hΨsq0
      _ = n * (n ^ ((C₀ + 4) * δ) * Ψ ^ 2) := by ring
  · refine prelimBounds_div_step hn0 (sq_nonneg _) hS2 ?_
    rw [hb2, hlam2, ← mul_assoc, prelimBounds_rpow_mul hn0]
    ring_nf; exact le_rfl

/-- On the complement of the bad events of (a_priori_1), (a_priori_2), Lemma 4.8 and the large
deviation bounds, under the hypotheses `R1`–`R8` on `N`, every `μ` satisfies `GoodSec8` with
`K = N^{3δ}`, `b = N^{(C₀/2+2)δ}Ψ`. -/
private theorem prelimBounds_good {τ c Cn₀ Cn C₀ δ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) (hδ : 0 < δ)
    (hC₀ : 3 ≤ C₀) (hCn₀ : Cn₀ ≤ Cn) (hCn : 0 < Cn)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hzD : z ∈ specDomain τ N)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (hmK : ‖mFun N (specOf Sig) z‖ ≤ mBoundConst τ)
    (hmlow : (mBoundConst τ)⁻¹ * z.im ≤ (mFun N (specOf Sig) z).im)
    (R1 : mBoundConst τ ≤ (N : ℝ) ^ (5 / 2 * δ))
    (R3 : 16 * τ⁻¹ ^ 2 * Cn * (N : ℝ) ^ (11 / 4 * δ) ≤ (N : ℝ) ^ τ)
    (R4 : (8 * τ⁻¹ ^ 4 * Cn + 16 * τ⁻¹ ^ 5 * Cn + 128 * τ⁻¹ ^ 4 * Cn ^ 2 +
      3 * τ⁻¹ ^ 2 * mBoundConst τ) * (N : ℝ) ^ ((C₀ + 9 / 4) * δ) ≤ (N : ℝ) ^ ((C₀ + 15 / 4) * δ))
    (R5 : (√(mBoundConst τ) + 1) * (N : ℝ) ^ ((C₀ / 2 + 2) * δ) ≤ (N : ℝ) ^ (τ / 2))
    (R6 : τ⁻¹ * (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ (mBoundConst τ) + 8) * (N : ℝ) ^ (5 / 2 * δ) ≤
      (N : ℝ) ^ (3 * δ))
    (R7 : 8 * τ⁻¹ ^ 3 * (Cn + 1) * (N : ℝ) ^ (δ / 4) ≤ (N : ℝ) ^ (3 * δ))
    (R8 : 2 * (N : ℝ) ^ (6 * δ) ≤ (N : ℝ) ^ (τ / 2))
    (r1 : ‖testBilin v (lawMat Sig A z) v‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm v))
    (r2 : ∀ j, ‖testBilin v (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) * testNorm v *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))))
    (r3 : ∀ jk : Fin M × Fin M, ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.1))
      (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.2))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.1)) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.2))))
    (r4 : ∀ ν, ‖testBilin (eI (Sum.inr ν)) (lawMat Sig A z) (eI (Sum.inr ν))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) * testNorm (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) *
        testNorm (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ)))
    (r5 : ImGvv Sig A z v ≤ (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
      ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)))
    (r6 : ∀ j, ImGvv Sig A z ((testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))⁻¹ •
        (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))) ≤ (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
      ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)))
    (r7 : ‖Aᵀ * A‖ ≤ Cn₀)
    (r8 : ∀ μ, ‖linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ)‖ ≤
      (N : ℝ) ^ (δ / 8) * ldeLinBound N (colC Sig A z (vbar Sig v) μ))
    (r9 : ∀ μj : Fin N × Fin M, ‖linForm (colC Sig A z (eI (Sum.inl μj.2)) μj.1)
      (fun k => A k μj.1)‖ ≤
        (N : ℝ) ^ (δ / 8) * ldeLinBound N (colC Sig A z (eI (Sum.inl μj.2)) μj.1))
    (r10 : ∀ μ, ‖∑ i, ∑ j ∈ Finset.univ.erase i,
      ((A i μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl i) (Sum.inl j) * ((A j μ : ℝ) : ℂ)‖ ≤
      (N : ℝ) ^ (δ / 8) * ldeOffBound N (fun i j => Gmu Sig A z μ (Sum.inl i) (Sum.inl j)))
    (r11 : ∀ μ, ‖∑ i, Gmu Sig A z μ (Sum.inl i) (Sum.inl i) *
      (((A i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ ≤
      (N : ℝ) ^ (δ / 8) * ldeDiagBound N (fun i => Gmu Sig A z μ (Sum.inl i) (Sum.inl i)))
    (μ : Fin N) :
    GoodSec8 τ ((N : ℝ) ^ (3 * δ)) ((N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Psi N (specOf Sig) z) Cn
      Sig A z v μ := by
  have hSig := hS.posDef
  obtain ⟨hη0, -, -, hη1, hη2⟩ := hzD
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hKm := prelimBounds_Km_ge hτ hτ1
  obtain ⟨-, -, -, -, hσ⟩ := prelimBounds_diag hSig
  have hmI0 := (mFun_spec N _ (fun i => (hσ i).le) hη0).1
  have hmIK : (mFun N (specOf Sig) z).im ≤ mBoundConst τ := (Complex.im_le_norm _).trans hmK
  obtain ⟨n1, n2a, n2b, n3, n3', n4, n5, n6⟩ := prelimBounds_goodNum hτ hτ1 hδ hC₀ hCn hn hη0 hη1
    hη2 hmI0 hmIK hmlow rfl R1 R3 R4 R5 R6 R7 R8
  have hv1 : testNorm v * testNorm v = 1 := by rw [hv, mul_one]
  have h1 : ‖testBilin v (lawMat Sig A z) v‖ ≤ (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) := by
    have := r1; rw [mul_assoc _ (testNorm v), hv1, mul_one] at this; exact this
  have h2 : ∀ j, ‖testBilin v (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) := by
    intro j; have := r2 j; rw [hv, mul_one, ← mul_assoc] at this; exact this
  have h3 : ∀ j k, ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) (lawMat Sig A z)
      (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl k)) := by
    intro j k; have := r3 (j, k); rw [← mul_assoc, ← mul_assoc] at this; exact this
  have h4 : ∀ ν, ‖testBilin (eI (Sum.inr ν)) (lawMat Sig A z) (eI (Sum.inr ν))‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) := by
    intro ν; have := r4 ν
    rw [prelimBounds_testNorm_eI, mul_one, mul_one] at this; exact this
  have hP0 : 0 ≤ (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
      ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)) := by
    have : 0 < Psi N (specOf Sig) z := by
      unfold Psi; have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
      linarith [Real.sqrt_nonneg ((mFun N (specOf Sig) z).im / (N * z.im))]
    positivity
  have h6 : ∀ j, (ent (G Sig A z) (eI (Sum.inl j)) (eI (Sum.inl j))).im ≤
      τ⁻¹ ^ 2 * ((N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
        ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z))) := by
    intro j
    rw [(prelimBounds_wj hSig A z j).2]
    have hSe := prelimBounds_testNorm_SigU hS hτ hτ1 (eI (Sum.inl j) : Fin M ⊕ Fin N → ℝ)
    rw [prelimBounds_testNorm_eI, mul_one] at hSe
    have hSe2 : testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) ^ 2 ≤ τ⁻¹ ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hSe 2
    exact (mul_le_mul_of_nonneg_left (r6 j) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hSe2 hP0)
  exact prelimBounds_det hS hτ hτ1 hc A hη0 v hv hn0 hM hOne hmK hKm hCn (by positivity)
    (by positivity) h1 h2 h3 h4 r5 h6 (r7.trans hCn₀) r8 (fun μ j => r9 (μ, j)) r10 r11 n1 rfl
    n2a n2b n3 n3' n4 n5 n6 μ


/-- The union of eleven bad events of probability `≤ N^{−(D_A − 7/2)}` has probability
`≤ N^{−(D_A − 4)}` once `11 ≤ N^{1/2}`. -/
private theorem prelimBounds_final {N : ℕ} {DA : ℝ} (hN : 1 ≤ N)
    (R10 : 11 ≤ (N : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ _i : Fin 11, ENNReal.ofReal ((N : ℝ) ^ (-(DA - 7 / 2))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(DA - 4))) := by
  have hn0 : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e : ((11 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 11 := by simp
  rw [e, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (N : ℝ) ^ (-(DA - 4)) = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(DA - 7 / 2)) := by
    rw [prelimBounds_rpow_mul hn0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right R10 (Real.rpow_nonneg hn0.le _)

/-- The index sets of the events have at most `N^{5/2}` elements. -/
private theorem prelimBounds_cards {τ n m : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hn : 1 ≤ n)
    (hm0 : 0 ≤ m) (hm : m ≤ τ⁻¹ * n) (R9 : τ⁻¹ ^ 2 ≤ n ^ (1 / 2 : ℝ)) :
    m ≤ n ^ (5 / 2 : ℝ) ∧ m * m ≤ n ^ (5 / 2 : ℝ) ∧ n ≤ n ^ (5 / 2 : ℝ) ∧
      n * m ≤ n ^ (5 / 2 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hτ2 : τ⁻¹ ≤ τ⁻¹ ^ 2 := le_self_pow₀ hτi (by norm_num)
  have e : n ^ (5 / 2 : ℝ) = n ^ (1 / 2 : ℝ) * (n * n) := by
    rw [show (5 / 2 : ℝ) = 1 / 2 + 2 by norm_num, Real.rpow_add hn0]
    norm_num [sq]
  have hh : 1 ≤ n ^ (1 / 2 : ℝ) := Real.one_le_rpow hn (by norm_num)
  have hm1 : m ≤ n ^ (1 / 2 : ℝ) * n := by
    calc m ≤ τ⁻¹ * n := hm
      _ ≤ n ^ (1 / 2 : ℝ) * n := mul_le_mul_of_nonneg_right (hτ2.trans R9) hn0.le
  have hnn : n ≤ n * n := le_mul_of_one_le_left hn0.le hn
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m ≤ n ^ (1 / 2 : ℝ) * n := hm1
      _ ≤ n ^ (1 / 2 : ℝ) * (n * n) := mul_le_mul_of_nonneg_left hnn (by positivity)
  · calc m * m ≤ (τ⁻¹ * n) * (τ⁻¹ * n) := mul_le_mul hm hm hm0 (by positivity)
      _ = τ⁻¹ ^ 2 * (n * n) := by ring
      _ ≤ n ^ (1 / 2 : ℝ) * (n * n) := mul_le_mul_of_nonneg_right R9 (by positivity)
  · calc n ≤ n * n := hnn
      _ ≤ n ^ (1 / 2 : ℝ) * (n * n) := le_mul_of_one_le_left (by positivity) hh
  · calc n * m ≤ n * (n ^ (1 / 2 : ℝ) * n) := mul_le_mul_of_nonneg_left hm1 hn0.le
      _ = n ^ (1 / 2 : ℝ) * (n * n) := by ring

/-- `Ψ ≥ 0`. -/
private theorem prelimBounds_Psi_nonneg {σ : Fin M → ℝ} {z : ℂ} (hz : 0 < z.im) :
    0 ≤ Psi N σ z := by
  unfold Psi
  have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

/-- `Θ` has high probability: on (A_{m−1}) at `(δ/4, D_A)` and `z ∈ S_m`, with `κ = 3δ`,
`b = N^{(C₀/2+2)δ} Ψ`, the event `⋂_μ Θ_μ` holds with probability `≥ 1 − N^{−(D_A − 4)}`
((BGX_est), (im_BGB), (z-Y_bound), Lemma 8.9's inputs). -/
theorem goodSec8_highProb (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ Cn : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          HighProbAt N (DA - 4) {ω | ∀ μ, GoodSec8 τ ((N : ℝ) ^ (3 * δ))
            ((N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Psi N (specOf Sig) z) Cn Sig (X ω) z v μ} := by
  have hC₀' : 2400 ≤ C₀ := (prelimBounds_czero_ge hτ hτ1).trans hC₀
  have hC₀3 : (3 : ℝ) ≤ C₀ := by linarith
  have hδτ : 2400 * δ ≤ τ / 4 := (mul_le_mul_of_nonneg_right hC₀' hδ.le).trans hC₀δ
  obtain ⟨Cn₀, hCn₀⟩ := norm_XtX_le hτ hτ1
  set Cn := max Cn₀ 1 with hCndef
  have hCn : 0 < Cn := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Km := mBoundConst τ with hKmdef
  refine ⟨Cn, ?_⟩
  obtain ⟨Na, hNa⟩ := cor_rough_bound' τ c C C₀ δ (δ / 4) DA hτ hτ1 hc hδ (by linarith) hC₀δ
    (by positivity)
  obtain ⟨Nl, hNl⟩ := prelimBounds_lde C (ε := δ / 8) (by positivity) DA
  obtain ⟨Nn, hNn⟩ := hCn₀ C (DA - 7 / 2)
  obtain ⟨N1, R1⟩ := prelimBounds_eventually Km 0 (5 / 2 * δ) (by positivity)
  obtain ⟨N3, R3⟩ := prelimBounds_eventually (16 * τ⁻¹ ^ 2 * Cn) (11 / 4 * δ) τ (by linarith)
  obtain ⟨N4, R4⟩ := prelimBounds_eventually
    (8 * τ⁻¹ ^ 4 * Cn + 16 * τ⁻¹ ^ 5 * Cn + 128 * τ⁻¹ ^ 4 * Cn ^ 2 + 3 * τ⁻¹ ^ 2 * Km)
    ((C₀ + 9 / 4) * δ) ((C₀ + 15 / 4) * δ) (mul_lt_mul_of_pos_right (by linarith) hδ)
  obtain ⟨N5, R5⟩ := prelimBounds_eventually (√Km + 1) ((C₀ / 2 + 2) * δ) (τ / 2)
    (by nlinarith)
  obtain ⟨N6, R6⟩ := prelimBounds_eventually (τ⁻¹ * (τ⁻¹ ^ 2 + τ⁻¹ ^ 2 * max c⁻¹ Km + 8))
    (5 / 2 * δ) (3 * δ) (by linarith)
  obtain ⟨N7, R7⟩ := prelimBounds_eventually (8 * τ⁻¹ ^ 3 * (Cn + 1)) (δ / 4) (3 * δ)
    (by linarith)
  obtain ⟨N8, R8⟩ := prelimBounds_eventually 2 (6 * δ) (τ / 2) (by linarith)
  obtain ⟨N9, R9⟩ := prelimBounds_eventually (τ⁻¹ ^ 2) 0 (1 / 2) (by norm_num)
  obtain ⟨N10, R10⟩ := prelimBounds_eventually 11 0 (1 / 2) (by norm_num)
  refine ⟨max (max (max Na (max Nl Nn)) (max (max N1 N3) (max N4 N5)))
    (max (max (max N6 N7) (max N8 N9)) (max N10 1)), ?_⟩
  intro N hN M Sig S P m hset hm hPA Ω _ _ X hX hP z hz v hv
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hNa', hNl', hNn'⟩, ⟨hN1', hN3'⟩, hN4', hN5'⟩, ⟨⟨hN6', hN7'⟩, hN8', hN9'⟩, hN10', hN1⟩ :=
    hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hS := hset.sigma
  have hSig := hS.posDef
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hn0] at this
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hη0 : 0 < z.im := hzD.1
  obtain ⟨-, hmK, hmlow⟩ := gen_prop_m_specDomain (prelimBounds_density hset hN1) hzD
  have hOne := hset.oneXm z hzS
  have R1' := R1 N hN1'
  rw [Real.rpow_zero, mul_one] at R1'
  have R9' := R9 N hN9'
  rw [Real.rpow_zero, mul_one] at R9'
  have R10' := R10 N hN10'
  rw [Real.rpow_zero, mul_one] at R10'
  obtain ⟨hcM, hcMM, hcN, hcNM⟩ := prelimBounds_cards hτ hτ1 hn (Nat.cast_nonneg M) hM R9'
  obtain ⟨hA1, hA2⟩ := hNa N hNa' M Sig S P m hset hm hPA Ω X hX hP z hz
  have hL := hNl N hNl' M Sig z X hX
  have hNorm := hNn N hNn' M X hX hM
  -- the bad events
  have hΨ0 : 0 ≤ Psi N (specOf Sig) z := prelimBounds_Psi_nonneg hη0
  have hmI0 : 0 ≤ (mFun N (specOf Sig) z).im := by
    obtain ⟨-, -, -, -, hσ⟩ := prelimBounds_diag hSig
    exact (mFun_spec N _ (fun i => (hσ i).le) hη0).1.le
  have hpw : ∀ r : ℝ, 0 ≤ (N : ℝ) ^ r := fun r => Real.rpow_nonneg hn0.le r
  have hTN : ∀ x : Fin M ⊕ Fin N → ℝ, 0 ≤ testNorm x := fun x => Real.sqrt_nonneg _
  set wj : Fin M → Fin M ⊕ Fin N → ℝ := fun j =>
    (testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)))⁻¹ •
      (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j)) with hwj
  set B : Fin 11 → Set Ω := ![
    {ω | (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm v) <
      ‖testBilin v (lawMat Sig (X ω) z) v‖},
    {ω | ∃ j : Fin M, (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) * testNorm v *
      testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))) <
      ‖testBilin v (lawMat Sig (X ω) z) (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl j))‖},
    {ω | ∃ jk : Fin M × Fin M, (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) *
      testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.1)) *
      testNorm (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.2))) <
      ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.1)) (lawMat Sig (X ω) z)
        (SigU (n := Fin N) Sig *ᵥ eI (Sum.inl jk.2))‖},
    {ω | ∃ ν : Fin N, (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ (2 * δ) *
      testNorm (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) *
      testNorm (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ)) <
      ‖testBilin (eI (Sum.inr ν)) (lawMat Sig (X ω) z) (eI (Sum.inr ν))‖},
    {ω | (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
      ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)) <
      ImGvv Sig (X ω) z v},
    {ω | ∃ j : Fin M, (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) *
      ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)) <
      ImGvv Sig (X ω) z (wj j)},
    {ω | ‖(X ω)ᵀ * X ω‖ ≤ Cn₀}ᶜ,
    {ω | ∃ μ : Fin N, (N : ℝ) ^ (δ / 8) * ldeLinBound N (colC Sig (X ω) z (vbar Sig v) μ) <
      ‖linForm (colC Sig (X ω) z (vbar Sig v) μ) (fun j => X ω j μ)‖},
    {ω | ∃ μj : Fin N × Fin M, (N : ℝ) ^ (δ / 8) *
      ldeLinBound N (colC Sig (X ω) z (eI (Sum.inl μj.2)) μj.1) <
      ‖linForm (colC Sig (X ω) z (eI (Sum.inl μj.2)) μj.1) (fun k => X ω k μj.1)‖},
    {ω | ∃ μ : Fin N, (N : ℝ) ^ (δ / 8) *
      ldeOffBound N (fun i j => Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl j)) <
      ‖∑ i, ∑ j ∈ Finset.univ.erase i, ((X ω i μ : ℝ) : ℂ) *
        Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl j) * ((X ω j μ : ℝ) : ℂ)‖},
    {ω | ∃ μ : Fin N, (N : ℝ) ^ (δ / 8) *
      ldeDiagBound N (fun i => Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl i)) <
      ‖∑ i, Gmu Sig (X ω) z μ (Sum.inl i) (Sum.inl i) *
        (((X ω i μ : ℝ) : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖}] with hBdef
  have hD1 : DA - 7 / 2 + 5 / 2 ≤ DA - 1 := by linarith
  have hD2 : DA - 7 / 2 + 5 / 2 ≤ DA := by linarith
  have hB : ∀ i, ℙ (B i) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(DA - 7 / 2))) := by
    intro i
    fin_cases i
    · exact prelimBounds_single hN1 (fun _ => mul_nonneg (mul_nonneg (hpw _) (hTN _)) (hTN _))
        (by linarith) (hA1 v v)
    · exact prelimBounds_family (ι := Fin M) hN1 (by simpa using hcM)
        (fun _ _ => mul_nonneg (mul_nonneg (hpw _) (hTN _)) (hTN _)) hD1 (fun j => hA1 v _)
    · exact prelimBounds_family (ι := Fin M × Fin M) hN1 (by simpa using hcMM)
        (fun _ _ => mul_nonneg (mul_nonneg (hpw _) (hTN _)) (hTN _)) hD1 (fun jk => hA1 _ _)
    · exact prelimBounds_family (ι := Fin N) hN1 (by simpa using hcN)
        (fun _ _ => mul_nonneg (mul_nonneg (hpw _) (hTN _)) (hTN _)) hD1 (fun ν => hA1 _ _)
    · exact prelimBounds_single hN1
        (fun _ => mul_nonneg (hpw _) (add_nonneg hmI0 (mul_nonneg (hpw _) hΨ0)))
        (by linarith) (hA2 v hv)
    · exact prelimBounds_family (ι := Fin M) hN1 (by simpa using hcM)
        (fun _ _ => mul_nonneg (hpw _) (add_nonneg hmI0 (mul_nonneg (hpw _) hΨ0))) hD2
        (fun j => hA2 (wj j) (prelimBounds_wj hSig (0 : Matrix (Fin M) (Fin N) ℝ) z j).1)
    · exact hNorm
    · exact prelimBounds_family (ι := Fin N) hN1 (by simpa using hcN)
        (fun _ _ => Real.sqrt_nonneg _) hD2 (fun μ => (hL μ).1 (vbar Sig v))
    · exact prelimBounds_family (ι := Fin N × Fin M) hN1 (by simpa using hcNM)
        (fun _ _ => Real.sqrt_nonneg _) hD2 (fun μj => (hL μj.1).1 (eI (Sum.inl μj.2)))
    · exact prelimBounds_family (ι := Fin N) hN1 (by simpa using hcN)
        (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) hD2
        (fun μ => (hL μ).2.1)
    · exact prelimBounds_family (ι := Fin N) hN1 (by simpa using hcN)
        (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) hD2
        (fun μ => (hL μ).2.2)
  have hsub : {ω | ∀ μ, GoodSec8 τ ((N : ℝ) ^ (3 * δ))
      ((N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Psi N (specOf Sig) z) Cn Sig (X ω) z v μ}ᶜ ⊆
      ⋃ i, B i := by
    intro ω hω
    by_contra hU
    simp only [Set.mem_iUnion, not_exists] at hU
    apply hω
    have hU0 : ω ∉ B 0 := hU 0
    have hU1 : ω ∉ B 1 := hU 1
    have hU2 : ω ∉ B 2 := hU 2
    have hU3 : ω ∉ B 3 := hU 3
    have hU4 : ω ∉ B 4 := hU 4
    have hU5 : ω ∉ B 5 := hU 5
    have hU6 : ω ∉ B 6 := hU 6
    have hU7 : ω ∉ B 7 := hU 7
    have hU8 : ω ∉ B 8 := hU 8
    have hU9 : ω ∉ B 9 := hU 9
    have hU10 : ω ∉ B 10 := hU 10
    simp only [hBdef, Matrix.cons_val, Set.mem_ofPred_eq, not_exists, not_lt, Set.mem_compl_iff,
      not_not] at hU0 hU1 hU2 hU3 hU4 hU5 hU6 hU7 hU8 hU9 hU10
    intro μ
    exact prelimBounds_good hS hτ hτ1 hc hδ hC₀3 (le_max_left _ _) hCn (X ω) hzD v hv hN1 hM
      hOne hmK hmlow R1' (R3 N hN3') (R4 N hN4') (R5 N hN5') (R6 N hN6') (R7 N hN7')
      (R8 N hN8') hU0 hU1 hU2 hU3 hU4 hU5 hU6 hU7 hU8 hU9 hU10 μ
  unfold HighProbAt
  calc ℙ _ ≤ ℙ (⋃ i, B i) := measure_mono hsub
    _ ≤ ∑ i, ℙ (B i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 11, ENNReal.ofReal ((N : ℝ) ^ (-(DA - 7 / 2))) :=
        Finset.sum_le_sum fun i _ => hB i
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(DA - 4))) := prelimBounds_final hN1 R10'

/-- (whA_rough3) on `Θ`: `|A(w, σ)| ≤ (2K)^{n(w)+1}` (with `b ≤ 1 ≤ K`). -/
theorem whA_rough3 {τ K b Cn : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {z : ℂ} {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1)
    (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (h : GoodSec8 τ K b Cn Sig A z v μ) (i : Fin M) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    ‖tagA Sig A z v i μ n w σ‖ ≤ (2 * K) ^ (n + 1) := by
  have _ := hv
  have hK0 : 0 ≤ K := by linarith
  cases n with
  | zero =>
    rw [zero_add, pow_one]
    have hcV := h.col_v.1
    have hrV := h.col_v.2
    generalize hs : σ 0 = s
    simp only [tagA, hs]
    fin_cases s
    · simp only [emptyForms, emptyScal, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.map_nil,
        List.prod_nil, mul_one]
      have := h.ent_vv
      simp only [emptyScal, ↓reduceIte] at this
      linarith
    · simp only [emptyForms, emptyScal, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, norm_mul]
      have : ‖linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ‖ *
          ‖linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ‖ ≤ b * b :=
        mul_le_mul hcV hrV (norm_nonneg _) hb0
      nlinarith
    · simp only [emptyForms, emptyScal, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, neg_mul, one_mul,
        norm_neg, prelimBounds_linForm_add]
      have := norm_add_le (linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ)
        (linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ)
      linarith
  | succ k =>
    simp only [tagA]
    rw [norm_prod]
    calc ∏ l : Fin (k + 2), ‖brack Sig A z v i μ (factorX w l) (factorY w l) (σ l)‖
        ≤ ∏ _l : Fin (k + 2), 2 * K := by
          gcongr with l
          exact (prelimBounds_brack_le hK hb h i _ _ _ (prelimBounds_not_VV w l)).trans
            (by linarith)
      _ = (2 * K) ^ (k + 1 + 1) := by simp

/-- (whA_rough4) on `Θ`: for the empty word, `|A(w₀, σ)| ≤ 4 K_m (b + F_v + F_{e_μ})` when
`|Π_μμ| = |m| ≤ K_m`. -/
theorem whA_rough4 {τ K b Cn Km : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hb0 : 0 ≤ b) (hb : b ≤ 1) (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km)
    (h : GoodSec8 τ K b Cn Sig A z v μ) (i : Fin M) (w : Word 0) (σ : Fin 1 → Fin 3) :
    ‖tagA Sig A z v i μ 0 w σ‖ ≤
      4 * Km * (b + Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ))) := by
  set a := linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ with ha
  set a' := linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ with ha'
  have hcV : ‖a‖ ≤ b := h.col_v.1
  have hrV : ‖a'‖ ≤ b := h.col_v.2
  set Fe := Fv Sig A z (eI (Sum.inr μ)) with hFe
  set F := Fv Sig A z v with hF
  have hF0 : 0 ≤ F := norm_nonneg _
  have hFe0 : 0 ≤ Fe := norm_nonneg _
  have hFe' : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ = Fe := by
    rw [hFe, Fv, prelimBounds_vbar_eI_inr, ent_eI_eI, Matrix.sub_apply]
  have hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km + Fe := by
    have := norm_add_le (G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
      (PiZ N Sig z (Sum.inr μ) (Sum.inr μ))
    rw [sub_add_cancel, hFe'] at this
    linarith
  have hab : ‖a‖ * ‖a'‖ ≤ b * b := mul_le_mul hcV hrV (norm_nonneg _) hb0
  have hRHS : b ≤ 4 * Km * (b + F + Fe) := by nlinarith
  generalize hs : σ 0 = s
  simp only [tagA, hs]
  fin_cases s
  · simp only [emptyForms, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.map_nil, List.prod_nil,
      mul_one]
    rw [prelimBounds_emptyScal_eq hSig A hz v μ]
    set g := G Sig A z (Sum.inr μ) (Sum.inr μ)
    set ν : ℂ := ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ)
    have hν : ‖ν‖ ≤ 1 := by simpa [ν, Complex.norm_real] using hv
    have hν0 : 0 ≤ ‖ν‖ := norm_nonneg _
    have h1 : ‖ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)‖ = F := rfl
    have h2 : ‖ν ^ 2 * (g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))‖ ≤ Fe := by
      rw [norm_mul, norm_pow, hFe']
      have : ‖ν‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h3 : ‖g * (a * a' - ν * (a + a'))‖ ≤ (Km + Fe) * (3 * b) := by
      rw [norm_mul]
      refine mul_le_mul hg ?_ (norm_nonneg _) (by linarith)
      calc ‖a * a' - ν * (a + a')‖ ≤ ‖a‖ * ‖a'‖ + ‖ν‖ * (‖a‖ + ‖a'‖) := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le _ _) hν0)
        _ ≤ b * b + 1 * (b + b) := by
            have : ‖ν‖ * (‖a‖ + ‖a'‖) ≤ 1 * (b + b) :=
              mul_le_mul hν (add_le_add hcV hrV) (by positivity) zero_le_one
            linarith
        _ ≤ 3 * b := by nlinarith
    calc _ ≤ ‖ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v) -
            ν ^ 2 * (g - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))‖ +
          ‖g * (a * a' - ν * (a + a'))‖ := norm_sub_le _ _
      _ ≤ (F + Fe) + (Km + Fe) * (3 * b) := by
          refine add_le_add ((norm_sub_le _ _).trans ?_) h3
          rw [h1]; linarith
      _ ≤ 4 * Km * (b + F + Fe) := by nlinarith
  · simp only [emptyForms, emptyScal, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, norm_mul]
    nlinarith
  · simp only [emptyForms, emptyScal, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, neg_mul, one_mul,
      norm_neg, prelimBounds_linForm_add]
    have := norm_add_le a a'
    nlinarith


/-- (bound_sum_hat) on `GoodMinor`: `∑_j |c_j|^d ≤ τ⁻¹ N b^{d ∧ 2} K^{d − 2}` for a coefficient
vector with `|c_j| ≤ K` and `∑_j |c_j|² ≤ N b²`. -/
theorem bound_sum_hat {τ K b : ℝ} {N : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hK : 1 ≤ K) (hb : 0 ≤ b)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (c : Fin M → ℂ) (hc : ∀ j, ‖c j‖ ≤ K)
    (hc2 : ∑ j, ‖c j‖ ^ 2 ≤ N * b ^ 2) (d : ℕ) :
    ∑ j, ‖c j‖ ^ d ≤ τ⁻¹ * N * b ^ (min d 2) * K ^ (d - 2) := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNb : 0 ≤ (N : ℝ) * b ^ 2 := by positivity
  rcases d with _ | _ | _ | d
  · simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Nat.zero_sub, Nat.zero_le, min_eq_left]
    exact hM
  · simp only [zero_add, pow_one, Nat.reduceSub, pow_zero, mul_one]
    have hmin : min 1 2 = 1 := rfl
    rw [hmin, pow_one]
    have hs : (∑ j, ‖c j‖) ^ 2 ≤ (M : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M))) (f := fun j => ‖c j‖)
      simpa using this
    have h0 : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h1 : (M : ℝ) * ∑ j, ‖c j‖ ^ 2 ≤ (τ⁻¹ * N) * (N * b ^ 2) :=
      mul_le_mul hM hc2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    have h2 : (τ⁻¹ * N) * (N * b ^ 2) ≤ (τ⁻¹ * N * b) ^ 2 := by
      have : τ⁻¹ ≤ τ⁻¹ ^ 2 := by nlinarith
      have e : (τ⁻¹ * N * b) ^ 2 = τ⁻¹ ^ 2 * (N * (N * b ^ 2)) := by ring
      rw [e, show (τ⁻¹ * N) * (N * b ^ 2) = τ⁻¹ * (N * (N * b ^ 2)) by ring]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : 0 ≤ τ⁻¹ * N * b := by positivity
    nlinarith [hs, h1, h2]
  · simp only [Nat.reduceAdd, Nat.sub_self, pow_zero, mul_one]
    have hmin : min 2 2 = 2 := rfl
    rw [hmin]
    calc ∑ j, ‖c j‖ ^ 2 ≤ N * b ^ 2 := hc2
      _ ≤ τ⁻¹ * N * b ^ 2 := by
          rw [mul_assoc]; exact le_mul_of_one_le_left hNb hτi
  · have hmin : min (d + 1 + 1 + 1) 2 = 2 := by omega
    have hsub : d + 1 + 1 + 1 - 2 = d + 1 := by omega
    rw [hmin, hsub]
    have hK0 : 0 ≤ K := by linarith
    calc ∑ j, ‖c j‖ ^ (d + 1 + 1 + 1) ≤ ∑ j, K ^ (d + 1) * ‖c j‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [show d + 1 + 1 + 1 = (d + 1) + 2 by omega, pow_add]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) _)
            (by positivity)
      _ = K ^ (d + 1) * ∑ j, ‖c j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K ^ (d + 1) * (N * b ^ 2) := mul_le_mul_of_nonneg_left hc2 (by positivity)
      _ ≤ τ⁻¹ * N * b ^ 2 * K ^ (d + 1) := by
          rw [mul_comm (K ^ (d + 1))]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [mul_assoc]; exact le_mul_of_one_le_left hNb hτi

/-- The coefficients `𝒴_{μ,k} = ∑_{t=k}^{K} (−z−Y)^{−t−1} C(t,k) (−Y)^{t−k}` of (Gmumu_exp2). -/
def calY (z Y : ℂ) (K k : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc k K, (-z - Y)⁻¹ ^ (t + 1) * (t.choose k : ℂ) * (-Y) ^ (t - k)

/-- The truncated geometric expansion `∑_{t ≤ K} Z^t a^{−t−1}` of `(a − Z)⁻¹`, with remainder. -/
private theorem prelimBounds_geom (g a Z : ℂ) (ha : a ≠ 0) (hg : g * (a - Z) = 1) (K : ℕ) :
    g = ∑ t ∈ Finset.range (K + 1), a⁻¹ ^ (t + 1) * Z ^ t + g * (Z * a⁻¹) ^ (K + 1) := by
  have htel : ∀ K : ℕ, (∑ t ∈ Finset.range (K + 1), a⁻¹ ^ (t + 1) * Z ^ t) * (a - Z) =
      1 - (Z * a⁻¹) ^ (K + 1) := by
    intro K
    induction K with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_one, pow_zero, mul_one]
      field_simp
    | succ K ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      have h : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
      linear_combination (Z * a⁻¹) ^ (K + 1) * h
  have h := htel K
  calc g = g * ((∑ t ∈ Finset.range (K + 1), a⁻¹ ^ (t + 1) * Z ^ t) * (a - Z) +
        (Z * a⁻¹) ^ (K + 1)) := by rw [h]; ring
    _ = (∑ t ∈ Finset.range (K + 1), a⁻¹ ^ (t + 1) * Z ^ t) * (g * (a - Z)) +
        g * (Z * a⁻¹) ^ (K + 1) := by ring
    _ = _ := by rw [hg, mul_one]

/-- Binomial expansion and exchange of the sums: `∑_{t ≤ K} a^{−t−1} (Q − Y)^t = ∑_k 𝒴_k Q^k`. -/
private theorem prelimBounds_binom (z Y Q : ℂ) (K : ℕ) :
    ∑ t ∈ Finset.range (K + 1), (-z - Y)⁻¹ ^ (t + 1) * (Q - Y) ^ t =
      ∑ k ∈ Finset.range (K + 1), calY z Y K k * Q ^ k := by
  have h1 : ∀ t, (-z - Y)⁻¹ ^ (t + 1) * (Q - Y) ^ t =
      ∑ k ∈ Finset.range (t + 1),
        (-z - Y)⁻¹ ^ (t + 1) * (t.choose k : ℂ) * (-Y) ^ (t - k) * Q ^ k := by
    intro t
    rw [show Q - Y = Q + -Y by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [h1, calY, Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

/-- (Gmumu_exp2), exact form: `G_μμ = ∑_{k ≤ K} 𝒴_{μ,k} Q_μ^k + G_μμ (Z_μ/(−z−Y_μ))^{K+1}`. -/
theorem gmumu_exp {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (K : ℕ)
    (hY : -z - Ymu Sig A z μ ≠ 0) :
    G Sig A z (Sum.inr μ) (Sum.inr μ) =
      ∑ k ∈ Finset.range (K + 1), calY z (Ymu Sig A z μ) K k * Qmu Sig A z μ ^ k +
        G Sig A z (Sum.inr μ) (Sum.inr μ) *
          ((Qmu Sig A z μ - Ymu Sig A z μ) * (-z - Ymu Sig A z μ)⁻¹) ^ (K + 1) := by
  have hii := Gii hSig A hz μ
  have hg0 := G_diag_ne_zero hSig A hz (Sum.inr μ)
  have hQ : ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ) * Xhat A) (Sum.inr μ) (Sum.inr μ) =
      Qmu Sig A z μ := rfl
  rw [hQ] at hii
  have hg : G Sig A z (Sum.inr μ) (Sum.inr μ) *
      ((-z - Ymu Sig A z μ) - (Qmu Sig A z μ - Ymu Sig A z μ)) = 1 := by
    have e : (-z - Ymu Sig A z μ) - (Qmu Sig A z μ - Ymu Sig A z μ) = -z - Qmu Sig A z μ := by
      ring
    rw [e, ← hii, mul_one_div_cancel hg0]
  rw [← prelimBounds_binom]
  exact prelimBounds_geom _ _ _ hY hg K

/-- (cal_Y_rough): `|Y_μ| + |−z − Y_μ|⁻¹ ≤ C N` deterministically (`Im(−z − Y_μ) ≤ −Im z`). -/
theorem calY_rough {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) :
    (-z - Ymu Sig A z μ).im ≤ -z.im ∧
      ‖Ymu Sig A z μ‖ ≤ (M : ℝ) / N * ‖Sig‖ * (1 + ‖z‖) / z.im := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := Fin.pos μ
    exact_mod_cast this
  have hNc : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  constructor
  · have hY : 0 ≤ (Ymu Sig A z μ).im := by
      unfold Ymu
      rw [hNc, Complex.im_ofReal_mul, Complex.im_sum]
      refine mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun j _ => ?_)
      have := prelimBounds_Gmu_im_nonneg hSig A hz μ (eI (Sum.inl j))
      rwa [ent_eI_eI] at this
    simp only [Complex.sub_im, Complex.neg_im]
    linarith
  · have hj : ∀ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖ ≤ ‖Sig‖ * (1 + ‖z‖) / z.im := by
      intro j
      refine (prelimBounds_Gmu_inl_le hSig A hz μ j).trans ?_
      refine div_le_div_of_nonneg_right ?_ hz.le
      have h1 := (le_abs_self (Sig j j)).trans (prelimBounds_diag_le_norm Sig j)
      have h2 : 0 < Sig j j := hSig.diag_pos
      have h3 : ‖z‖ ≤ 1 + ‖z‖ := by linarith
      calc ‖z‖ * Sig j j ≤ (1 + ‖z‖) * ‖Sig‖ :=
            mul_le_mul h3 h1 h2.le (by positivity)
        _ = ‖Sig‖ * (1 + ‖z‖) := by ring
    unfold Ymu
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ j, Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖
        ≤ (N : ℝ)⁻¹ * ∑ _j : Fin M, ‖Sig‖ * (1 + ‖z‖) / z.im :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j))
            (inv_nonneg.2 hN.le)
      _ = (M : ℝ) / N * ‖Sig‖ * (1 + ‖z‖) / z.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-- The values `C₀(1) = 2400`, `K_1 = 24`. -/
example : czero 1 = 2400 ∧ kTau 1 = 24 := by
  norm_num [czero, kTau]

/-- The numerical condition `45 K_τ + 75 ≤ C₀(τ)/2` for `0 < τ ≤ 1`. -/
example (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 45 * (kTau τ : ℝ) + 75 ≤ czero τ / 2 := by
  have h1 : (kTau τ : ℝ) < 24 / τ + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : 2400 / τ ≤ czero τ := Nat.le_ceil _
  have h3 : 1 ≤ τ⁻¹ := one_le_inv_iff₀.mpr ⟨hτ, hτ1⟩
  rw [div_eq_mul_inv] at h1 h2
  linarith

/-- The parameters `C₀ = C₀(τ)`, `δ = min(ε, τ)/(4 C₀(τ))` satisfy the hypotheses
`C₀(τ) ≤ C₀`, `25 ≤ C₀`, `0 < δ`, `C₀ δ ≤ τ/4` of the §8 statements. -/
example (ε τ : ℝ) (hε : 0 < ε) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    czero τ ≤ czero τ ∧ 25 ≤ czero τ ∧ 0 < deltaTwo ε τ ∧ czero τ * deltaTwo ε τ ≤ τ / 4 := by
  have h2 : 2400 / τ ≤ czero τ := Nat.le_ceil _
  have h3 : 2400 ≤ 2400 / τ := by rw [le_div_iff₀ hτ]; nlinarith
  have hc : 0 < czero τ := by linarith
  have hm : 0 < min ε τ := lt_min hε hτ
  refine ⟨le_rfl, by linarith, by unfold deltaTwo; positivity, ?_⟩
  unfold deltaTwo
  rw [mul_div_assoc', mul_comm, mul_div_mul_comm, div_self hc.ne', mul_one]
  exact div_le_div_of_nonneg_right (min_le_right ε τ) (by norm_num)

/-! ### Instances at `M = N = 2`, `Σ = I`, `z = i`, `μ = 0`, `i = 0` -/

section Checks

open Complex

/-- `goodSec8_highProb` at `τ = 1/2`, `c = 1`, `C_p = 2`, `C₀ = C₀(1/2) = 4800`,
`δ = min(1, 1/2)/(4 C₀(1/2)) = 1/38400`: the parameter hypotheses are discharged, and the
statement is the bound for every `N ≥ N₀`. At `N = 2` the level `b = 2^{(C₀/2+2)δ} Ψ` exceeds
`1`, so the event is meaningful only for large `N`; the model hypotheses stay binders of the
conclusion. -/
example (DA : ℝ) :
    ∃ Cn : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
        (deltaTwo 1 (1 / 2) / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          HighProbAt N (DA - 4) {ω | ∀ μ, GoodSec8 (1 / 2) ((N : ℝ) ^ (3 * deltaTwo 1 (1 / 2)))
            ((N : ℝ) ^ ((czero (1 / 2) / 2 + 2) * deltaTwo 1 (1 / 2)) * Psi N (specOf Sig) z)
            Cn Sig (X ω) z v μ} := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact goodSec8_highProb (1 / 2) 1 (fun _ => 2) (czero (1 / 2)) (deltaTwo 1 (1 / 2)) DA
    (by norm_num) (by norm_num) one_pos (by rw [hd]; norm_num) le_rfl
    (by rw [hc, hd]; norm_num)

/-- `whA_rough3` for the word `𝐢𝛍` with tags `(1, 2)` at `Σ = I`, `z = i`, under the event
`GoodSec8` (kept as a hypothesis). -/
example (K b Cn : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 ⊕ Fin 2 → ℝ) (hK : 1 ≤ K)
    (hb0 : 0 ≤ b) (hb : b ≤ 1)
    (hv : |vbar (1 : Matrix (Fin 2) (Fin 2) ℝ) v (Sum.inr 0)| ≤ 1)
    (h : GoodSec8 (1 / 2) K b Cn (1 : Matrix (Fin 2) (Fin 2) ℝ) A I v 0) :
    ‖tagA (1 : Matrix (Fin 2) (Fin 2) ℝ) A I v 0 0 1 (fun _ => true) ![1, 2]‖ ≤
      (2 * K) ^ (1 + 1) :=
  whA_rough3 hK hb0 hb hv h 0 1 (fun _ => true) ![1, 2]

/-- `whA_rough4` for the empty word with tag `0` at `Σ = I`, `z = i`, under the event `GoodSec8`
(kept as a hypothesis) and `|m| ≤ K_m`. -/
example (K b Cn Km : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 ⊕ Fin 2 → ℝ)
    (hb0 : 0 ≤ b) (hb : b ≤ 1) (hKm : 1 ≤ Km)
    (hv : |vbar (1 : Matrix (Fin 2) (Fin 2) ℝ) v (Sum.inr 0)| ≤ 1)
    (hm : ‖PiZ 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) I (Sum.inr 0) (Sum.inr 0)‖ ≤ Km)
    (h : GoodSec8 (1 / 2) K b Cn (1 : Matrix (Fin 2) (Fin 2) ℝ) A I v 0) (w : Word 0) :
    ‖tagA (1 : Matrix (Fin 2) (Fin 2) ℝ) A I v 0 0 0 w ![0]‖ ≤
      4 * Km * (b + Fv (1 : Matrix (Fin 2) (Fin 2) ℝ) A I v +
        Fv (1 : Matrix (Fin 2) (Fin 2) ℝ) A I (eI (Sum.inr 0))) :=
  whA_rough4 Matrix.PosDef.one (by simp) hb0 hb hKm hv hm h 0 w ![0]

/-- (bound_sum_hat) at `d = 0`, `M = N = 2`, `τ = 1/2`, `K = b = 1`, `c = (1, 1)`:
`2 ≤ τ⁻¹ N = 4`. -/
example : ∑ j : Fin 2, ‖(fun _ => (1 : ℂ)) j‖ ^ 0 ≤
    (1 / 2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) * 1 ^ (min 0 2) * 1 ^ (0 - 2) :=
  bound_sum_hat (M := 2) (N := 2) (τ := 1 / 2) (K := 1) (b := 1) (by norm_num) (by norm_num)
    le_rfl zero_le_one (by norm_num) (fun _ => (1 : ℂ)) (fun _ => by simp) (by simp) 0

/-- (cal_Y_rough) at `Σ = I`, `X = [[1, 1], [1, −1]]/√2`, `z = i`, `μ = 0`. -/
example :
    (-I - Ymu (1 : Matrix (Fin 2) (Fin 2) ℝ) ((√2)⁻¹ • !![1, 1; 1, -1]) I 0).im ≤ -I.im ∧
      ‖Ymu (1 : Matrix (Fin 2) (Fin 2) ℝ) ((√2)⁻¹ • !![1, 1; 1, -1]) I 0‖ ≤
        ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * (1 + ‖I‖) / I.im :=
  calY_rough Matrix.PosDef.one _ (by simp) 0

end Checks

end Anisotropic
