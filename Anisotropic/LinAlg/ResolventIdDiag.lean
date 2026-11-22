module

public import Anisotropic.LinAlg.ResolventId

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-! ### Single-index Schur step for zero-extended minor inverses

For a matrix `A` on a finite index set `ι` and `S ⊆ ι`, a matrix `B` is a zero-extended inverse
of the principal minor `A|_{ι∖S}` if it vanishes on the rows and columns in `S` and
`(A B)_{st} = (B A)_{st} = δ_{st}` for `s, t ∉ S`. The identities below relate such inverses for
`S` and for `S ∪ {r}`, `r ∉ S`; they are the Schur-complement formulas behind Lemma 4.4. -/

section Schur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `B` is the zero extension of an inverse of the principal minor of `A` on `ι ∖ S`. -/
private structure IsMinorInv (A : Matrix ι ι ℂ) (S : Finset ι) (B : Matrix ι ι ℂ) : Prop where
  row : ∀ u ∈ S, ∀ t, B u t = 0
  col : ∀ u ∈ S, ∀ s, B s u = 0
  mul_left : ∀ s t, s ∉ S → t ∉ S → (A * B) s t = (1 : Matrix ι ι ℂ) s t
  mul_right : ∀ s t, s ∉ S → t ∉ S → (B * A) s t = (1 : Matrix ι ι ℂ) s t

variable {A B C : Matrix ι ι ℂ} {S : Finset ι} {r : ι}

/-- A product whose left factor has a zero row `u` has a zero row `u`. -/
private theorem mul_apply_eq_zero_of_row {P : Matrix ι ι ℂ} (Q : Matrix ι ι ℂ) {u : ι}
    (h : ∀ t, P u t = 0) (t : ι) : (P * Q) u t = 0 := by
  simp [mul_apply, h]

/-- A product whose right factor has a zero column `u` has a zero column `u`. -/
private theorem mul_apply_eq_zero_of_col (P : Matrix ι ι ℂ) {Q : Matrix ι ι ℂ} {u : ι}
    (h : ∀ s, Q s u = 0) (s : ι) : (P * Q) s u = 0 := by
  simp [mul_apply, h]

/-- `C_{st} = B_{st} + (C A)_{sr} B_{rt}` for `s ∉ S ∪ {r}`, `t ∉ S`. -/
private theorem IsMinorInv.key_col (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    {s t : ι} (hs : s ∉ insert r S) (ht : t ∉ S) :
    C s t = B s t + (C * A) s r * B r t := by
  have hsr : s ≠ r := fun h => hs (h ▸ Finset.mem_insert_self s S)
  have e := congrFun (congrFun (Matrix.mul_assoc C A B) s) t
  have lhs : (C * A * B) s t = B s t + (C * A) s r * B r t := by
    rw [mul_apply]
    have hv : ∀ v, (C * A) s v * B v t
        = (1 : Matrix ι ι ℂ) s v * B v t + (if v = r then (C * A) s r * B r t else 0) := by
      intro v
      by_cases hvr : v = r
      · subst hvr
        simp [one_apply, hsr]
      · by_cases hvS : v ∈ S
        · simp [hB.row v hvS, hvr]
        · rw [hC.mul_right s v hs (by simp [hvr, hvS])]
          simp [hvr]
    rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← mul_apply, Matrix.one_mul]
  have rhs : (C * (A * B)) s t = C s t := by
    rw [mul_apply]
    have hu : ∀ u, C s u * (A * B) u t = C s u * (1 : Matrix ι ι ℂ) u t := by
      intro u
      by_cases hu : u ∈ insert r S
      · simp [hC.col u hu]
      · rw [hB.mul_left u t (fun h => hu (Finset.mem_insert_of_mem h)) ht]
    rw [Finset.sum_congr rfl (fun u _ => hu u), ← mul_apply, Matrix.mul_one]
  rw [← rhs, ← e, lhs]

/-- `C_{st} = B_{st} + B_{sr} (A C)_{rt}` for `s ∉ S`, `t ∉ S ∪ {r}`. -/
private theorem IsMinorInv.key_row (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    {s t : ι} (hs : s ∉ S) (ht : t ∉ insert r S) :
    C s t = B s t + B s r * (A * C) r t := by
  have htr : t ≠ r := fun h => ht (h ▸ Finset.mem_insert_self t S)
  have e := congrFun (congrFun (Matrix.mul_assoc B A C) s) t
  have rhs : (B * (A * C)) s t = B s t + B s r * (A * C) r t := by
    rw [mul_apply]
    have hv : ∀ v, B s v * (A * C) v t
        = B s v * (1 : Matrix ι ι ℂ) v t + (if v = r then B s r * (A * C) r t else 0) := by
      intro v
      by_cases hvr : v = r
      · subst hvr
        simp [one_apply, htr.symm]
      · by_cases hvS : v ∈ S
        · simp [hB.col v hvS, hvr]
        · rw [hC.mul_left v t (by simp [hvr, hvS]) ht]
          simp [hvr]
    rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← mul_apply, Matrix.mul_one]
  have lhs : (B * A * C) s t = C s t := by
    rw [mul_apply]
    have hu : ∀ u, (B * A) s u * C u t = (1 : Matrix ι ι ℂ) s u * C u t := by
      intro u
      by_cases hu : u ∈ insert r S
      · simp [hC.row u hu]
      · rw [hB.mul_right s u hs (fun h => hu (Finset.mem_insert_of_mem h))]
    rw [Finset.sum_congr rfl (fun u _ => hu u), ← mul_apply, Matrix.one_mul]
  rw [← lhs, e, rhs]

/-- Column form: `B_{sr} = -B_{rr} (C A)_{sr}` for `s ≠ r`. -/
private theorem IsMinorInv.col_eq (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    (hr : r ∉ S) {s : ι} (hsr : s ≠ r) :
    B s r = -B r r * (C * A) s r := by
  by_cases hsS : s ∈ S
  · rw [hB.row s hsS, mul_apply_eq_zero_of_row A (hC.row s (Finset.mem_insert_of_mem hsS)),
      mul_zero]
  · have h := hB.key_col hC (s := s) (t := r) (by simp [hsr, hsS]) hr
    rw [hC.col r (Finset.mem_insert_self r S)] at h
    linear_combination -h

/-- Row form: `B_{rt} = -B_{rr} (A C)_{rt}` for `t ≠ r`. -/
private theorem IsMinorInv.row_eq (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    (hr : r ∉ S) {t : ι} (htr : t ≠ r) :
    B r t = -B r r * (A * C) r t := by
  by_cases htS : t ∈ S
  · rw [hB.col t htS, mul_apply_eq_zero_of_col A (hC.col t (Finset.mem_insert_of_mem htS)),
      mul_zero]
  · have h := hB.key_row hC (s := r) (t := t) hr (by simp [htr, htS])
    rw [hC.row r (Finset.mem_insert_self r S)] at h
    linear_combination -h

/-- (Gii) form: `B_{rr} (A_{rr} - (A C A)_{rr}) = 1`. -/
private theorem IsMinorInv.diag (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    (hr : r ∉ S) : B r r * (A r r - (A * (C * A)) r r) = 1 := by
  have hcol : ∀ v, B v r = (B r r • ((1 : Matrix ι ι ℂ) - C * A)) v r := by
    intro v
    by_cases hvr : v = r
    · subst hvr
      rw [Matrix.smul_apply, Matrix.sub_apply,
        mul_apply_eq_zero_of_row A (hC.row v (Finset.mem_insert_self v S))]
      simp
    · rw [hB.col_eq hC hr hvr, Matrix.smul_apply, Matrix.sub_apply, one_apply_ne hvr, smul_eq_mul]
      ring
  have h1 := hB.mul_left r r hr hr
  rw [one_apply_eq, mul_apply] at h1
  rw [Finset.sum_congr rfl (fun v _ => by rw [hcol v])] at h1
  rw [← mul_apply, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul] at h1
  exact h1

end Schur

/-- A sum over `𝓘` of a function vanishing on `S` is the sum over `𝓘 ∖ S`. -/
private theorem sum_eq_sum_compl (S : Finset (m ⊕ n)) (f : m ⊕ n → ℂ)
    (hf : ∀ u ∈ S, f u = 0) : ∑ u, f u = ∑ u : {u // u ∉ S}, f u := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun u => u ∉ S) f]
  have h0 : ∑ u : {u // ¬ u ∉ S}, f u = 0 :=
    Finset.sum_eq_zero fun u _ => hf u (not_not.1 u.2)
  rw [h0, add_zero]

/-! ### The minors `G^{(S)}` as zero-extended inverses of minors of `H` -/

section MinorInv
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hSig hz

/-- `G^{(S)}` is the zero extension of the inverse of `H^{(S)}`. -/
private theorem Gm_isMinorInv (S : Finset (m ⊕ n)) :
    IsMinorInv (H Sig X z) S (Gm Sig X z S) := by
  have hdet := (isUnit_iff_isUnit_det _).1 (minorH_isUnit hSig X hz S)
  have hHG := mul_nonsing_inv _ hdet
  have hGH := nonsing_inv_mul _ hdet
  refine ⟨fun u hu t => by simp [Gm, hu], fun u hu s => ?_, fun s t hs ht => ?_,
    fun s t hs ht => ?_⟩
  · unfold Gm
    split_ifs <;> rfl
  · rw [mul_apply, sum_eq_sum_compl S _ (fun u hu => by simp [Gm, hu])]
    have h := congrFun (congrFun hHG ⟨s, hs⟩) ⟨t, ht⟩
    rw [mul_apply] at h
    have e : ∀ u : {u // u ∉ S}, H Sig X z s u * Gm Sig X z S u t
        = minorH Sig X z S ⟨s, hs⟩ u * minorG Sig X z S u ⟨t, ht⟩ := by
      intro u
      simp [Gm, minorH, minorG, u.2, ht]
    simp only [e, minorG, h, one_apply, Subtype.mk.injEq]
  · rw [mul_apply, sum_eq_sum_compl S _ (fun u hu => by unfold Gm; split_ifs <;> simp)]
    have h := congrFun (congrFun hGH ⟨s, hs⟩) ⟨t, ht⟩
    rw [mul_apply] at h
    have e : ∀ u : {u // u ∉ S}, Gm Sig X z S s u * H Sig X z u t
        = minorG Sig X z S ⟨s, hs⟩ u * minorH Sig X z S u ⟨t, ht⟩ := by
      intro u
      simp [Gm, minorH, minorG, u.2, hs]
    simp only [e, minorG, h, one_apply, Subtype.mk.injEq]

end MinorInv

/-! ### Rows and columns of `H` in `𝓘_M` for diagonal `Σ` -/

/-- `(diagonal v)⁻¹ = diagonal (v⁻¹)` when every entry of `v` is nonzero. -/
private theorem inv_diagonal_of_ne_zero' {p : Type*} [Fintype p] [DecidableEq p] (v : p → ℝ)
    (hv : ∀ i, v i ≠ 0) : (diagonal v)⁻¹ = diagonal (fun i => (v i)⁻¹) := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  exact mul_inv_cancel₀ (hv i)

section Rows
variable {σ : m → ℝ} (hσ : ∀ i, σ i ≠ 0) (X : Matrix m n ℝ) (z : ℂ)
include hσ

/-- Row `i ∈ 𝓘_M` of `H(z)` for diagonal `Σ` is row `i` of `X̂` plus `-σ_i⁻¹` on the diagonal. -/
private theorem H_inl_row (i : m) (v : m ⊕ n) :
    H (diagonal σ) X z (inl i) v
      = Xhat X (inl i) v + (-1 / (σ i : ℂ)) * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) (inl i) v := by
  cases v with
  | inl j =>
    simp only [H, linH, inv_diagonal_of_ne_zero' σ hσ, Xhat, one_apply]
    by_cases hij : i = j
    · subst hij; simp [neg_div]
    · simp [hij]
  | inr ν => simp [H, linH, Xhat]

/-- Column `i ∈ 𝓘_M` of `H(z)` for diagonal `Σ` is column `i` of `X̂ᵀ` plus `-σ_i⁻¹` on the
diagonal. -/
private theorem H_inl_col (i : m) (v : m ⊕ n) :
    H (diagonal σ) X z v (inl i)
      = (Xhat X)ᵀ v (inl i) + (-1 / (σ i : ℂ)) * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) v (inl i) := by
  cases v with
  | inl j =>
    simp only [H, linH, inv_diagonal_of_ne_zero' σ hσ, Xhat, one_apply]
    by_cases hij : i = j
    · subst hij; simp [neg_div]
    · have : j ≠ i := fun h => hij h.symm
      simp [this]
  | inr ν => simp [H, linH, Xhat]

/-- `H(z)_{ii} = -σ_i⁻¹` for diagonal `Σ`. -/
private theorem H_inl_inl_self (i : m) :
    H (diagonal σ) X z (inl i) (inl i) = -1 / (σ i : ℂ) := by
  rw [H_inl_row hσ X z i (inl i)]
  simp [Xhat]

/-- `(H D)_{it} = (X̂ D)_{it} - σ_i⁻¹ D_{it}` for diagonal `Σ`. -/
private theorem H_inl_mul (D : Matrix (m ⊕ n) (m ⊕ n) ℂ) (i : m) (t : m ⊕ n) :
    (H (diagonal σ) X z * D) (inl i) t
      = (Xhat X * D) (inl i) t + (-1 / (σ i : ℂ)) * D (inl i) t := by
  have e : D (inl i) t = ((1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) * D) (inl i) t := by
    rw [Matrix.one_mul]
  rw [e, mul_apply, mul_apply, mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [H_inl_row hσ X z i v]; ring

/-- `(D H)_{si} = (D X̂ᵀ)_{si} - σ_i⁻¹ D_{si}` for diagonal `Σ`. -/
private theorem mul_H_inl (D : Matrix (m ⊕ n) (m ⊕ n) ℂ) (s : m ⊕ n) (i : m) :
    (D * H (diagonal σ) X z) s (inl i)
      = (D * (Xhat X)ᵀ) s (inl i) + (-1 / (σ i : ℂ)) * D s (inl i) := by
  have e : D s (inl i) = (D * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ)) s (inl i) := by
    rw [Matrix.mul_one]
  rw [e, mul_apply, mul_apply, mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [H_inl_col hσ X z i v]; ring

end Rows

/-- Row `i ∈ 𝓘_M` of `X̂` vanishes at `inl j`. -/
private theorem Xhat_inl_inl (X : Matrix m n ℝ) (i j : m) : Xhat X (inl i) (inl j) = 0 := by
  simp [Xhat]

/-- `X̂_{i μ} = X_{iμ}`. -/
private theorem Xhat_inl_inr (X : Matrix m n ℝ) (i : m) (μ : n) :
    Xhat X (inl i) (inr μ) = (X i μ : ℂ) := by
  simp [Xhat]

/-- Column `μ ∈ 𝓘_N` of `H(z)` is column `μ` of `X̂ - z`. -/
private theorem mul_H_inr' (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ)
    (D : Matrix (m ⊕ n) (m ⊕ n) ℂ) (s : m ⊕ n) (μ : n) :
    (D * H Sig X z) s (inr μ) = (D * Xhat X) s (inr μ) - z * D s (inr μ) := by
  have hH : ∀ v, H Sig X z v (inr μ)
      = Xhat X v (inr μ) - z * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) v (inr μ) := by
    intro v
    cases v with
    | inl i => simp [H, linH, Xhat]
    | inr ν => simp [H, linH, Xhat, one_apply]
  have e : D s (inr μ) = (D * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ)) s (inr μ) := by
    rw [Matrix.mul_one]
  rw [e, mul_apply, mul_apply, mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [hH]; ring

section L44minorDiag
variable {σ : m → ℝ} (hσ : ∀ i, 0 < σ i) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
  (S : Finset (m ⊕ n))
include hσ hz

/-- (Gaa) for `G^{(S)}`, `Σ` diagonal. -/
theorem Gaa_minor (i : m) (hi : inl i ∉ S) :
    1 / Gm (diagonal σ) X z S (inl i) (inl i) = -1 / (σ i : ℂ)
      - (Xhat X * Gm (diagonal σ) X z (insert (inl i) S) * (Xhat X)ᵀ) (inl i) (inl i) := by
  have hσ' : ∀ i, σ i ≠ 0 := fun i => (hσ i).ne'
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inl i) S)
  have h := hB.diag hC hi
  have hrow : ∀ t, Gm (diagonal σ) X z (insert (inl i) S) (inl i) t = 0 :=
    hC.row _ (Finset.mem_insert_self _ S)
  have hcol : ∀ s, Gm (diagonal σ) X z (insert (inl i) S) s (inl i) = 0 :=
    hC.col _ (Finset.mem_insert_self _ S)
  rw [H_inl_mul hσ' X z, mul_apply_eq_zero_of_row _ hrow, mul_zero, add_zero,
    ← Matrix.mul_assoc, mul_H_inl hσ' X z, mul_apply_eq_zero_of_col _ hcol, mul_zero, add_zero,
    H_inl_inl_self hσ' X z] at h
  exact (eq_one_div_of_mul_eq_one_right h).symm

/-- (Gab) for `G^{(S)}`, `Σ` diagonal. -/
theorem Gab_minor (i j : m) (hij : i ≠ j) (hi : inl i ∉ S) (hj : inl j ∉ S) :
    Gm (diagonal σ) X z S (inl i) (inl j) = -Gm (diagonal σ) X z S (inl i) (inl i)
        * (Xhat X * Gm (diagonal σ) X z (insert (inl i) S)) (inl i) (inl j) ∧
    Gm (diagonal σ) X z S (inl i) (inl j) = -Gm (diagonal σ) X z S (inl j) (inl j)
        * (Gm (diagonal σ) X z (insert (inl j) S) * (Xhat X)ᵀ) (inl i) (inl j) ∧
    Gm (diagonal σ) X z S (inl i) (inl j) = Gm (diagonal σ) X z S (inl i) (inl i)
        * Gm (diagonal σ) X z (insert (inl i) S) (inl j) (inl j)
        * (Xhat X * Gm (diagonal σ) X z (insert (inl j) (insert (inl i) S)) * (Xhat X)ᵀ)
            (inl i) (inl j) := by
  have hσ' : ∀ i, σ i ≠ 0 := fun i => (hσ i).ne'
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inl i) S)
  have hC' := Gm_isMinorInv hSig X hz (insert (inl j) S)
  have hC2 := Gm_isMinorInv hSig X hz (insert (inl j) (insert (inl i) S))
  have hne : (inl j : m ⊕ n) ≠ inl i := fun h => hij (inl_injective h).symm
  have f1 : Gm (diagonal σ) X z S (inl i) (inl j) = -Gm (diagonal σ) X z S (inl i) (inl i)
      * (Xhat X * Gm (diagonal σ) X z (insert (inl i) S)) (inl i) (inl j) := by
    rw [hB.row_eq hC hi hne, H_inl_mul hσ' X z, hC.row _ (Finset.mem_insert_self _ S), mul_zero,
      add_zero]
  refine ⟨f1, ?_, ?_⟩
  · rw [hB.col_eq hC' hj hne.symm, mul_H_inl hσ' X z, hC'.col _ (Finset.mem_insert_self _ S),
      mul_zero, add_zero]
  · have hjS : inl j ∉ insert (inl i) S := by simp [hne, hj]
    have hv : ∀ v, Xhat X (inl i) v * Gm (diagonal σ) X z (insert (inl i) S) v (inl j)
        = Xhat X (inl i) v * (-Gm (diagonal σ) X z (insert (inl i) S) (inl j) (inl j)
          * (Gm (diagonal σ) X z (insert (inl j) (insert (inl i) S)) * (Xhat X)ᵀ) v (inl j)) := by
      intro v
      by_cases hvj : v = inl j
      · subst hvj
        rw [Xhat_inl_inl, zero_mul, zero_mul]
      · rw [hC.col_eq hC2 hjS hvj, mul_H_inl hσ' X z, hC2.col _ (Finset.mem_insert_self _ _),
          mul_zero, add_zero]
    rw [f1, mul_apply (M := Xhat X), Finset.sum_congr rfl (fun v _ => hv v), Matrix.mul_assoc,
      mul_apply (M := Xhat X), Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

/-- (Gia2) for `G^{(S)}`, `Σ` diagonal. -/
theorem Gia2_minor (i : m) (μ : n) (hi : inl i ∉ S) (hμ : inr μ ∉ S) :
    Gm (diagonal σ) X z S (inl i) (inr μ) = -Gm (diagonal σ) X z S (inl i) (inl i)
        * (Xhat X * Gm (diagonal σ) X z (insert (inl i) S)) (inl i) (inr μ) ∧
    Gm (diagonal σ) X z S (inl i) (inr μ) = Gm (diagonal σ) X z S (inl i) (inl i)
        * Gm (diagonal σ) X z (insert (inl i) S) (inr μ) (inr μ)
        * (-(X i μ : ℂ) + (Xhat X * Gm (diagonal σ) X z (insert (inr μ) (insert (inl i) S))
            * Xhat X) (inl i) (inr μ)) := by
  have hσ' : ∀ i, σ i ≠ 0 := fun i => (hσ i).ne'
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inl i) S)
  have hC2 := Gm_isMinorInv hSig X hz (insert (inr μ) (insert (inl i) S))
  have f1 : Gm (diagonal σ) X z S (inl i) (inr μ) = -Gm (diagonal σ) X z S (inl i) (inl i)
      * (Xhat X * Gm (diagonal σ) X z (insert (inl i) S)) (inl i) (inr μ) := by
    rw [hB.row_eq hC hi inl_ne_inr.symm, H_inl_mul hσ' X z, hC.row _ (Finset.mem_insert_self _ S),
      mul_zero, add_zero]
  refine ⟨f1, ?_⟩
  have hμS : inr μ ∉ insert (inl i) S := by simp [hμ]
  have hzero : (Gm (diagonal σ) X z (insert (inr μ) (insert (inl i) S)) * Xhat X) (inr μ) (inr μ)
      = 0 := mul_apply_eq_zero_of_row _ (hC2.row _ (Finset.mem_insert_self _ _)) _
  have hv : ∀ v, Xhat X (inl i) v * Gm (diagonal σ) X z (insert (inl i) S) v (inr μ)
      = (if v = inr μ then (X i μ : ℂ)
          * Gm (diagonal σ) X z (insert (inl i) S) (inr μ) (inr μ) else 0)
        + (-Gm (diagonal σ) X z (insert (inl i) S) (inr μ) (inr μ))
          * (Xhat X (inl i) v
            * (Gm (diagonal σ) X z (insert (inr μ) (insert (inl i) S)) * Xhat X) v (inr μ)) := by
    intro v
    by_cases hvμ : v = inr μ
    · subst hvμ
      rw [hzero, Xhat_inl_inr]
      simp
    · rw [hC.col_eq hC2 hμS hvμ, mul_H_inr', hC2.col _ (Finset.mem_insert_self _ _)]
      simp [hvμ]
      ring
  rw [f1, mul_apply (M := Xhat X), Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum, Matrix.mul_assoc, mul_apply (M := Xhat X)]
  ring

end L44minorDiag

section L44diag
variable {σ : m → ℝ} (hσ : ∀ i, 0 < σ i) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hσ hz

/-- (Gaa), `Σ = diagonal σ`. -/
theorem Gaa (i : m) :
    1 / G (diagonal σ) X z (inl i) (inl i)
      = -1 / (σ i : ℂ) - (Xhat X * G1 (diagonal σ) X z (inl i) * (Xhat X)ᵀ) (inl i) (inl i) := by
  have h := Gaa_minor hσ X hz ∅ i (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty] at h

/-- (Gab), three forms, `Σ = diagonal σ`. -/
theorem Gab (i j : m) (hij : i ≠ j) :
    G (diagonal σ) X z (inl i) (inl j) = -G (diagonal σ) X z (inl i) (inl i)
        * (Xhat X * G1 (diagonal σ) X z (inl i)) (inl i) (inl j) ∧
    G (diagonal σ) X z (inl i) (inl j) = -G (diagonal σ) X z (inl j) (inl j)
        * (G1 (diagonal σ) X z (inl j) * (Xhat X)ᵀ) (inl i) (inl j) ∧
    G (diagonal σ) X z (inl i) (inl j) = G (diagonal σ) X z (inl i) (inl i)
        * G1 (diagonal σ) X z (inl i) (inl j) (inl j)
        * (Xhat X * G2 (diagonal σ) X z (inl i) (inl j) * (Xhat X)ᵀ) (inl i) (inl j) := by
  have h := Gab_minor hσ X hz ∅ i j hij (Finset.notMem_empty _) (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty, Finset.insert_empty, Finset.pair_comm (inl j) (inl i)]
    at h

/-- (Gia2), `Σ = diagonal σ`. -/
theorem Gia2 (i : m) (μ : n) :
    G (diagonal σ) X z (inl i) (inr μ) = -G (diagonal σ) X z (inl i) (inl i)
        * (Xhat X * G1 (diagonal σ) X z (inl i)) (inl i) (inr μ) ∧
    G (diagonal σ) X z (inl i) (inr μ) = G (diagonal σ) X z (inl i) (inl i)
        * G1 (diagonal σ) X z (inl i) (inr μ) (inr μ)
        * (-(X i μ : ℂ) + (Xhat X * G2 (diagonal σ) X z (inl i) (inr μ) * Xhat X) (inl i) (inr μ)) := by
  have h := Gia2_minor hσ X hz ∅ i μ (Finset.notMem_empty _) (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty, Finset.pair_comm (inr μ) (inl i)]
    at h

end L44diag

/-! ### Compiled checks at `Σ = diag(2,1)`, `X = I/√2` and `X = [[1,1],[0,1]]`, `z = i` -/

section Checks

open Complex

end Checks

end Anisotropic

#print axioms Anisotropic.Gaa
#print axioms Anisotropic.Gab
#print axioms Anisotropic.Gia2
#print axioms Anisotropic.Gaa_minor
#print axioms Anisotropic.Gab_minor
#print axioms Anisotropic.Gia2_minor
