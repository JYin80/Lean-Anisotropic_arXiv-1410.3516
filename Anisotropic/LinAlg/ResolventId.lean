module

public import Anisotropic.LinAlg.Minor

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
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

/-- (Gstu) form: `C_{st} = B_{st} - B_{sr} B_{rt} / B_{rr}` for `s, t ∉ S ∪ {r}`. -/
private theorem IsMinorInv.stu (hB : IsMinorInv A S B) (hC : IsMinorInv A (insert r S) C)
    (hr : r ∉ S) (hrr : B r r ≠ 0) {s t : ι} (hs : s ∉ insert r S) (ht : t ∉ insert r S) :
    C s t = B s t - B s r * B r t / B r r := by
  have hsr : s ≠ r := fun h => hs (h ▸ Finset.mem_insert_self s S)
  have htS : t ∉ S := fun h => ht (Finset.mem_insert_of_mem h)
  rw [hB.key_col hC hs htS, hB.col_eq hC hr hsr]
  field_simp
  ring

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
  rw [← mul_apply, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul] at h1
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

/-! ### Rows and columns of `H` in `𝓘_N` -/

/-- Row `μ ∈ 𝓘_N` of `H(z)` is row `μ` of `X̂ᵀ - z`. -/
private theorem H_inr_mul (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ)
    (D : Matrix (m ⊕ n) (m ⊕ n) ℂ) (μ : n) (t : m ⊕ n) :
    (H Sig X z * D) (inr μ) t = ((Xhat X)ᵀ * D) (inr μ) t - z * D (inr μ) t := by
  have hH : ∀ v, H Sig X z (inr μ) v
      = (Xhat X)ᵀ (inr μ) v - z * (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) (inr μ) v := by
    intro v
    cases v with
    | inl i => simp [H, linH, Xhat]
    | inr ν => simp [H, linH, Xhat, one_apply]
  have e : D (inr μ) t = ((1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) * D) (inr μ) t := by
    rw [Matrix.one_mul]
  rw [e, mul_apply, mul_apply, mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [hH]; ring

/-- Column `μ ∈ 𝓘_N` of `H(z)` is column `μ` of `X̂ - z`. -/
private theorem mul_H_inr (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ)
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

/-- Row `μ ∈ 𝓘_N` of `X̂ᵀ` vanishes at `inr ν`. -/
private theorem Xhat_transpose_inr_inr (X : Matrix m n ℝ) (μ ν : n) :
    (Xhat X)ᵀ (inr μ) (inr ν) = 0 := by
  simp [Xhat]

/-- `H(z)_{μμ} = -z` for `μ ∈ 𝓘_N`. -/
private theorem H_inr_inr_self (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (μ : n) :
    H Sig X z (inr μ) (inr μ) = -z := by
  simp [H, linH]

section L44minor
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
  (S : Finset (m ⊕ n))
include hSig hz

/-- (Gii) for `G^{(S)}`, any `S`. -/
theorem Gii_minor (μ : n) (hμ : inr μ ∉ S) :
    1 / Gm Sig X z S (inr μ) (inr μ)
      = -z - ((Xhat X)ᵀ * Gm Sig X z (insert (inr μ) S) * Xhat X) (inr μ) (inr μ) := by
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inr μ) S)
  have h := hB.diag hC hμ
  have hrow : ∀ t, Gm Sig X z (insert (inr μ) S) (inr μ) t = 0 :=
    hC.row _ (Finset.mem_insert_self _ S)
  have hcol : ∀ s, Gm Sig X z (insert (inr μ) S) s (inr μ) = 0 :=
    hC.col _ (Finset.mem_insert_self _ S)
  rw [H_inr_mul, mul_apply_eq_zero_of_row _ hrow, mul_zero, sub_zero, ← Matrix.mul_assoc,
    mul_H_inr, mul_apply_eq_zero_of_col _ hcol, mul_zero, sub_zero, H_inr_inr_self] at h
  exact (eq_one_div_of_mul_eq_one_right h).symm

/-- (Gij) for `G^{(S)}`, any `S`. -/
theorem Gij_minor (μ ν : n) (hμν : μ ≠ ν) (hμ : inr μ ∉ S) (hν : inr ν ∉ S) :
    Gm Sig X z S (inr μ) (inr ν) = -Gm Sig X z S (inr μ) (inr μ)
        * ((Xhat X)ᵀ * Gm Sig X z (insert (inr μ) S)) (inr μ) (inr ν) ∧
    Gm Sig X z S (inr μ) (inr ν) = -Gm Sig X z S (inr ν) (inr ν)
        * (Gm Sig X z (insert (inr ν) S) * Xhat X) (inr μ) (inr ν) ∧
    Gm Sig X z S (inr μ) (inr ν) = Gm Sig X z S (inr μ) (inr μ)
        * Gm Sig X z (insert (inr μ) S) (inr ν) (inr ν)
        * ((Xhat X)ᵀ * Gm Sig X z (insert (inr ν) (insert (inr μ) S)) * Xhat X) (inr μ) (inr ν) := by
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inr μ) S)
  have hC' := Gm_isMinorInv hSig X hz (insert (inr ν) S)
  have hC2 := Gm_isMinorInv hSig X hz (insert (inr ν) (insert (inr μ) S))
  have hne : (inr ν : m ⊕ n) ≠ inr μ := fun h => hμν (inr_injective h).symm
  have f1 : Gm Sig X z S (inr μ) (inr ν) = -Gm Sig X z S (inr μ) (inr μ)
      * ((Xhat X)ᵀ * Gm Sig X z (insert (inr μ) S)) (inr μ) (inr ν) := by
    rw [hB.row_eq hC hμ hne, H_inr_mul, hC.row _ (Finset.mem_insert_self _ S), mul_zero, sub_zero]
  refine ⟨f1, ?_, ?_⟩
  · rw [hB.col_eq hC' hν hne.symm, mul_H_inr, hC'.col _ (Finset.mem_insert_self _ S), mul_zero,
      sub_zero]
  · have hνS : inr ν ∉ insert (inr μ) S := by simp [hne, hν]
    have hv : ∀ v, (Xhat X)ᵀ (inr μ) v * Gm Sig X z (insert (inr μ) S) v (inr ν)
        = (Xhat X)ᵀ (inr μ) v * (-Gm Sig X z (insert (inr μ) S) (inr ν) (inr ν)
          * (Gm Sig X z (insert (inr ν) (insert (inr μ) S)) * Xhat X) v (inr ν)) := by
      intro v
      by_cases hvν : v = inr ν
      · subst hvν
        rw [Xhat_transpose_inr_inr, zero_mul, zero_mul]
      · rw [hC.col_eq hC2 hνS hvν, mul_H_inr, hC2.col _ (Finset.mem_insert_self _ _), mul_zero,
          sub_zero]
    rw [f1, mul_apply (M := (Xhat X)ᵀ), Finset.sum_congr rfl (fun v _ => hv v), Matrix.mul_assoc,
      mul_apply (M := (Xhat X)ᵀ), Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

/-- (Gia) for `G^{(S)}`, any `S`. -/
theorem Gia_minor (i : m) (μ : n) (hi : inl i ∉ S) (hμ : inr μ ∉ S) :
    Gm Sig X z S (inl i) (inr μ) = -Gm Sig X z S (inr μ) (inr μ)
        * (Gm Sig X z (insert (inr μ) S) * Xhat X) (inl i) (inr μ) ∧
    Gm Sig X z S (inr μ) (inl i) = -Gm Sig X z S (inr μ) (inr μ)
        * ((Xhat X)ᵀ * Gm Sig X z (insert (inr μ) S)) (inr μ) (inl i) := by
  have hB := Gm_isMinorInv hSig X hz S
  have hC := Gm_isMinorInv hSig X hz (insert (inr μ) S)
  refine ⟨?_, ?_⟩
  · rw [hB.col_eq hC hμ inl_ne_inr, mul_H_inr, hC.col _ (Finset.mem_insert_self _ S), mul_zero,
      sub_zero]
  · rw [hB.row_eq hC hμ inl_ne_inr, H_inr_mul, hC.row _ (Finset.mem_insert_self _ S), mul_zero,
      sub_zero]

/-- (Gstu) for `G^{(S)}`, any `S`. -/
theorem Gstu_minor (r s t : m ⊕ n) (hr : r ∉ S) (hs : s ∉ insert r S) (ht : t ∉ insert r S) :
    Gm Sig X z (insert r S) s t
      = Gm Sig X z S s t - Gm Sig X z S s r * Gm Sig X z S r t / Gm Sig X z S r r :=
  (Gm_isMinorInv hSig X hz S).stu (Gm_isMinorInv hSig X hz (insert r S)) hr
    (Gm_diag_ne_zero hSig X hz S r hr) hs ht

end L44minor

section L44
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hSig hz

/-- (Gii). -/
theorem Gii (μ : n) :
    1 / G Sig X z (inr μ) (inr μ)
      = -z - ((Xhat X)ᵀ * G1 Sig X z (inr μ) * Xhat X) (inr μ) (inr μ) := by
  have h := Gii_minor hSig X hz ∅ μ (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty] at h

/-- (Gij), three forms. -/
theorem Gij (μ ν : n) (hμν : μ ≠ ν) :
    G Sig X z (inr μ) (inr ν)
        = -G Sig X z (inr μ) (inr μ) * ((Xhat X)ᵀ * G1 Sig X z (inr μ)) (inr μ) (inr ν) ∧
    G Sig X z (inr μ) (inr ν)
        = -G Sig X z (inr ν) (inr ν) * (G1 Sig X z (inr ν) * Xhat X) (inr μ) (inr ν) ∧
    G Sig X z (inr μ) (inr ν)
        = G Sig X z (inr μ) (inr μ) * G1 Sig X z (inr μ) (inr ν) (inr ν)
          * ((Xhat X)ᵀ * G2 Sig X z (inr μ) (inr ν) * Xhat X) (inr μ) (inr ν) := by
  have h := Gij_minor hSig X hz ∅ μ ν hμν (Finset.notMem_empty _) (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty, Finset.insert_empty, Finset.pair_comm (inr ν) (inr μ)]
    at h

/-- (Gia), both identities. -/
theorem Gia (i : m) (μ : n) :
    G Sig X z (inl i) (inr μ)
        = -G Sig X z (inr μ) (inr μ) * (G1 Sig X z (inr μ) * Xhat X) (inl i) (inr μ) ∧
    G Sig X z (inr μ) (inl i)
        = -G Sig X z (inr μ) (inr μ) * ((Xhat X)ᵀ * G1 Sig X z (inr μ)) (inr μ) (inl i) := by
  have h := Gia_minor hSig X hz ∅ i μ (Finset.notMem_empty _) (Finset.notMem_empty _)
  rwa [Gm_empty, Finset.insert_empty] at h

/-- (Gstu), with `s, t ∈ 𝓘 ∖ {r}`. -/
theorem Gstu (r s t : m ⊕ n) (hs : s ≠ r) (ht : t ≠ r) :
    G1 Sig X z r s t = G Sig X z s t - G Sig X z s r * G Sig X z r t / G Sig X z r r := by
  have h := Gstu_minor hSig X hz ∅ r s t (Finset.notMem_empty _) (by simp [hs]) (by simp [ht])
  rwa [Gm_empty, Finset.insert_empty] at h

end L44

/-! ### Compiled checks at the instance `Σ = diag(2,1)`, `X = I/√2` or `X = [[1,1],[0,1]]`,
`z = i` -/

section Checks

open Complex

end Checks

end Anisotropic

#print axioms Anisotropic.Gii
#print axioms Anisotropic.Gij
#print axioms Anisotropic.Gia
#print axioms Anisotropic.Gstu
#print axioms Anisotropic.Gii_minor
#print axioms Anisotropic.Gij_minor
#print axioms Anisotropic.Gia_minor
#print axioms Anisotropic.Gstu_minor
