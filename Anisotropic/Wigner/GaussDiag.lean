module

public import Anisotropic.Framework.Domination
public import Anisotropic.Gaussian.Lemma62
public import Anisotropic.Gaussian.Parity
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.GOE
public import Anisotropic.Wigner.Model

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The Gaussian step: entrywise ⇒ anisotropic law for the GOE plus a diagonal matrix -/

/-! ## Linear algebra: `Π^W` for diagonal `A`, the resolvent bound, sign flips -/

/-- `Im m^W ≥ 0` (the solution has `Im m^W > 0`; the junk value is `0`). -/
private theorem gaussDiag_im_mW_nonneg {N : ℕ} (a : Fin N → ℝ) (z : ℂ) : 0 ≤ (mW a z).im := by
  unfold mW
  split_ifs with h
  · exact h.choose_spec.1.le
  · simp

/-- The inverse of a diagonal matrix with nonzero entries. -/
private theorem gaussDiag_inv_diagonal {N : ℕ} (d : Fin N → ℂ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd i)
  rw [this, diagonal_one]

/-- `cplx(diag(a)) − c = diag(aᵢ − c)`. -/
private theorem gaussDiag_cplx_diagonal_sub {N : ℕ} (a : Fin N → ℝ) (c : ℂ) :
    cplx (diagonal a) - c • (1 : Matrix (Fin N) (Fin N) ℂ) = diagonal fun i => (a i : ℂ) - c := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cplx]
  · simp [cplx, h]

/-- For `A = diag(a)`, `Π^W(z) = diag((aᵢ − m^W − z)⁻¹)` (`Im z > 0`). -/
private theorem gaussDiag_piW_eq {N : ℕ} (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    piW (diagonal a) z =
      diagonal fun i => ((a i : ℂ) - (mW (specOf (diagonal a)) z + z))⁻¹ := by
  unfold piW
  rw [gaussDiag_cplx_diagonal_sub]
  refine gaussDiag_inv_diagonal _ fun i h0 => ?_
  have h := congrArg Complex.im h0
  have hm := gaussDiag_im_mW_nonneg (specOf (diagonal a)) z
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.zero_im] at h
  linarith

/-- `Π^W` of a diagonal `A` vanishes off the diagonal. -/
private theorem gaussDiag_piW_offdiag {N : ℕ} (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im)
    {s t : Fin N} (hst : s ≠ t) : piW (diagonal a) z s t = 0 := by
  rw [gaussDiag_piW_eq a hz]
  exact diagonal_apply_ne _ hst

/-- The real orthogonal matrix of eigenvectors of a symmetric `H`, with `U Uᵀ = 1`, `Uᵀ U = 1`
and `H = U diag(λ) Uᵀ`. -/
private theorem gaussDiag_eig {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      H = U * diagonal hH.eigenvalues * Uᵀ := by
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- For `H = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ ≠ w`, `(H − w)⁻¹` is the rotated
diagonal `(λₖ − w)⁻¹`. -/
private theorem gaussDiag_resolvent_eq {N : ℕ} {H U : Matrix (Fin N) (Fin N) ℝ}
    {l : Fin N → ℝ} {w : ℂ} (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1)
    (hHU : H = U * diagonal l * Uᵀ) (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    rw [← cplx_transpose, ← cplx_mul, hUU, cplx_one]
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    rw [← cplx_transpose, ← cplx_mul, hUU', cplx_one]
  have hM : cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx H = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hHU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - w) =
        diagonal (fun k => (l k : ℂ)) - w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  refine Matrix.inv_eq_right_inv ?_
  rw [hM]
  calc cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ *
        (cplx U * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ)
      = cplx U * diagonal (fun k => (l k : ℂ) - w) * ((cplx U)ᵀ * cplx U) *
        diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
        have : (fun k => ((l k : ℂ) - w) * ((l k : ℂ) - w)⁻¹) = fun _ => 1 := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]

/-- The resolvent bound `|G^W_{st}| ≤ η⁻¹` for symmetric `W` and diagonal `A`. -/
private theorem gaussDiag_norm_GW_le {N : ℕ} (a : Fin N → ℝ) {Wm : Matrix (Fin N) (Fin N) ℝ}
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (s t : Fin N) :
    ‖GW (diagonal a) Wm z s t‖ ≤ z.im⁻¹ := by
  have hH : (Wm + diagonal a).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, hW,
      diagonal_transpose]
  obtain ⟨U, hUU, hUU', hHU⟩ := gaussDiag_eig hH
  set l := hH.eigenvalues
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h0 => by
    have h := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at h
    linarith
  have hG : GW (diagonal a) Wm z = (cplx U) * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    gaussDiag_resolvent_eq hUU hUU' hHU hne
  have hent : GW (diagonal a) Wm z s t = ∑ k, (U s k : ℂ) * ((l k : ℂ) - z)⁻¹ * (U t k : ℂ) := by
    rw [hG, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply]
    simp [cplx]
  have hd : ∀ k, ‖((l k : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
    intro k
    rw [norm_inv]
    refine inv_anti₀ hz (le_trans ?_ (Complex.abs_im_le_norm _))
    simpa using le_abs_self z.im
  have hrow : ∀ r, ∑ k, U r k ^ 2 = 1 := by
    intro r
    have h := congrFun (congrFun hUU r) r
    simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq] at h
    simpa [sq] using h
  have hCS : ∑ k, |U s k| * |U t k| ≤ 1 := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |U s k|) (fun k => |U t k|)
    simp only [sq_abs, hrow, Real.sqrt_one, mul_one] at h
    exact h
  rw [hent]
  calc ‖∑ k, (U s k : ℂ) * ((l k : ℂ) - z)⁻¹ * (U t k : ℂ)‖
      ≤ ∑ k, ‖(U s k : ℂ) * ((l k : ℂ) - z)⁻¹ * (U t k : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k, z.im⁻¹ * (|U s k| * |U t k|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have := hd k
        have h0 : 0 ≤ |U s k| := abs_nonneg _
        have h1 : 0 ≤ |U t k| := abs_nonneg _
        nlinarith [mul_nonneg h0 h1]
    _ = z.im⁻¹ * ∑ k, |U s k| * |U t k| := by rw [Finset.mul_sum]
    _ ≤ z.im⁻¹ * 1 := mul_le_mul_of_nonneg_left hCS (inv_pos.2 hz).le
    _ = z.im⁻¹ := mul_one _

/-- A sign flip `R = diag(r)`, `rᵢ² = 1`, fixes `diag(a)` and maps `G^W_{st}` to
`r_s r_t G^W_{st}`. -/
private theorem gaussDiag_GW_flip {N : ℕ} (a r : Fin N → ℝ) (hr : ∀ i, r i * r i = 1)
    (Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s t : Fin N) :
    GW (diagonal a) (diagonal r * Wm * (diagonal r)ᵀ) z s t =
      (r s : ℂ) * (r t : ℂ) * GW (diagonal a) Wm z s t := by
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal fun i => (r i : ℂ) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact_mod_cast hr i
  have hM : cplx (diagonal r * Wm * (diagonal r)ᵀ + diagonal a) -
      z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      D * (cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * D := by
    ext i j
    simp only [hD, diagonal_transpose, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      cplx, Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.one_apply,
      diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      have hi : ((r i : ℂ)) * (r i : ℂ) = 1 := by exact_mod_cast hr i
      simp only [ite_true, Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_mul]
      linear_combination (z - (a i : ℂ)) * hi
    · simp only [h, ite_false, Complex.coe_algebraMap, Complex.ofReal_mul, add_zero, mul_zero,
        sub_zero]
  have hDi : D⁻¹ = D := Matrix.inv_eq_left_inv hDD
  have hG : GW (diagonal a) (diagonal r * Wm * (diagonal r)ᵀ) z =
      D * GW (diagonal a) Wm z * D := by
    unfold GW
    rw [show diagonal r * Wm * (diagonal r)ᵀ + diagonal a =
      diagonal r * Wm * (diagonal r)ᵀ + diagonal a from rfl, hM, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hDi, Matrix.mul_assoc]
  rw [hG, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- Every entry of `G^W` is a measurable function of the matrix `W`. -/
private theorem gaussDiag_measurable_GW {N : ℕ} (a : Fin N → ℝ) (z : ℂ) (s t : Fin N) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW (diagonal a) Wm z s t := by
  have hc : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    unfold cplx
    exact ((continuous_id.add continuous_const).matrix_map Complex.continuous_ofReal).sub
      continuous_const
  have hdet : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    hc.matrix_det.measurable
  have hadj : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t :=
    (Matrix.measurable_iff.1 hc.matrix_adjugate.measurable) s t
  have h : (fun Wm : Matrix (Fin N) (Fin N) ℝ => GW (diagonal a) Wm z s t) = fun Wm =>
      (cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        (cplx (Wm + diagonal a) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t := by
    funext Wm
    unfold GW
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

/-! ## The expansion of `|𝒵|^p` over labelings -/

/-- The summand `v_s A_{st} w_t` of `𝒵` at `x = (s, t)`, and `0` for `s = t`. -/
private def gaussDiag_ent {ι : Type*} [DecidableEq ι] (v w : ι → ℝ) (B : Matrix ι ι ℂ)
    (x : ι × ι) : ℂ :=
  if x.1 = x.2 then 0 else (v x.1 : ℂ) * B x.1 x.2 * w x.2

/-- The `r`-th factor of `𝒵^q 𝒵̄^q`: the summand of `𝒵` for `r < q`, its conjugate otherwise. -/
private def gaussDiag_fac {ι : Type*} [DecidableEq ι] (q : ℕ) (v w : ι → ℝ) (B : Matrix ι ι ℂ)
    (r : Fin (q + q)) (x : ι × ι) : ℂ :=
  if (r : ℕ) < q then gaussDiag_ent v w B x else (starRingEnd ℂ) (gaussDiag_ent v w B x)

/-- The term of a labeling `ℓ` of `2n` slots: the slots `(0, r)` and `(1, r)` carry the index
pair of the `r`-th factor. -/
private def gaussDiag_term {ι : Type*} {n : ℕ} (f : Fin n → ι × ι → ℂ) (ℓ : Fin (2 * n) → ι) : ℂ :=
  ∏ r, f r (ℓ (finProdFinEquiv (0, r)), ℓ (finProdFinEquiv (1, r)))

/-- A product over the `2n` slots, grouped by the pairs `(0, r)`, `(1, r)`. -/
private theorem gaussDiag_prod_slots {R : Type*} [CommMonoid R] {n : ℕ} (h : Fin (2 * n) → R) :
    ∏ a, h a = ∏ r : Fin n, h (finProdFinEquiv (0, r)) * h (finProdFinEquiv (1, r)) := by
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type_right]
  simp [Fin.prod_univ_two]

/-- Labelings of `2n` slots are the `n`-tuples of index pairs. -/
private def gaussDiag_slotEquiv (ι : Type*) (n : ℕ) : (Fin (2 * n) → ι) ≃ (Fin n → ι × ι) where
  toFun ℓ r := (ℓ (finProdFinEquiv (0, r)), ℓ (finProdFinEquiv (1, r)))
  invFun g a := if (finProdFinEquiv.symm a).1 = 0 then (g (finProdFinEquiv.symm a).2).1
    else (g (finProdFinEquiv.symm a).2).2
  left_inv ℓ := by
    funext a
    obtain ⟨⟨j, r⟩, rfl⟩ := finProdFinEquiv.surjective a
    fin_cases j <;> simp
  right_inv g := by
    funext r
    simp

/-- `Π_r Σ_x f_r(x) = Σ_ℓ Π_r f_r(ℓ_{(0,r)}, ℓ_{(1,r)})`. -/
private theorem gaussDiag_prod_sum {ι : Type*} [Fintype ι] {n : ℕ} (f : Fin n → ι × ι → ℂ) :
    ∏ r, ∑ x, f r x = ∑ ℓ : Fin (2 * n) → ι, gaussDiag_term f ℓ := by
  rw [Fintype.prod_sum]
  exact (Fintype.sum_equiv (gaussDiag_slotEquiv ι n) _ _ fun ℓ => rfl).symm

/-- `𝒵 = Σ_{(s,t)} v_s A_{st} w_t 1(s ≠ t)`. -/
private theorem gaussDiag_offPart_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (v w : ι → ℝ)
    (B : Matrix ι ι ℂ) : offPart v B w = ∑ x, gaussDiag_ent v w B x := by
  rw [offPart, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  simp only [gaussDiag_ent, ↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp [(Finset.ne_of_mem_erase ht).symm]

/-- `|𝒵|^{2q} = Σ_ℓ T_ℓ` over labelings `ℓ` of `4q` slots. -/
private theorem gaussDiag_norm_pow_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (v w : ι → ℝ) (B : Matrix ι ι ℂ) :
    ((‖offPart v B w‖ ^ (q + q) : ℝ) : ℂ) =
      ∑ ℓ : Fin (2 * (q + q)) → ι, gaussDiag_term (gaussDiag_fac q v w B) ℓ := by
  rw [← gaussDiag_prod_sum, Fin.prod_univ_add]
  have h1 : ∀ i : Fin q, ∑ x, gaussDiag_fac q v w B (Fin.castAdd q i) x = offPart v B w := by
    intro i
    rw [gaussDiag_offPart_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [gaussDiag_fac, i.isLt]
  have h2 : ∀ i : Fin q, ∑ x, gaussDiag_fac q v w B (Fin.natAdd q i) x =
      (starRingEnd ℂ) (offPart v B w) := by
    intro i
    rw [gaussDiag_offPart_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [gaussDiag_fac]
  simp only [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- `|T_ℓ| ≤ Π_a c_a(ℓ_a) L^n` when every factor is bounded by `α_s β_t L`. -/
private theorem gaussDiag_norm_term_le {ι : Type*} {n : ℕ} (f : Fin n → ι × ι → ℂ)
    (α β : ι → ℝ) (L : ℝ) (hf : ∀ r x, ‖f r x‖ ≤ α x.1 * β x.2 * L) (ℓ : Fin (2 * n) → ι) :
    ‖gaussDiag_term f ℓ‖ ≤
      (∏ a, (if (finProdFinEquiv.symm a).1 = 0 then α else β) (ℓ a)) * L ^ n := by
  rw [gaussDiag_prod_slots, gaussDiag_term, norm_prod]
  simp only [Equiv.symm_apply_apply, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
  calc ∏ r, ‖f r (ℓ (finProdFinEquiv (0, r)), ℓ (finProdFinEquiv (1, r)))‖
      ≤ ∏ r, (α (ℓ (finProdFinEquiv (0, r))) * β (ℓ (finProdFinEquiv (1, r))) * L) :=
        Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) fun r _ => hf r _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `T_ℓ` for the factors `g_r(x) = ε_s ε_t f_r(x)` is `Π_a ε_{ℓ_a}` times `T_ℓ` for `f`. -/
private theorem gaussDiag_term_sign {ι : Type*} {n : ℕ} (f g : Fin n → ι × ι → ℂ) (ε : ι → ℝ)
    (h : ∀ r x, g r x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * f r x) (ℓ : Fin (2 * n) → ι) :
    gaussDiag_term g ℓ = ((∏ a, ε (ℓ a) : ℝ) : ℂ) * gaussDiag_term f ℓ := by
  rw [gaussDiag_prod_slots (fun a => ε (ℓ a)), gaussDiag_term, gaussDiag_term]
  simp only [h, Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_mul_distrib]

/-- The factors of `B'` with `B'_{st} = ε_s ε_t B_{st}` are `ε_s ε_t` times those of `B`. -/
private theorem gaussDiag_fac_sign {ι : Type*} [DecidableEq ι] (q : ℕ) (v w ε : ι → ℝ)
    (B B' : Matrix ι ι ℂ) (hB : ∀ s t, B' s t = (ε s : ℂ) * (ε t : ℂ) * B s t)
    (r : Fin (q + q)) (x : ι × ι) :
    gaussDiag_fac q v w B' r x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * gaussDiag_fac q v w B r x := by
  have he : gaussDiag_ent v w B' x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * gaussDiag_ent v w B x := by
    unfold gaussDiag_ent
    split_ifs
    · simp
    · rw [hB]
      push_cast
      ring
  unfold gaussDiag_fac
  split_ifs
  · exact he
  · rw [he, map_mul, Complex.conj_ofReal]

/-- `|v_s B_{st} w_t| ≤ |v_s| |w_t| L` when `|B_{st}| ≤ L` for `s ≠ t`. -/
private theorem gaussDiag_fac_norm_le {ι : Type*} [DecidableEq ι] (q : ℕ) (v w : ι → ℝ)
    (B : Matrix ι ι ℂ) (L : ℝ) (hL : 0 ≤ L) (hB : ∀ s t, s ≠ t → ‖B s t‖ ≤ L)
    (r : Fin (q + q)) (x : ι × ι) :
    ‖gaussDiag_fac q v w B r x‖ ≤ |v x.1| * |w x.2| * L := by
  have he : ‖gaussDiag_ent v w B x‖ ≤ |v x.1| * |w x.2| * L := by
    unfold gaussDiag_ent
    split_ifs with h
    · simp only [norm_zero]
      positivity
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      calc |v x.1| * ‖B x.1 x.2‖ * |w x.2| = |v x.1| * |w x.2| * ‖B x.1 x.2‖ := by ring
        _ ≤ |v x.1| * |w x.2| * L := mul_le_mul_of_nonneg_left (hB _ _ h) (by positivity)
  unfold gaussDiag_fac
  split_ifs
  · exact he
  · rwa [Complex.norm_conj]

/-- `Π_a ε_{ℓ_a} = (−1)^{n_u(ℓ)}` for the sign flip at `u`. -/
private theorem gaussDiag_prod_sign {ι : Type*} [DecidableEq ι] {m : ℕ} (ℓ : Fin m → ι) (u : ι) :
    ∏ a, (if ℓ a = u then (-1 : ℝ) else 1) =
      (-1) ^ (Finset.univ.filter fun a => ℓ a = u).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]


/-! ## The parity argument for the GOE -/

/-- `B = G^W − Π^W` for `A = diag(a)`. -/
private def gaussDiag_B {N : ℕ} (a : Fin N → ℝ) (Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  GW (diagonal a) Wm z - piW (diagonal a) z

/-- Under `W ↦ R W R`, `R = diag(r)`, `rᵢ² = 1`, the entry `B_{st}` becomes `r_s r_t B_{st}`. -/
private theorem gaussDiag_B_flip {N : ℕ} (a r : Fin N → ℝ) (hr : ∀ i, r i * r i = 1)
    (Wm : Matrix (Fin N) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (s t : Fin N) :
    gaussDiag_B a (diagonal r * Wm * (diagonal r)ᵀ) z s t =
      (r s : ℂ) * (r t : ℂ) * gaussDiag_B a Wm z s t := by
  unfold gaussDiag_B
  rw [Matrix.sub_apply, Matrix.sub_apply, gaussDiag_GW_flip a r hr Wm z s t]
  by_cases hst : s = t
  · subst hst
    have hi : (r s : ℂ) * (r s : ℂ) = 1 := by exact_mod_cast hr s
    linear_combination (piW (diagonal a) z s s) * hi
  · rw [gaussDiag_piW_offdiag a hz hst]
    ring

/-- Every entry of `B` is a measurable function of the matrix `W`. -/
private theorem gaussDiag_measurable_B {N : ℕ} (a : Fin N → ℝ) (z : ℂ) (s t : Fin N) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => gaussDiag_B a Wm z s t := by
  unfold gaussDiag_B
  simp only [Matrix.sub_apply]
  exact (gaussDiag_measurable_GW a z s t).sub_const _

/-- Each factor is a measurable function of the matrix `W`. -/
private theorem gaussDiag_measurable_fac {N : ℕ} (a : Fin N → ℝ) (z : ℂ) (q : ℕ)
    (v w : Fin N → ℝ) (r : Fin (q + q)) (x : Fin N × Fin N) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      gaussDiag_fac q v w (gaussDiag_B a Wm z) r x := by
  have he : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      gaussDiag_ent v w (gaussDiag_B a Wm z) x := by
    unfold gaussDiag_ent
    by_cases h : x.1 = x.2
    · simp only [h, ↓reduceIte]
      exact measurable_const
    · simp only [h, ↓reduceIte]
      exact ((gaussDiag_measurable_B a z _ _).const_mul _).mul_const _
  unfold gaussDiag_fac
  by_cases hr : (r : ℕ) < q
  · simp only [hr, ↓reduceIte]
    exact he
  · simp only [hr, ↓reduceIte]
    exact Complex.continuous_conj.measurable.comp he

section Moments

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The parity bound `E|𝒵|^p ≤ (2p − 1)!! E L^p` for the GOE, `A = diag(a)`, even `p`, unit
`v`, `w`, and any `L ≥ |B_{st}|` (`s ≠ t`): the sign flip `W ↦ R W R` at one index preserves the
GOE law and fixes `diag(a)`, so only even labelings contribute. -/
private theorem gaussDiag_moment {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W)
    (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) {v w : Fin N → ℝ} (hv : testNorm v = 1)
    (hw : testNorm w = 1) {p : ℕ} (hp : Even p) (L : Ω → ℝ) (hL0 : ∀ ω, 0 ≤ L ω)
    (hL : ∀ ω s t, s ≠ t → ‖gaussDiag_B a (W ω) z s t‖ ≤ L ω)
    (hint : Integrable fun ω => L ω ^ p) :
    Integrable (fun ω => ‖offPart v (gaussDiag_B a (W ω) z) w‖ ^ p) ∧
      ∫ ω, ‖offPart v (gaussDiag_B a (W ω) z) w‖ ^ p ≤
        ((2 * p - 1).doubleFactorial : ℝ) * ∫ ω, L ω ^ p := by
  obtain ⟨q, rfl⟩ := hp
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  let c : Fin (2 * (q + q)) → Fin N → ℝ := fun a =>
    if (finProdFinEquiv.symm a).1 = 0 then fun u => |v u| else fun u => |w u|
  have hv2 : ∑ u, v u ^ 2 = 1 := by rwa [testNorm, Real.sqrt_eq_one] at hv
  have hw2 : ∑ u, w u ^ 2 = 1 := by rwa [testNorm, Real.sqrt_eq_one] at hw
  have hc : ∀ a u, 0 ≤ c a u := by
    intro a u
    simp only [c]
    split_ifs <;> exact abs_nonneg _
  have hc1 : ∀ a, ∑ u, c a u ^ 2 ≤ 1 := by
    intro a
    simp only [c]
    split_ifs <;> simp [sq_abs, hv2, hw2]
  let g : (Fin (2 * (q + q)) → Fin N) → Matrix (Fin N) (Fin N) ℝ → ℝ :=
    fun ℓ A => (gaussDiag_term (gaussDiag_fac q v w (gaussDiag_B a A z)) ℓ).re
  have hgm : ∀ ℓ, Measurable (g ℓ) := fun ℓ =>
    Complex.measurable_re.comp (Finset.measurable_prod _ fun r _ =>
      gaussDiag_measurable_fac a z q v w r _)
  have hgb : ∀ ℓ ω, ‖g ℓ (W ω)‖ ≤ (∏ a, c a (ℓ a)) * L ω ^ (q + q) := by
    intro ℓ ω
    refine le_trans (by simpa [g] using Complex.abs_re_le_norm _) (gaussDiag_norm_term_le _
      (fun u => |v u|) (fun u => |w u|) _
      (fun r x => gaussDiag_fac_norm_le q v w _ _ (hL0 ω)
        (fun s t hst => hL ω s t hst) r x) ℓ)
  have hgi : ∀ ℓ, Integrable fun ω => g ℓ (W ω) := fun ℓ =>
    Integrable.mono' (hint.const_mul _) ((hgm ℓ).comp hWm).aestronglyMeasurable
      (ae_of_all _ fun ω => hgb ℓ ω)
  have hexp : ∀ A : Matrix (Fin N) (Fin N) ℝ,
      ‖offPart v (gaussDiag_B a A z) w‖ ^ (q + q) = ∑ ℓ, g ℓ A := by
    intro A
    have h := congrArg Complex.re (gaussDiag_norm_pow_eq q v w (gaussDiag_B a A z))
    rwa [Complex.ofReal_re, Complex.re_sum] at h
  have hzero : ∀ ℓ, ¬EvenLabel ℓ → ∫ ω, g ℓ (W ω) = 0 := by
    intro ℓ hℓ
    unfold EvenLabel at hℓ
    simp only [not_forall] at hℓ
    obtain ⟨u, hu⟩ := hℓ
    set r : Fin N → ℝ := fun i => if i ∈ ({u} : Finset (Fin N)) then -1 else 1 with hr_def
    have hr : ∀ i, r i * r i = 1 := by
      intro i
      simp only [hr_def]
      split_ifs <;> norm_num
    have hR : signMat ({u} : Finset (Fin N)) = diagonal r := rfl
    have hflip : ∀ A, g ℓ (signMat {u} * A * (signMat {u})ᵀ) = -g ℓ A := by
      intro A
      rw [hR]
      have hs := gaussDiag_term_sign _ _ r
        (gaussDiag_fac_sign q v w r _ _ (gaussDiag_B_flip a r hr A hz)) ℓ
      have hp : ∏ a, r (ℓ a) = -1 := by
        have e : ∀ a, r (ℓ a) = if ℓ a = u then -1 else 1 := by
          intro a
          simp [hr_def, Finset.mem_singleton]
        simp only [e]
        rw [gaussDiag_prod_sign]
        exact (Nat.not_even_iff_odd.1 hu).neg_one_pow
      simp only [g]
      rw [hs, hp]
      simp
    have hcm : Measurable fun A : Matrix (Fin N) (Fin N) ℝ =>
        signMat ({u} : Finset (Fin N)) * A * (signMat {u})ᵀ :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
    have h1 : ∫ ω, g ℓ (signMat {u} * W ω * (signMat {u})ᵀ) = ∫ ω, g ℓ (W ω) := by
      have hcm' : Measurable fun ω => signMat ({u} : Finset (Fin N)) * W ω * (signMat {u})ᵀ :=
        hcm.comp hWm
      have e1 := integral_map (μ := (ℙ : Measure Ω)) hcm'.aemeasurable (hgm ℓ).aestronglyMeasurable
      have e2 := integral_map (μ := (ℙ : Measure Ω)) hWm.aemeasurable (hgm ℓ).aestronglyMeasurable
      rw [← e1, hW.map_conj (signMat_mem _), e2]
    simp only [hflip, integral_neg] at h1
    linarith
  have hle : ∀ ℓ, ∫ ω, g ℓ (W ω) ≤ (∏ a, c a (ℓ a)) * ∫ ω, L ω ^ (q + q) := by
    intro ℓ
    rw [← integral_const_mul]
    exact integral_mono (hgi ℓ) (hint.const_mul _) fun ω =>
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hgb ℓ ω)
  have hI : 0 ≤ ∫ ω, L ω ^ (q + q) := integral_nonneg fun ω => pow_nonneg (hL0 ω) _
  have hsum : (fun ω => ‖offPart v (gaussDiag_B a (W ω) z) w‖ ^ (q + q)) =
      fun ω => ∑ ℓ, g ℓ (W ω) := funext fun ω => hexp (W ω)
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun ℓ _ => hgi ℓ
  · rw [hsum, integral_finsetSum _ fun ℓ _ => hgi ℓ]
    calc ∑ ℓ, ∫ ω, g ℓ (W ω)
        ≤ ∑ ℓ, if EvenLabel ℓ then (∏ a, c a (ℓ a)) * ∫ ω, L ω ^ (q + q) else 0 := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          split_ifs with h
          · exact hle ℓ
          · exact (hzero ℓ h).le
      _ = (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * (q + q)) → Fin N => EvenLabel ℓ),
            ∏ a, c a (ℓ a)) * ∫ ω, L ω ^ (q + q) := by
          rw [Finset.sum_filter, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          split_ifs <;> simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_evenLabel_le (q + q) c hc hc1) hI

end Moments


/-! ## Test vectors and exponents -/

/-- `|v| = 1` gives `Σ_s v_s² = 1`. -/
private theorem gaussDiag_sum_sq {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : testNorm v = 1) :
    ∑ s, v s ^ 2 = 1 := by
  have h0 : 0 ≤ ∑ s, v s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg (v s)
  have h := Real.sq_sqrt h0
  unfold testNorm at hv
  rw [hv] at h
  linarith

/-- `Σ_s |v_s| |w_s| ≤ 1` for unit `v`, `w`. -/
private theorem gaussDiag_sum_abs_mul_le {ι : Type*} [Fintype ι] {v w : ι → ℝ}
    (hv : testNorm v = 1) (hw : testNorm w = 1) : ∑ s, |v s| * |w s| ≤ 1 := by
  have h : ∀ s, |v s| * |w s| ≤ (v s ^ 2 + w s ^ 2) / 2 := by
    intro s
    nlinarith [sq_nonneg (|v s| - |w s|), sq_abs (v s), sq_abs (w s)]
  calc ∑ s, |v s| * |w s| ≤ ∑ s, (v s ^ 2 + w s ^ 2) / 2 := Finset.sum_le_sum fun s _ => h s
    _ = ((∑ s, v s ^ 2) + ∑ s, w s ^ 2) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = 1 := by rw [gaussDiag_sum_sq hv, gaussDiag_sum_sq hw]; norm_num

/-- `|v| = 0` forces `v = 0`. -/
private theorem gaussDiag_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : testNorm v = 0) :
    v = 0 := by
  unfold testNorm at hv
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun s _ => sq_nonneg (v s)),
    Finset.sum_eq_zero_iff_of_nonneg fun s _ => sq_nonneg (v s)] at hv
  funext s
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hv s (Finset.mem_univ s))

/-- `|c v| = |c| |v|`. -/
private theorem gaussDiag_testNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    testNorm (c • v) = |c| * testNorm v := by
  unfold testNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- `⟨a v, A (b w)⟩ = a b ⟨v, A w⟩`. -/
private theorem gaussDiag_testBilin_smul {ι : Type*} [Fintype ι] (a b : ℝ) (v : ι → ℝ)
    (A : Matrix ι ι ℂ) (w : ι → ℝ) :
    testBilin (a • v) A (b • w) = ((a * b : ℝ) : ℂ) * testBilin v A w := by
  simp only [testBilin, dotProduct, mulVec, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `p = lawPow ε D ≥ 1`. -/
private theorem gaussDiag_one_le (ε D : ℝ) : 1 ≤ lawPow ε D := by
  unfold lawPow
  have := le_max_left 1 ⌈2 * (D + 1) / ε⌉₊
  omega

/-- The Markov exponent: `D + 1 ≤ (3ε/4 − ε/2) p`. -/
private theorem gaussDiag_exp {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    D + 1 ≤ (3 * ε / 4 - ε / 2) * (lawPow ε D : ℝ) := by
  set m : ℕ := max 1 ⌈2 * (D + 1) / ε⌉₊ with hm
  have hp : (lawPow ε D : ℝ) = 2 * (m : ℝ) := by simp [lawPow, hm]
  have h1 : 2 * (D + 1) / ε ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have h2 : 2 * (D + 1) ≤ (m : ℝ) * ε := (div_le_iff₀ hε).1 h1
  rw [hp]
  nlinarith

/-- `x^{-(D + k)} = x^{-D} / x^k`. -/
private theorem gaussDiag_rpow_neg_add {x : ℝ} (hx : 0 < x) (D : ℝ) (k : ℕ) :
    x ^ (-(D + k)) = x ^ (-D) / x ^ k := by
  rw [neg_add, Real.rpow_add hx, Real.rpow_neg hx.le (k : ℝ), Real.rpow_natCast, div_eq_mul_inv]

/-- `x^{a k} = (x^a)^k`. -/
private theorem gaussDiag_rpow_mul_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (k : ℕ) :
    x ^ (a * k) = (x ^ a) ^ k := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

/-- The thresholds for `N₀`: `N ≥ 2`, `N^{ε/4} ≥ max(2, 2 (2p − 1)!!)` and `τ^p N^{p+1} ≥ 1`. -/
private theorem gaussDiag_thresholds {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N ∧ max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4) ∧
      1 ≤ τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1) := by
  have h1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have h2 : ∀ᶠ N : ℕ in atTop, max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4) :=
    ((tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h3 : ∀ᶠ N : ℕ in atTop, 1 ≤ τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1) :=
    (Tendsto.const_mul_atTop (pow_pos hτ _) ((tendsto_pow_atTop (Nat.succ_ne_zero _)).comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop _
  exact eventually_atTop.1 (h1.and (h2.and h3))

/-! ## The core estimate for unit test vectors -/

section Core

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The core estimate of the Gaussian step of §12.2 (proof of Theorem 12.2 (i), as for
Lemma 6.2) for unit `v`, `w` at one `N` above the thresholds:
`ℙ(|⟨v, (G^W − Π^W) w⟩| > N^ε Ψ^W) ≤ N^{-D}`. -/
private theorem gaussDiag_unit {τ ε D : ℝ} (hτ : 0 < τ) (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N)
    (hX : max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4))
    (hB : 1 ≤ τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1))
    {a : Fin N → ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hW : IsGOE W) (hS : S ⊆ domW τ N)
    (h : EntrywiseLawWAt N (ε / 4) (lawD1 ε D) (diagonal a) W S)
    {z : ℂ} (hz : z ∈ S) {v w : Fin N → ℝ} (hv : testNorm v = 1) (hw : testNorm w = 1) :
    ℙ {ω | (N : ℝ) ^ ε * PsiW (specOf (diagonal a)) z <
      ‖testBilin v (gaussDiag_B a (W ω) z) w‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  set p := lawPow ε D with hp_def
  set Ψ := PsiW (specOf (diagonal a)) z with hΨ_def
  set X : ℝ := (N : ℝ) ^ (ε / 4) with hX_def
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hzD := hS hz
  have hzim : 0 < z.im := hzD.1
  have hzle : z.im ≤ τ⁻¹ := hzD.2.2.2
  have hzge : (N : ℝ) ^ (-1 + τ) ≤ z.im := hzD.2.2.1
  -- `η⁻¹ ≤ N`
  have hηN : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ)⁻¹ ≤ z.im := by
      refine le_trans ?_ hzge
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    calc z.im⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hNpos) h1
      _ = N := inv_inv _
  -- `Ψ ≥ 1/(Nη) ≥ τ/N > 0`
  have hΨ1 : 1 / (N * z.im) ≤ Ψ := by
    rw [hΨ_def, PsiW]
    linarith [Real.sqrt_nonneg ((mW (specOf (diagonal a)) z).im / (N * z.im))]
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNpos hzim
  have hΨpos : 0 < Ψ := lt_of_lt_of_le (div_pos one_pos hNη) hΨ1
  have hΨτ : τ / N ≤ Ψ := by
    refine le_trans ?_ hΨ1
    rw [div_le_div_iff₀ hNpos hNη]
    have : τ * z.im ≤ 1 := by
      calc τ * z.im ≤ τ * τ⁻¹ := mul_le_mul_of_nonneg_left hzle hτ.le
        _ = 1 := mul_inv_cancel₀ hτ.ne'
    nlinarith
  -- `X = N^{ε/4}`
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXK : lawMomConst p ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hp1 : 1 ≤ p := gaussDiag_one_le ε D
  have hXp : X ≤ X ^ p := le_self_pow₀ hX1 (by omega)
  have hXε2 : (N : ℝ) ^ (ε / 2) = X * X := by
    rw [hX_def, ← Real.rpow_add hNpos]; congr 1; ring
  have hXε34 : (N : ℝ) ^ (3 * ε / 4) = X ^ 3 := by
    rw [hX_def, ← gaussDiag_rpow_mul_nat hNpos.le]; congr 1; push_cast; ring
  have hXε : (N : ℝ) ^ ε = X ^ 4 := by
    rw [hX_def, ← gaussDiag_rpow_mul_nat hNpos.le]; congr 1; push_cast; ring
  -- the bad event `{max_{s,t} |B_{st}| > N^{ε/4} Ψ}`, of probability `≤ N² N^{-D₁}`
  set Bad : Set Ω := {ω | ∃ s t, X * Ψ < ‖gaussDiag_B a (W ω) z s t‖} with hBad_def
  have hBadU : Bad = ⋃ s, ⋃ t, {ω | X * Ψ < ‖gaussDiag_B a (W ω) z s t‖} := by
    ext ω
    simp [hBad_def]
  have hBadm : MeasurableSet Bad := by
    rw [hBadU]
    exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun t =>
      measurableSet_lt measurable_const ((gaussDiag_measurable_B a z s t).comp hWm).norm
  set c : ℝ := (N : ℝ) ^ (-lawD1 ε D) with hc_def
  have hc0 : 0 ≤ c := Real.rpow_nonneg hNpos.le _
  have hbad : ℙ Bad ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * c) := by
    rw [hBadU]
    calc ℙ (⋃ s, ⋃ t, {ω | X * Ψ < ‖gaussDiag_B a (W ω) z s t‖})
        ≤ ∑ s, ℙ (⋃ t, {ω | X * Ψ < ‖gaussDiag_B a (W ω) z s t‖}) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ s : Fin N, ∑ t : Fin N, ENNReal.ofReal c := by
          refine Finset.sum_le_sum fun s _ => (measure_iUnion_fintype_le _ _).trans ?_
          exact Finset.sum_le_sum fun t _ => h z hz s t
      _ = ENNReal.ofReal ((N : ℝ) ^ 2 * c) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring
  have hbadR : (ℙ Bad).toReal ≤ (N : ℝ) ^ 2 * c :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by positivity) hc0) hbad
  -- the dominating variable `L = η⁻¹` on the bad event and `N^{ε/4} Ψ` off it
  set L : Ω → ℝ := fun ω => if ω ∈ Bad then z.im⁻¹ else X * Ψ with hL_def
  have hXΨ0 : 0 ≤ X * Ψ := mul_nonneg (by linarith) hΨpos.le
  have hη0 : 0 ≤ z.im⁻¹ := (inv_pos.2 hzim).le
  have hL0 : ∀ ω, 0 ≤ L ω := fun ω => by
    simp only [hL_def]
    split_ifs
    · exact hη0
    · exact hXΨ0
  have hLB : ∀ ω s t, s ≠ t → ‖gaussDiag_B a (W ω) z s t‖ ≤ L ω := by
    intro ω s t hst
    simp only [hL_def]
    split_ifs with hω
    · unfold gaussDiag_B
      rw [Matrix.sub_apply, gaussDiag_piW_offdiag a hzim hst, sub_zero]
      exact gaussDiag_norm_GW_le a (hW.symm ω) hzim s t
    · simp only [hBad_def, Set.mem_ofPred_eq, not_exists, not_lt] at hω
      exact hω s t
  have hLm : Measurable L := Measurable.ite hBadm measurable_const measurable_const
  have hLp : ∀ ω, L ω ^ p ≤ (X * Ψ) ^ p + z.im⁻¹ ^ p * Bad.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp only [hL_def]
    split_ifs with hω
    · rw [Set.indicator_of_mem hω, mul_one]
      linarith [pow_nonneg hXΨ0 p]
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
  have hint_ind :
      Integrable (fun ω => (X * Ψ) ^ p + z.im⁻¹ ^ p * Bad.indicator (fun _ => (1 : ℝ)) ω) :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hBadm).const_mul _)
  have hint : Integrable fun ω => L ω ^ p :=
    Integrable.mono' hint_ind (hLm.pow_const p).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (hL0 ω) p)]
        exact hLp ω)
  have hIle : ∫ ω, L ω ^ p ≤ (X * Ψ) ^ p + z.im⁻¹ ^ p * ((N : ℝ) ^ 2 * c) := by
    calc ∫ ω, L ω ^ p ≤ ∫ ω, ((X * Ψ) ^ p + z.im⁻¹ ^ p * Bad.indicator (fun _ => (1 : ℝ)) ω) :=
          integral_mono hint hint_ind hLp
      _ = (X * Ψ) ^ p + z.im⁻¹ ^ p * (ℙ Bad).toReal := by
          rw [integral_add (integrable_const _)
            (((integrable_const (1 : ℝ)).indicator hBadm).const_mul _), integral_const,
            integral_const_mul, integral_indicator_const _ hBadm]
          simp [Measure.real]
      _ ≤ (X * Ψ) ^ p + z.im⁻¹ ^ p * ((N : ℝ) ^ 2 * c) := by
          gcongr
  obtain ⟨hint2, hmom⟩ := gaussDiag_moment hW a hzim hv hw (even_two_mul _) L hL0 hLB hint
  -- the bad term is `≤ Ψ^p`
  have hNpow : ∀ k : ℕ, 0 < (N : ℝ) ^ k := fun k => pow_pos hNpos k
  have hD₁p : -lawD1 ε D ≤ -((8 * p + 4 : ℕ) : ℝ) := by
    rw [neg_le_neg_iff, lawD1]; push_cast; exact le_max_left _ _
  have hc1 : c ≤ ((N : ℝ) ^ (8 * p + 4))⁻¹ := by
    refine (Real.rpow_le_rpow_of_exponent_le hN1' hD₁p).trans (le_of_eq ?_)
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
  have hbadterm : z.im⁻¹ ^ p * ((N : ℝ) ^ 2 * c) ≤ Ψ ^ p := by
    have hτN : ((N : ℝ) ^ (6 * p + 2))⁻¹ ≤ τ ^ p := by
      rw [inv_le_iff_one_le_mul₀ (hNpow _)]
      calc (1 : ℝ) ≤ τ ^ p * (N : ℝ) ^ (p + 1) := hB
        _ ≤ τ ^ p * (N : ℝ) ^ (6 * p + 2) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1' (by omega)) (pow_nonneg hτ.le _)
    calc z.im⁻¹ ^ p * ((N : ℝ) ^ 2 * c)
        ≤ (N : ℝ) ^ p * ((N : ℝ) ^ 2 * ((N : ℝ) ^ (8 * p + 4))⁻¹) := by
          gcongr
      _ = ((N : ℝ) ^ p)⁻¹ * ((N : ℝ) ^ (6 * p + 2))⁻¹ := by
          have e1 : (N : ℝ) ^ (8 * p + 4) =
              (N : ℝ) ^ p * (N : ℝ) ^ 2 * ((N : ℝ) ^ p * (N : ℝ) ^ (6 * p + 2)) := by
            rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
          rw [e1]
          have h1 := (hNpow p).ne'
          have h2 := (hNpow 2).ne'
          have h3 := (hNpow (6 * p + 2)).ne'
          field_simp
      _ ≤ ((N : ℝ) ^ p)⁻¹ * τ ^ p := by gcongr
      _ = (τ / N) ^ p := by rw [div_pow]; ring
      _ ≤ Ψ ^ p := pow_le_pow_left₀ (div_nonneg hτ.le hNpos.le) hΨτ p
  -- the moment bound `E|𝒵|^p ≤ (N^{ε/2} Ψ)^p`
  have hdf : (0 : ℝ) ≤ ((2 * p - 1).doubleFactorial : ℝ) := Nat.cast_nonneg _
  have hΨXp : Ψ ^ p ≤ (X * Ψ) ^ p :=
    pow_le_pow_left₀ hΨpos.le (le_mul_of_one_le_left hΨpos.le hX1) p
  have hmom' : ∫ ω, ‖offPart v (gaussDiag_B a (W ω) z) w‖ ^ p ≤
      ((N : ℝ) ^ (ε / 2) * Ψ) ^ p := by
    calc ∫ ω, ‖offPart v (gaussDiag_B a (W ω) z) w‖ ^ p
        ≤ ((2 * p - 1).doubleFactorial : ℝ) * ∫ ω, L ω ^ p := hmom
      _ ≤ ((2 * p - 1).doubleFactorial : ℝ) * ((X * Ψ) ^ p + (X * Ψ) ^ p) := by
          refine mul_le_mul_of_nonneg_left (hIle.trans ?_) hdf
          linarith
      _ = lawMomConst p * X ^ p * Ψ ^ p := by rw [lawMomConst, mul_pow]; ring
      _ ≤ X ^ p * X ^ p * Ψ ^ p := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hXK.trans hXp)
            (pow_nonneg (by linarith) _)) (pow_nonneg hΨpos.le _)
      _ = ((N : ℝ) ^ (ε / 2) * Ψ) ^ p := by rw [hXε2, mul_pow, mul_pow]
  -- Markov at `(ε/2 → 3ε/4, D + 1)`
  have hdom : ℙ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ <
      ‖offPart v (gaussDiag_B a (W ω) z) w‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
    DomAt.of_moment (ε := ε / 2) (ξ := fun ω => ‖offPart v (gaussDiag_B a (W ω) z) w‖)
      p hN1 (gaussDiag_exp hε D) (fun ω => norm_nonneg _) hΨpos hint2 hmom'
  -- assembly
  have hsub : {ω | (N : ℝ) ^ ε * Ψ < ‖testBilin v (gaussDiag_B a (W ω) z) w‖} ⊆
      Bad ∪ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (gaussDiag_B a (W ω) z) w‖} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, hBad_def, not_exists] at hc hω
    obtain ⟨h1, h2⟩ := hc
    set B := gaussDiag_B a (W ω) z with hB_def
    have hdiag : ‖∑ s, (v s : ℂ) * B s s * w s‖ ≤ X * Ψ := by
      calc ‖∑ s, (v s : ℂ) * B s s * w s‖ ≤ ∑ s, ‖(v s : ℂ) * B s s * w s‖ := norm_sum_le _ _
        _ ≤ ∑ s, X * Ψ * (|v s| * |w s|) := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
            calc |v s| * ‖B s s‖ * |w s| = ‖B s s‖ * (|v s| * |w s|) := by ring
              _ ≤ X * Ψ * (|v s| * |w s|) :=
                mul_le_mul_of_nonneg_right (h1 s s) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = X * Ψ * ∑ s, |v s| * |w s| := by rw [Finset.mul_sum]
        _ ≤ X * Ψ * 1 := mul_le_mul_of_nonneg_left (gaussDiag_sum_abs_mul_le hv hw) hXΨ0
        _ = X * Ψ := mul_one _
    have htot : ‖testBilin v B w‖ ≤ (N : ℝ) ^ ε * Ψ := by
      rw [testBilin_eq_diag_add_offPart]
      calc ‖∑ s, (v s : ℂ) * B s s * w s + offPart v B w‖
          ≤ ‖∑ s, (v s : ℂ) * B s s * w s‖ + ‖offPart v B w‖ := norm_add_le _ _
        _ ≤ X * Ψ + X ^ 3 * Ψ := by rw [← hXε34]; linarith
        _ ≤ X ^ 4 * Ψ := by
            rw [← add_mul]
            refine mul_le_mul_of_nonneg_right ?_ hΨpos.le
            have h3 : X ≤ X ^ 3 := le_self_pow₀ hX1 (by norm_num)
            have h4 : X ^ 3 * 2 ≤ X ^ 4 := by
              rw [show X ^ 4 = X ^ 3 * X by ring]
              exact mul_le_mul_of_nonneg_left hX2 (by positivity)
            linarith
        _ = (N : ℝ) ^ ε * Ψ := by rw [hXε]
    linarith
  -- 
  have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNpos _
  have ha2 : (N : ℝ) ^ 2 * c ≤ (N : ℝ) ^ (-D) / 2 := by
    have e1 : c ≤ (N : ℝ) ^ (-D) / (N : ℝ) ^ 4 := by
      rw [hc_def, ← gaussDiag_rpow_neg_add hNpos]
      refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
      rw [neg_le_neg_iff, lawD1]; push_cast; exact le_max_right _ _
    calc (N : ℝ) ^ 2 * c ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ (-D) / (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = (N : ℝ) ^ (-D) * (1 / (N : ℝ) ^ 2) := by
          field_simp
      _ ≤ (N : ℝ) ^ (-D) * (1 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hND.le
          rw [div_le_div_iff₀ (hNpow 2) (by norm_num)]
          nlinarith
      _ = (N : ℝ) ^ (-D) / 2 := by ring
  have hb2 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
    have := gaussDiag_rpow_neg_add hNpos D 1
    rw [Nat.cast_one, pow_one] at this
    rw [this]
    exact div_le_div_of_nonneg_left hND.le (by norm_num) hN2'
  have ha0 : 0 ≤ (N : ℝ) ^ 2 * c := mul_nonneg (by positivity) hc0
  calc ℙ {ω | (N : ℝ) ^ ε * Ψ < ‖testBilin v (gaussDiag_B a (W ω) z) w‖}
      ≤ ℙ (Bad ∪ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (gaussDiag_B a (W ω) z) w‖}) :=
        measure_mono hsub
    _ ≤ ℙ Bad + ℙ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (gaussDiag_B a (W ω) z) w‖} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * c) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hbad hdom
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 * c + (N : ℝ) ^ (-(D + 1))) :=
        (ENNReal.ofReal_add ha0 (Real.rpow_nonneg hNpos.le _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (by linarith)

end Core


/-- Lemma 6.2 analogue for the GOE: for `D = diag(a)`, the entrywise law at `(ε/4, D₁)` gives
the anisotropic law at `(ε, D)` (proof: diagonal part plus the off-diagonal part `𝒵`, whose
moments are bounded through sign flips `S W S`, which preserve the GOE law and fix `D`). -/
theorem goe_aniso_diag (τ ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : Fin N → ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      IsGOE W → S ⊆ domW τ N →
      EntrywiseLawWAt N (ε / 4) (lawD1 ε D) (diagonal a) W S →
      AnisotropicLawWAt N ε D (diagonal a) W S := by
  obtain ⟨N₀, hN₀⟩ := gaussDiag_thresholds hτ hε D
  refine ⟨N₀, fun N hN => ?_⟩
  intro Ω _ _ a W S hW hS h z hz v w
  obtain ⟨hN2, hX, hB⟩ := hN₀ N hN
  change ℙ {ω | (N : ℝ) ^ ε * (PsiW (specOf (diagonal a)) z * testNorm v * testNorm w) <
    ‖testBilin v (gaussDiag_B a (W ω) z) w‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))
  by_cases hv0 : testNorm v = 0
  · have : v = 0 := gaussDiag_eq_zero hv0
    subst this
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by simp)
    simp [hv0, testBilin, dotProduct, mulVec] at hω
  by_cases hw0 : testNorm w = 0
  · have : w = 0 := gaussDiag_eq_zero hw0
    subst this
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by simp)
    simp [hw0, testBilin, dotProduct, mulVec] at hω
  have hva : 0 < testNorm v := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv0)
  have hwb : 0 < testNorm w := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hw0)
  set α := testNorm v with hα
  set β := testNorm w with hβ
  have hv1 : testNorm (α⁻¹ • v) = 1 := by
    rw [gaussDiag_testNorm_smul, ← hα, abs_of_pos (inv_pos.2 hva), inv_mul_cancel₀ hva.ne']
  have hw1 : testNorm (β⁻¹ • w) = 1 := by
    rw [gaussDiag_testNorm_smul, ← hβ, abs_of_pos (inv_pos.2 hwb), inv_mul_cancel₀ hwb.ne']
  have hv' : v = α • (α⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hva.ne', one_smul]
  have hw' : w = β • (β⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hwb.ne', one_smul]
  have hαβ : 0 < α * β := mul_pos hva hwb
  refine le_trans (measure_mono fun ω hω => ?_)
    (gaussDiag_unit hτ hε hN2 hX hB hW hS h hz hv1 hw1)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have e : ‖testBilin v (gaussDiag_B a (W ω) z) w‖ =
      ‖testBilin (α⁻¹ • v) (gaussDiag_B a (W ω) z) (β⁻¹ • w)‖ * (α * β) := by
    conv_lhs => rw [hv', hw']
    rw [gaussDiag_testBilin_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hαβ, mul_comm]
  rw [e, show (N : ℝ) ^ ε * (PsiW (specOf (diagonal a)) z * α * β) =
    (N : ℝ) ^ ε * PsiW (specOf (diagonal a)) z * (α * β) by ring] at hω
  exact lt_of_mul_lt_mul_right hω hαβ.le

/-! ## Checks -/

section Checks

/-- `goe_aniso_diag` at `τ = 1/2`, `ε = D = 1` (hypothesis level `(1/4, lawD1 1 1)`) for the GOE
`goeW N`, `aᵢ = (−1)^i/4` and `S = 𝐃^W(1/2, N)`. The GOE and domain hypotheses are discharged;
the entrywise law (the deformed-GOE local law) stays a hypothesis: this is a conditional
example. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀,
    EntrywiseLawWAt N (1 / 4) (lawD1 1 1) (diagonal fun i : Fin N => (-1 : ℝ) ^ (i : ℕ) / 4)
      (goeW N) (domW (1 / 2) N) →
    AnisotropicLawWAt N 1 1 (diagonal fun i : Fin N => (-1 : ℝ) ^ (i : ℕ) / 4) (goeW N)
      (domW (1 / 2) N) := by
  obtain ⟨N₀, hN₀⟩ := goe_aniso_diag (1 / 2) 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN h => hN₀ N hN _ (goeW N) _ (isGOE_goeW N) subset_rfl h⟩

/-- The resolvent bound `|G^W_{st}| ≤ η⁻¹` for one sample of the GOE `goeW 3`, the diagonal
`a = (1, −1, 0)` and `z = i`. -/
example (ω : GOESpace 3) (s t : Fin 3) :
    ‖GW (diagonal ![1, -1, 0]) (goeW 3 ω) Complex.I s t‖ ≤ Complex.I.im⁻¹ :=
  gaussDiag_norm_GW_le _ ((isGOE_goeW 3).symm ω) (by simp) s t

/-- The sign flip `diag(1, −1, 1)` multiplies `(G^W − Π^W)_{01}` by `−1`, for `a = (1, −1, 0)`,
any `3 × 3` matrix and `z = i`. -/
example (Wm : Matrix (Fin 3) (Fin 3) ℝ) :
    gaussDiag_B ![1, -1, 0] (diagonal ![1, -1, 1] * Wm * (diagonal ![1, -1, 1])ᵀ)
        Complex.I 0 1 =
      ((1 : ℝ) : ℂ) * ((-1 : ℝ) : ℂ) * gaussDiag_B ![1, -1, 0] Wm Complex.I 0 1 :=
  gaussDiag_B_flip _ ![1, -1, 1] (fun i => by fin_cases i <;> norm_num) Wm (by simp) 0 1

end Checks

end Anisotropic

#print axioms Anisotropic.goe_aniso_diag
