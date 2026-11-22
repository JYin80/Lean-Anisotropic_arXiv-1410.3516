module

public import Anisotropic.Averaged.ClaimThree
public import Anisotropic.Averaged.Column
public import Anisotropic.Averaged.Defs
public import Anisotropic.Comparison.Brackets
public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.PrelimBounds
public import Anisotropic.Comparison.TaggedWords
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # (avg_pf_claim) for `n = 3`: the removal of `ν = μ` and the sum over tagged tuples (§9) -/

/-! ## Products, conjugations, the coefficients `f_n` -/

/-- The conjugation flags of `f_n`: `x` for `r < p/2`, `x̄` otherwise. -/
private def hatAvg_cs (p : ℕ) : Fin p → Bool := fun r => !decide ((r : ℕ) < p / 2)

/-- `f_n = ∑_κ ∏_r (a_{κ_r} or its conjugate)`. -/
private theorem hatAvg_fCoeff_eq (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    fCoeff p a n = ∑ κ ∈ Finset.Nat.antidiagonalTuple p n,
      ∏ r : Fin p, conjIf (hatAvg_cs p r) (a (κ r)) := by
  unfold fCoeff
  refine Finset.sum_congr rfl fun κ _ => Finset.prod_congr rfl fun r _ => ?_
  by_cases h : (r : ℕ) < p / 2 <;> simp [h, hatAvg_cs, conjIf]

private theorem hatAvg_conjIf_mul (c : Bool) (x y : ℂ) :
    conjIf c (x * y) = conjIf c x * conjIf c y := by
  cases c <;> simp [conjIf]

private theorem hatAvg_conjIf_add (c : Bool) (x y : ℂ) :
    conjIf c (x + y) = conjIf c x + conjIf c y := by
  cases c <;> simp [conjIf]

private theorem hatAvg_conjIf_sub (c : Bool) (x y : ℂ) :
    conjIf c (x - y) = conjIf c x - conjIf c y := by
  cases c <;> simp [conjIf]

private theorem hatAvg_conjIf_sum {ι : Type*} (c : Bool) (s : Finset ι) (f : ι → ℂ) :
    conjIf c (∑ a ∈ s, f a) = ∑ a ∈ s, conjIf c (f a) := by
  cases c <;> simp [conjIf]

private theorem hatAvg_norm_conjIf (c : Bool) (x : ℂ) : ‖conjIf c x‖ = ‖x‖ := by
  cases c <;> simp [conjIf]

private theorem hatAvg_conjIf_ofReal (c : Bool) (x : ℝ) : conjIf c (x : ℂ) = x := by
  cases c <;> simp [conjIf]

private theorem hatAvg_conjIf_zero (c : Bool) : conjIf c 0 = 0 := by
  cases c <;> simp [conjIf]

/-- `|∏ α − ∏ β| ≤ ∑_r d_r ∏_{r' ≠ r} B_{r'}` for `|α_r|, |β_r| ≤ B_r`, `|α_r − β_r| ≤ d_r`. -/
private theorem hatAvg_prod_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (α β : ι → ℂ)
    (B d : ι → ℝ) (hB : ∀ r ∈ s, 0 ≤ B r) (hα : ∀ r ∈ s, ‖α r‖ ≤ B r)
    (hβ : ∀ r ∈ s, ‖β r‖ ≤ B r) (hd : ∀ r ∈ s, ‖α r - β r‖ ≤ d r) :
    ‖∏ r ∈ s, α r - ∏ r ∈ s, β r‖ ≤ ∑ r ∈ s, d r * ∏ r' ∈ s.erase r, B r' := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hB' : ∀ r ∈ s, 0 ≤ B r := fun r hr => hB r (Finset.mem_insert_of_mem hr)
    have hα' : ∀ r ∈ s, ‖α r‖ ≤ B r := fun r hr => hα r (Finset.mem_insert_of_mem hr)
    have hβ' : ∀ r ∈ s, ‖β r‖ ≤ B r := fun r hr => hβ r (Finset.mem_insert_of_mem hr)
    have hd' : ∀ r ∈ s, ‖α r - β r‖ ≤ d r := fun r hr => hd r (Finset.mem_insert_of_mem hr)
    have ih' := ih hB' hα' hβ' hd'
    have hpa : ‖∏ r ∈ s, α r‖ ≤ ∏ r ∈ s, B r := by
      rw [norm_prod]; exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hα'
    have hBa : 0 ≤ B a := hB a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
    have e : α a * ∏ r ∈ s, α r - β a * ∏ r ∈ s, β r =
        (α a - β a) * ∏ r ∈ s, α r + β a * (∏ r ∈ s, α r - ∏ r ∈ s, β r) := by ring
    rw [e]
    have hsum : ∑ r ∈ s, d r * ∏ r' ∈ (insert a s).erase r, B r' =
        B a * ∑ r ∈ s, d r * ∏ r' ∈ s.erase r, B r' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hra : r ≠ a := fun h => ha (h ▸ hr)
      rw [Finset.erase_insert_of_ne (Ne.symm hra), Finset.prod_insert (fun h => ha
        (Finset.mem_of_mem_erase h))]
      ring
    rw [hsum]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (hd a (Finset.mem_insert_self a s)) hpa (norm_nonneg _)
        ((norm_nonneg _).trans (hd a (Finset.mem_insert_self a s)))
    · rw [norm_mul]
      exact mul_le_mul (hβ a (Finset.mem_insert_self a s)) ih' (norm_nonneg _) hBa

/-- `#T(p, n) ≤ (n + 1)^p`. -/
private theorem hatAvg_card_T (p n : ℕ) :
    ((Finset.Nat.antidiagonalTuple p n).card : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
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

/-! ## The deterministic matrix `Π` -/

private theorem hatAvg_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

/-- `(Σ (1 + wΣ)⁻¹)_{jl} = ∑ₖ U_{jk} σₖ (1 + σₖ w)⁻¹ U_{lk}` for `Σ = U diag(σ) Uᵀ`. -/
private theorem hatAvg_SigInv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (j l : Fin M) :
    (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
      ∑ k, (U j k : ℂ) * ((σ k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹) * (U l k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
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
  have hprod : cplx Sig * (1 + w • cplx Sig)⁻¹ = (cplx Uᵀ)ᵀ *
      diagonal (fun i => (σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    rw [hinv, e1]
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [c₁, Matrix.mul_one, diagonal_mul_diagonal]
  rw [hprod]
  simp only [Matrix.mul_apply, cplx, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.map_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.coe_algebraMap]

/-- `∑_l |(U a)_l|² = ∑_k |a_k|²` for `Uᵀ U = 1`. -/
private theorem hatAvg_sum_normSq {U : Matrix (Fin M) (Fin M) ℝ} (h₁ : Uᵀ * U = 1)
    (a : Fin M → ℂ) :
    ∑ l, ‖∑ k, (U l k : ℂ) * a k‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  have hU : ∀ x : Fin M → ℝ, ∑ l, (U *ᵥ x) l ^ 2 = ∑ l, x l ^ 2 := by
    intro x
    have e : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
      rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, transpose_mul,
        transpose_transpose, h₁, one_mulVec]
    simpa [dotProduct, sq] using e
  have hre : ∀ l, (∑ k, (U l k : ℂ) * a k).re = (U *ᵥ fun k => (a k).re) l := by
    intro l
    simp [mulVec, dotProduct, Complex.re_sum]
  have him : ∀ l, (∑ k, (U l k : ℂ) * a k).im = (U *ᵥ fun k => (a k).im) l := by
    intro l
    simp [mulVec, dotProduct, Complex.im_sum]
  have hn : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := fun x => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hn, Finset.sum_add_distrib, hre, him, hU]

private theorem hatAvg_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (i : Fin K) : ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

private theorem hatAvg_col_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₁ : Uᵀ * U = 1)
    (k : Fin K) : ∑ j, U j k ^ 2 = 1 := by
  have := congrFun (congrFun h₁ k) k
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- The `𝓘_M × 𝓘_M` block of `Π`: `|Π_{jl}| ≤ τ⁻¹c⁻¹`, `∑_l |Π_{jl}|² ≤ (τ⁻¹c⁻¹)²`, and
`∑_j Π_{jj} = −∑_k σ_k (1 + σ_k w)⁻¹`, under (bound_Sigma) and `|1 + σ_k w| ≥ c`. -/
private theorem hatAvg_PiM {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (hτ : 0 < τ) (hc : 0 < c) {w : ℂ} (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖) :
    (∀ j l, ‖(cplx Sig * (1 + w • cplx Sig)⁻¹) j l‖ ≤ τ⁻¹ * c⁻¹) ∧
    (∀ j, ∑ l, ‖(cplx Sig * (1 + w • cplx Sig)⁻¹) j l‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    ∑ j, (cplx Sig * (1 + w • cplx Sig)⁻¹) j j =
      ∑ k, (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ ∧
    (∀ j l, (cplx Sig * (1 + w • cplx Sig)⁻¹) j l = (cplx Sig * (1 + w • cplx Sig)⁻¹) l j) := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := hatAvg_diag hS.posDef
  have hw : ∀ i, 1 + (specOf Sig i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  set d : Fin M → ℂ := fun k => (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ with hd
  have hdle : ∀ k, ‖d k‖ ≤ τ⁻¹ * c⁻¹ := fun k => by
    simp only [hd]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ k).le]
    exact mul_le_mul (hle k) (inv_anti₀ hc (hOne k)) (inv_nonneg.2 (norm_nonneg _))
      ((hσ k).le.trans (hle k))
  have hD0 : 0 ≤ τ⁻¹ * c⁻¹ := by have := hτ.le; positivity
  have he := hatAvg_SigInv_entry h₂ h₁ hSd hw
  refine ⟨fun j l => ?_, fun j => ?_, ?_, fun j l => ?_⟩
  · rw [he]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |U j k|) (fun k => |U l k|)
    simp only [sq_abs] at hcs
    rw [hatAvg_row_sq h₂, hatAvg_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    calc ‖∑ k, (U j k : ℂ) * d k * (U l k : ℂ)‖ ≤ ∑ k, τ⁻¹ * c⁻¹ * (|U j k| * |U l k|) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hdle k) (abs_nonneg (U j k))
          nlinarith [abs_nonneg (U l k), abs_nonneg (U j k)]
      _ = τ⁻¹ * c⁻¹ * ∑ k, |U j k| * |U l k| := by rw [Finset.mul_sum]
      _ ≤ τ⁻¹ * c⁻¹ * 1 := mul_le_mul_of_nonneg_left hcs hD0
      _ = τ⁻¹ * c⁻¹ := mul_one _
  · have e1 : ∀ l, (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
        ∑ k, (U l k : ℂ) * ((U j k : ℂ) * d k) := fun l => by
      rw [he]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e1]
    rw [hatAvg_sum_normSq h₁]
    calc ∑ k, ‖(U j k : ℂ) * d k‖ ^ 2 ≤ ∑ k, U j k ^ 2 * (τ⁻¹ * c⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdle k) 2)
            (sq_nonneg _)
      _ = (τ⁻¹ * c⁻¹) ^ 2 := by rw [← Finset.sum_mul, hatAvg_row_sq h₂, one_mul]
  · simp only [he]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hatAvg_col_sq h₁ k
    have e : ∑ j, (U j k : ℂ) * d k * (U j k : ℂ) = ((∑ j, U j k ^ 2 : ℝ) : ℂ) * d k := by
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    simp [hd]
  · rw [he, he]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ`. -/
private theorem hatAvg_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

/-- `Π` on `S`: `|Π_{st}| ≤ τ⁻¹c⁻¹ + C_m`, `∑_l |Π_{jl}|² ≤ (τ⁻¹c⁻¹)²` on `𝓘_M`, and
`N⁻¹ ∑_{j ∈ 𝓘_M} Π_{jj} = −z − m⁻¹` (m_sc_eq). -/
private theorem hatAvg_Pi {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (∀ s t, ‖PiZ N Sig z s t‖ ≤ τ⁻¹ * c⁻¹ + mBoundConst τ) ∧
    (∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl j) (Sum.inl l)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    (∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl l) (Sum.inl j)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    (N : ℂ)⁻¹ * ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) = -z - (mFun N (specOf Sig) z)⁻¹ := by
  have hτ := hset.pos
  have hc := hset.c_pos
  have hzD := hset.domain.1 hz
  obtain ⟨-, hm2, -⟩ := gen_prop_m_specDomain (hatAvg_density hset hN) hzD
  have hCm := mBoundConst_pos hτ
  have hD0 : 0 ≤ τ⁻¹ * c⁻¹ := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := hatAvg_PiM hset.sigma hτ hc (hset.oneXm z hz)
  refine ⟨fun s t => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · rcases s with j | ν <;> rcases t with l | ν'
    · simp only [PiZ, piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
      linarith [h1 j l]
    · simp [PiZ, piMat]; positivity
    · simp [PiZ, piMat]; positivity
    · simp only [PiZ, piMat, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      split_ifs
      · linarith
      · simp only [norm_zero]; positivity
  · simpa [PiZ, piMat] using h2 j
  · have := h2 j
    simp only [PiZ, piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
    simpa only [h4] using this
  · have hσ : ∀ i, 0 ≤ specOf Sig i := fun i => by
      rw [specOf_eq hset.sigma.posDef.isHermitian]
      exact (hset.sigma.posDef.eigenvalues_pos i).le
    have hf := (mFun_spec N (specOf Sig) hσ hzD.1).2
    unfold fC at hf
    set m := mFun N (specOf Sig) z
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have e : ∑ i, (specOf Sig i : ℂ) / (N * (1 + specOf Sig i * m)) =
        (N : ℂ)⁻¹ * ∑ k, (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * m)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv, mul_inv]; ring
    have e2 : ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) =
        -∑ j, (cplx Sig * (1 + m • cplx Sig)⁻¹) j j := by
      simp [PiZ, piMat, m, Finset.sum_neg_distrib]
    rw [e2, h3, mul_neg, ← e]
    linear_combination -hf

/-- `Σ_{jj} ≤ τ⁻¹` under (bound_Sigma). -/
private theorem hatAvg_Sig_diag_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (j : Fin M) : Sig j j ≤ τ⁻¹ := by
  obtain ⟨U, h₂, -, hSd, hσ⟩ := hatAvg_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have e : Sig j j = ∑ k, U j k ^ 2 * specOf Sig k := by
    conv_lhs => rw [hSd]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  calc ∑ k, U j k ^ 2 * specOf Sig k ≤ ∑ k, U j k ^ 2 * τ⁻¹ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (sq_nonneg _)
    _ = τ⁻¹ := by rw [← Finset.sum_mul, hatAvg_row_sq h₂, one_mul]

/-- The rough bound `|G_{st}| ≤ (1 + 5|z|) τ⁻¹ / η` (opbound). -/
private theorem hatAvg_G_rough {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    ‖G Sig A z s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hq : ∀ u : Fin M ⊕ Fin N, eI u ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI u ≤ τ⁻¹ := by
    intro u
    have e : eI u ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI u = SigU (n := Fin N) Sig u u := by
      simp [eI, dotProduct, mulVec, Pi.single_apply]
    rw [e]
    rcases u with j | ν
    · simpa [SigU] using hatAvg_Sig_diag_le hS j
    · simpa [SigU] using hτi
  have h := opbound hS.posDef A hz (eI s) (eI t)
  rw [ent_eI_eI] at h
  have hs := Real.sqrt_le_sqrt (hq s)
  have ht := Real.sqrt_le_sqrt (hq t)
  have hsq : Real.sqrt τ⁻¹ * Real.sqrt τ⁻¹ = τ⁻¹ := Real.mul_self_sqrt (by positivity)
  have hK : 0 ≤ (1 + 5 * ‖z‖) / z.im := by positivity
  calc ‖G Sig A z s t‖ ≤ _ := h
    _ ≤ (1 + 5 * ‖z‖) / z.im * Real.sqrt τ⁻¹ * Real.sqrt τ⁻¹ := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hs ht (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)) hK
    _ = (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by rw [mul_assoc, hsq]

/-! ## The column forms and the minor `G^{(μ)}` -/

private theorem hatAvg_Gmu_row (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (t : Fin M ⊕ Fin N) : Gmu Sig A z μ (Sum.inr μ) t = 0 := by
  simp [Gmu, G1, Gm]

private theorem hatAvg_Gmu_col (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) : Gmu Sig A z μ s (Sum.inr μ) = 0 := by
  simp [Gmu, G1, Gm]

private theorem hatAvg_linForm_colC (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) (y : Fin M → ℝ) :
    linForm (colC Sig A z (eI s) μ) y = ∑ j, Gmu Sig A z μ s (Sum.inl j) * (y j : ℂ) := by
  simp only [linForm, colC, ent_eI_eI]

private theorem hatAvg_linForm_rowC (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) (y : Fin M → ℝ) :
    linForm (rowC Sig A z (eI s) μ) y = ∑ j, Gmu Sig A z μ (Sum.inl j) s * (y j : ℂ) := by
  simp only [linForm, rowC, ent_eI_eI]

/-- (Gia), (Gij): `G_{sμ} = −G_μμ (G^{(μ)} X)_{sμ}` for `s ≠ μ`. -/
private theorem hatAvg_G_col {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) :
    G Sig A z s (Sum.inr μ) = -G Sig A z (Sum.inr μ) (Sum.inr μ) *
      linForm (colC Sig A z (eI s) μ) (fun j => A j μ) := by
  have hGX : ∀ u, (G1 Sig A z (Sum.inr μ) * Xhat A) u (Sum.inr μ) =
      ∑ j, G1 Sig A z (Sum.inr μ) u (Sum.inl j) * (A j μ : ℂ) := by
    intro u; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  rw [hatAvg_linForm_colC]
  rcases s with j | ν
  · rw [(Gia hSig A hz j μ).1, hGX]
  · have hν : ν ≠ μ := fun h => hs (by rw [h])
    rw [(Gij hSig A hz ν μ hν).2.1, hGX]

/-- (Gia), (Gij): `G_{μs} = −G_μμ (X^* G^{(μ)})_{μs}` for `s ≠ μ`. -/
private theorem hatAvg_G_row {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) :
    G Sig A z (Sum.inr μ) s = -G Sig A z (Sum.inr μ) (Sum.inr μ) *
      linForm (rowC Sig A z (eI s) μ) (fun j => A j μ) := by
  have hXG : ∀ u, ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (Sum.inr μ) u =
      ∑ j, G1 Sig A z (Sum.inr μ) (Sum.inl j) u * (A j μ : ℂ) := by
    intro u; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx, mul_comm]
  rw [hatAvg_linForm_rowC]
  rcases s with j | ν
  · rw [(Gia hSig A hz j μ).2, hXG]
  · have hν : μ ≠ ν := fun h => hs (by rw [h])
    rw [(Gij hSig A hz μ ν hν).1, hXG]

/-- `G^{(μ)}_{st} = G_{st}` of the matrix with column `μ` set to zero, `s, t ≠ μ`. -/
private theorem hatAvg_Gmu_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) (ht : t ≠ Sum.inr μ) :
    Gmu Sig A z μ s t = G Sig (updCol A μ 0) z s t := by
  rw [← Gmu_updCol Sig A z μ 0, Gmu, Gstu hSig _ hz _ s t hs ht, hatAvg_G_col hSig _ hz μ s hs]
  have h0 : (fun j => updCol A μ 0 j μ) = 0 := by funext j; simp [updCol]
  rw [h0]
  simp [linForm]

/-- The rough bound `|G^{(μ)}_{st}| ≤ (1 + 5|z|) τ⁻¹ / η`. -/
private theorem hatAvg_Gmu_rough {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    ‖Gmu Sig A z μ s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by
  by_cases hs : s = Sum.inr μ
  · rw [hs, hatAvg_Gmu_row]; simp only [norm_zero]; positivity
  by_cases ht : t = Sum.inr μ
  · rw [ht, hatAvg_Gmu_col]; simp only [norm_zero]; positivity
  rw [hatAvg_Gmu_eq hS.posDef A hz μ s t hs ht]
  exact hatAvg_G_rough hS hτ hτ1 _ hz s t

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem hatAvg_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
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

/-- `ℤ₂` tags: `|σ|_v = 0` means no tag `2`. -/
private theorem hatAvg_ne_two {n : ℕ} {σ : Fin (n + 1) → Fin 3} (hv : tagV σ = 0)
    (l : Fin (n + 1)) :
    σ l ≠ 2 := by
  intro h
  have := (Finset.sum_eq_zero_iff.1 hv) l (Finset.mem_univ l)
  simp [h] at this

/-- The empty word with tag `0` at `v = e_ν`, `ν ≠ μ`: `A⁰ = G^{(μ)}_{νν} − Π_{νν}`. -/
private theorem hatAvg_emptyScal_zero (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) :
    emptyScal Sig A z (eI (Sum.inr ν)) μ 0 =
      Gmu Sig A z μ (Sum.inr ν) (Sum.inr ν) - PiZ N Sig z (Sum.inr ν) (Sum.inr ν) := by
  simp only [emptyScal, ite_true, hatAvg_vbar_inr, ent_eI_eI]
  simp [eI, hν.symm]

/-- The scalar of one bracket at `v = e_ν`: at most `K` when every entry of `G^{(μ)}` is. -/
private theorem hatAvg_brackScal_le (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {K : ℝ}
    (hK1 : 1 ≤ K) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K) (x y : Letter) (s : Fin 3) :
    ‖brackScal Sig A z (eI (Sum.inr ν)) i μ x y s‖ ≤ K := by
  have hl : ∀ x : Letter, ∃ u, letVec Sig (eI (Sum.inr ν)) i μ x = eI u := by
    intro x
    cases x
    · exact ⟨Sum.inr ν, hatAvg_vbar_inr Sig ν⟩
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr μ, rfl⟩
  obtain ⟨u, hu⟩ := hl x
  obtain ⟨u', hu'⟩ := hl y
  unfold brackScal
  split_ifs <;> first
    | (rw [hu, hu', ent_eI_eI]; exact hK u u')
    | (simp only [norm_one, norm_neg, norm_zero]; linarith)

/-- The letters `V`, `I` give unit vectors `e_s`, `s ≠ μ`, at `v = e_ν`, `ν ≠ μ`. -/
private theorem hatAvg_letVec (Sig : Matrix (Fin M) (Fin M) ℝ) {ν μ : Fin N} (hν : ν ≠ μ)
    (i : Fin M) (x : Letter) (hx : x ≠ .M) :
    ∃ s, s ≠ Sum.inr μ ∧ letVec Sig (eI (Sum.inr ν)) i μ x = eI s := by
  cases x
  · exact ⟨Sum.inr ν, fun h => hν (Sum.inr_injective h), hatAvg_vbar_inr Sig ν⟩
  · exact ⟨Sum.inl i, Sum.inl_ne_inr, rfl⟩
  · exact absurd rfl hx

/-- The coefficient vectors of `[G_{xy}]^s` are `colC(x)` with `x ≠ M` or `rowC(y)` with
`y ≠ M`. -/
private theorem hatAvg_brackForms_mem (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) (c : Fin M → ℂ) (hc : c ∈ brackForms Sig A z v i μ x y s) :
    (x ≠ .M ∧ c = colC Sig A z (letVec Sig v i μ x) μ) ∨
      (y ≠ .M ∧ c = rowC Sig A z (letVec Sig v i μ y) μ) := by
  fin_cases s <;> cases x <;> cases y <;> simp [brackForms] at hc ⊢ <;> tauto

/-- Every coefficient vector of `A⁺(w, σ)` at `v = e_ν`, `ν ≠ μ`, `ℤ₂` tags, is `colC(e_s)` or
`rowC(e_s)` with `s ≠ μ`. -/
private theorem hatAvg_tagForms_mem (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) (n : ℕ)
    (w : Word n) (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) (c : Fin M → ℂ)
    (hc : c ∈ tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ) :
    ∃ s, s ≠ Sum.inr μ ∧ (c = colC Sig A z (eI s) μ ∨ c = rowC Sig A z (eI s) μ) := by
  cases n with
  | zero =>
    have h2 := hatAvg_ne_two hv 0
    simp only [tagForms, emptyForms] at hc
    split_ifs at hc with h0 h1
    · simp at hc
    · rw [hatAvg_vbar_inr] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      exact ⟨Sum.inr ν, fun h => hν (Sum.inr_injective h), hc⟩
    · exact absurd (by revert h0 h1 h2; generalize σ 0 = t; fin_cases t <;> simp) h2
  | succ k =>
    simp only [tagForms, List.mem_flatten, List.mem_ofFn] at hc
    obtain ⟨L, ⟨l, rfl⟩, hcL⟩ := hc
    rcases hatAvg_brackForms_mem Sig A z _ i μ _ _ _ c hcL with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
    · obtain ⟨s, hs, he⟩ := hatAvg_letVec Sig hν i _ hx
      exact ⟨s, hs, Or.inl (by rw [he])⟩
    · obtain ⟨s, hs, he⟩ := hatAvg_letVec Sig hν i _ hy
      exact ⟨s, hs, Or.inr (by rw [he])⟩

/-- `|∏_{c ∈ L} ⟨c, y⟩| ≤ a^{|L|}` when every factor is at most `a`. -/
private theorem hatAvg_list_prod_le (L : List (Fin M → ℂ)) (y : Fin M → ℝ) {a : ℝ}
    (h : ∀ c ∈ L, ‖linForm c y‖ ≤ a) :
    ‖(L.map fun c => linForm c y).prod‖ ≤ a ^ L.length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul]
    have hc := h c (by simp)
    have ha : 0 ≤ a := (norm_nonneg _).trans hc
    rw [pow_succ, mul_comm (a ^ L.length)]
    exact mul_le_mul hc (ih fun c' hc' => h c' (by simp [hc'])) (norm_nonneg _) ha

/-- `Π_{sμ} = Π_{μs} = 0` for `s ≠ μ`. -/
private theorem hatAvg_Pi_off (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (μ : Fin N)
    (s : Fin M ⊕ Fin N) (hs : s ≠ Sum.inr μ) :
    PiZ N Sig z s (Sum.inr μ) = 0 ∧ PiZ N Sig z (Sum.inr μ) s = 0 := by
  rcases s with j | ν
  · simp [PiZ, piMat]
  · have hν : ν ≠ μ := fun h => hs (by rw [h])
    simp [PiZ, piMat, hν, Ne.symm hν]

/-- On the a priori event: `|(G^{(μ)}X)_{sμ}|, |(X^*G^{(μ)})_{μs}| ≤ L b` for `s ≠ μ`. -/
private theorem hatAvg_form_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {b L : ℝ}
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (s : Fin M ⊕ Fin N) (hs : s ≠ Sum.inr μ) :
    ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖ ≤ L * b ∧
      ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖ ≤ L * b := by
  obtain ⟨h1, h2⟩ := hatAvg_Pi_off Sig z μ s hs
  have hc := hG s (Sum.inr μ)
  have hr := hG (Sum.inr μ) s
  rw [h1, sub_zero, hatAvg_G_col hSig A hz μ s hs, norm_mul, norm_neg] at hc
  rw [h2, sub_zero, hatAvg_G_row hSig A hz μ s hs, norm_mul, norm_neg] at hr
  have hL : 0 ≤ L := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith [norm_nonneg (G Sig A z (Sum.inr μ) (Sum.inr μ))]
  constructor
  · calc ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖
        ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ *
            ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hμ
      _ ≤ L * b := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc hL
  · calc ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖
        ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ *
            ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hμ
      _ ≤ L * b := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr hL

/-! ## Polynomials in the column have all moments -/

section Mom

variable {ρ : Fin M → Measure ℝ} [∀ j, IsProbabilityMeasure (ρ j)]

/-- `f` is continuous and `|f|^n` is integrable for the column law, for every `n`. -/
private def hatAvg_Mom (ρ : Fin M → Measure ℝ) (f : (Fin M → ℝ) → ℂ) : Prop :=
  Continuous f ∧ ∀ n : ℕ, Integrable (fun y => ‖f y‖ ^ n) (Measure.pi ρ)

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem hatAvg_Mom.integrable {f : (Fin M → ℝ) → ℂ} (h : hatAvg_Mom ρ f) :
    Integrable f (Measure.pi ρ) :=
  (h.2 1).mono' h.1.aestronglyMeasurable (ae_of_all _ fun y => by simp)

private theorem hatAvg_Mom_const (c : ℂ) : hatAvg_Mom ρ fun _ => c :=
  ⟨continuous_const, fun _ => integrable_const _⟩

private theorem hatAvg_Mom_coord (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (j : Fin M) : hatAvg_Mom ρ fun y => ((y j : ℝ) : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_apply j), fun n => ?_⟩
  have h := (measurePreserving_eval ρ j).integrable_comp_of_integrable (hρ j n)
  refine h.congr (ae_of_all _ fun y => ?_)
  simp [Function.comp, Complex.norm_real]

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem hatAvg_Mom_mul {f g : (Fin M → ℝ) → ℂ} (hf : hatAvg_Mom ρ f)
    (hg : hatAvg_Mom ρ g) : hatAvg_Mom ρ fun y => f y * g y := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  refine ((hf.2 (2 * n)).add (hg.2 (2 * n))).mono'
    ((hf.1.mul hg.1).norm.pow n).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [norm_mul, mul_pow, Real.norm_of_nonneg (by positivity)]
  have hu := pow_nonneg (norm_nonneg (f y)) n
  have hv := pow_nonneg (norm_nonneg (g y)) n
  have e1 : ‖f y‖ ^ (2 * n) = (‖f y‖ ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  have e2 : ‖g y‖ ^ (2 * n) = (‖g y‖ ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  simp only [Pi.add_apply, e1, e2]
  nlinarith [sq_nonneg (‖f y‖ ^ n - ‖g y‖ ^ n)]

private theorem hatAvg_pow_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hxn := pow_nonneg hx n
  have hyn := pow_nonneg hy n
  rcases le_total x y with h | h
  · calc (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * y ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (x ^ n + y ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
  · calc (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * x ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (x ^ n + y ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem hatAvg_Mom_add {f g : (Fin M → ℝ) → ℂ} (hf : hatAvg_Mom ρ f)
    (hg : hatAvg_Mom ρ g) : hatAvg_Mom ρ fun y => f y + g y := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  refine (((hf.2 n).add (hg.2 n)).const_mul (2 ^ n)).mono'
    ((hf.1.add hg.1).norm.pow n).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) n).trans
    (hatAvg_pow_add_le (norm_nonneg _) (norm_nonneg _) n)

private theorem hatAvg_Mom_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℂ}
    (hf : ∀ a ∈ s, hatAvg_Mom ρ (f a)) : hatAvg_Mom ρ fun y => ∑ a ∈ s, f a y := by
  induction s using Finset.induction_on with
  | empty => simpa using hatAvg_Mom_const (ρ := ρ) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hatAvg_Mom_add (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

private theorem hatAvg_Mom_prod {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℂ}
    (hf : ∀ a ∈ s, hatAvg_Mom ρ (f a)) : hatAvg_Mom ρ fun y => ∏ a ∈ s, f a y := by
  induction s using Finset.induction_on with
  | empty => simpa using hatAvg_Mom_const (ρ := ρ) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact hatAvg_Mom_mul (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem hatAvg_Mom_conjIf (c : Bool) {f : (Fin M → ℝ) → ℂ} (hf : hatAvg_Mom ρ f) :
    hatAvg_Mom ρ fun y => conjIf c (f y) := by
  cases c
  · simpa [conjIf] using hf
  · refine ⟨Complex.continuous_conj.comp hf.1, fun n => ?_⟩
    simpa [conjIf, Complex.norm_conj] using hf.2 n

private theorem hatAvg_Mom_linForm (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (c : Fin M → ℂ) : hatAvg_Mom ρ fun y => linForm c y :=
  hatAvg_Mom_sum _ fun j _ => hatAvg_Mom_mul (hatAvg_Mom_const _) (hatAvg_Mom_coord hρ j)

end Mom

private theorem hatAvg_tagMu_le {n : ℕ} (σ : Fin (n + 1) → Fin 3) : tagMu σ ≤ n + 1 := by
  unfold tagMu
  calc ∑ l, (if σ l = 0 then 0 else 1) ≤ ∑ _l : Fin (n + 1), 1 :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> omega
    _ = n + 1 := by simp

private theorem hatAvg_degTab_le (x y : Letter) (s : Fin 3) : degTab x y s ≤ 2 := by
  revert x y s; decide

/-- `deg A(w, σ) ≤ 2 (n(w) + 1)`. -/
private theorem hatAvg_tagDeg_le (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagDeg n w σ ≤ 2 * (n + 1) := by
  cases n with
  | zero => simp only [tagDeg]; split_ifs <;> omega
  | succ k =>
    simp only [tagDeg]
    calc ∑ l, degTab (factorX w l) (factorY w l) (σ l) ≤ ∑ _l : Fin (k + 2), 2 :=
          Finset.sum_le_sum fun l _ => hatAvg_degTab_le _ _ _
      _ = 2 * (k + 1 + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

/-! ## Continuity in the matrix -/

section Cont

variable {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im)
include hSig hz

private theorem hatAvg_cont_G : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
  have hc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
    unfold linH cplx
    refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
    · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
    · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ • (linH Sig⁻¹ A z).adjugate := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Continuous.smul ((hc.matrix_det).inv₀ fun A => ?_) hc.matrix_adjugate
  exact ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig A hz)).ne_zero

private theorem hatAvg_cont_Gent (s t : Fin M ⊕ Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t :=
  (hatAvg_cont_G hSig hz).matrix_elem s t

private theorem hatAvg_cont_Gmu (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t := by
  by_cases hs : s = Sum.inr μ
  · subst hs; simp only [hatAvg_Gmu_row]; exact continuous_const
  by_cases ht : t = Sum.inr μ
  · subst ht; simp only [hatAvg_Gmu_col]; exact continuous_const
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t) =
      fun A => G Sig (updCol A μ 0) z s t := funext fun A => hatAvg_Gmu_eq hSig A hz μ s t hs ht
  rw [e]
  have hu : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => updCol A μ 0 := by
    refine continuous_pi fun j => continuous_pi fun ν => ?_
    by_cases h : ν = μ
    · simp only [updCol, h, ite_true]; exact continuous_const
    · simp only [updCol, h, ite_false]; exact (continuous_apply ν).comp (continuous_apply j)
  exact (hatAvg_cont_Gent hSig hz s t).comp hu

private theorem hatAvg_cont_entGmu (μ : Fin N) (x y : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y := by
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y) =
      fun A => ∑ s, ∑ t, (x s : ℂ) * Gmu Sig A z μ s t * (y t : ℂ) := by
    funext A; simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (hatAvg_cont_Gmu hSig hz μ s t)).mul continuous_const

omit hSig hz in
private theorem hatAvg_cont_col (μ : Fin N) (j : Fin M) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => ((A j μ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply j))

private theorem hatAvg_cont_colC (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (colC Sig A z x μ) fun j => A j μ :=
  continuous_finsetSum _ fun j _ =>
    (hatAvg_cont_entGmu hSig hz μ x _).mul (hatAvg_cont_col μ j)

private theorem hatAvg_cont_rowC (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (rowC Sig A z x μ) fun j => A j μ :=
  continuous_finsetSum _ fun j _ =>
    (hatAvg_cont_entGmu hSig hz μ _ x).mul (hatAvg_cont_col μ j)

private theorem hatAvg_cont_brack (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => brack Sig A z v i μ x y s := by
  have h1 := hatAvg_cont_colC hSig hz μ (letVec Sig v i μ x)
  have h2 := hatAvg_cont_rowC hSig hz μ (letVec Sig v i μ y)
  have h3 := hatAvg_cont_entGmu hSig hz μ (letVec Sig v i μ x) (letVec Sig v i μ y)
  unfold brack brackScal brackForms
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append,
      List.nil_append, mul_one, one_mul] <;>
    first
    | exact continuous_const
    | exact h3
    | exact h1
    | exact h2
    | exact h1.mul h2
    | exact continuous_const.mul h1
    | exact continuous_const.mul h2
    | exact continuous_const.mul (h1.mul h2)

private theorem hatAvg_cont_tagA (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ)
    (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => tagA Sig A z v i μ n w σ := by
  cases n with
  | zero =>
    have h1 := hatAvg_cont_colC hSig hz μ (vbar Sig v)
    have h2 := hatAvg_cont_rowC hSig hz μ (vbar Sig v)
    have h3 := hatAvg_cont_entGmu hSig hz μ (vbar Sig v) (vbar Sig v)
    simp only [tagA, emptyScal, emptyForms]
    split_ifs <;>
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
      first
      | exact h3.sub continuous_const
      | exact continuous_const.mul (h1.mul h2)
      | exact continuous_const.mul (by
          simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
          exact h1.add h2)
  | succ k =>
    simp only [tagA]
    exact continuous_finsetProd _ fun l _ => hatAvg_cont_brack hSig hz v i μ _ _ _

end Cont

/-- The rough bound `|A⁰(w, σ)| ≤ (K + K')^{n+1}` for `|G^{(μ)}_{st}| ≤ K`, `|Π_{st}| ≤ K'`. -/
private theorem hatAvg_tagScal_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {K K' : ℝ}
    (hK1 : 1 ≤ K) (hK'0 : 0 ≤ K') (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤ (K + K') ^ (n + 1) := by
  cases n with
  | zero =>
    simp only [tagScal, zero_add, pow_one]
    by_cases h0 : σ 0 = 0
    · rw [h0, hatAvg_emptyScal_zero Sig A z hν]
      exact (norm_sub_le _ _).trans (add_le_add (hK _ _) (hK' _ _))
    · simp only [emptyScal, h0, ite_false]
      split_ifs <;> simp <;> linarith
  | succ k =>
    simp only [tagScal, norm_prod]
    calc ∏ l : Fin (k + 2), ‖brackScal Sig A z (eI (Sum.inr ν)) i μ (factorX w l) (factorY w l)
          (σ l)‖ ≤ ∏ _l : Fin (k + 2), (K + K') :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ =>
            (hatAvg_brackScal_le Sig A z ν i μ hK1 hK _ _ _).trans (by linarith)
      _ = (K + K') ^ (k + 1 + 1) := by simp

/-! ## Rough bounds -/

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def hatAvg_sq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem hatAvg_sq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ hatAvg_sq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The moment constant `2^q (1 + τ^{−q}) (1 + C'_{2q})`. -/
private def hatAvg_KS (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  2 ^ q * (1 + τ⁻¹ ^ q) * (1 + max (C (2 * q)) 0)

/-- `E (1 + ‖X‖_F²)^q ≤ 2^q (1 + τ^{−q}) (1 + C'_{2q}) N^q` for `M ≤ τ⁻¹ N`, from
(moments of X-1). -/
private theorem hatAvg_moment {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + hatAvg_sq (X ω)) ^ q) ∧
      ∫ ω, (1 + hatAvg_sq (X ω)) ^ q ≤ hatAvg_KS τ C q * (N : ℝ) ^ q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold hatAvg_KS
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set C' := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : ∀ t : ℝ, (t ^ 2) ^ (n + 1) =
      ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * t| ^ (2 * (n + 1)) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  have hXi : ∀ α : Fin M × Fin N, Integrable fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1) := by
    intro α
    simp_rw [hpow]
    exact (hX.integrable_moment (2 * (n + 1)) α.1 α.2).const_mul _
  have hXle : ∀ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro α
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hX.moment (2 * (n + 1)) α.1 α.2).trans (le_max_left _ _))
      (by positivity)
  set cd : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcd
  have hcdMN : cd = (M : ℝ) * N := by
    rw [hcd, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  have hcd0 : 0 ≤ cd := by rw [hcdMN]; positivity
  have hSi : Integrable fun ω => ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    integrable_finsetSum _ fun α _ => hXi α
  have hSi' : Integrable fun ω => cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    hSi.const_mul _
  have h1i : Integrable fun ω => 1 + cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    (integrable_const _).add hSi'
  set g : Ω → ℝ := fun ω => 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := h1i.const_mul _
  have hle : ∀ ω, (1 + hatAvg_sq (X ω)) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (hatAvg_sq_nonneg (X ω)) (n + 1)
    have h2 : hatAvg_sq (X ω) ^ (n + 1) ≤
        cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg, one_pow, Nat.add_sub_cancel]
          gcongr
  have hmeas : Measurable fun ω => (1 + hatAvg_sq (X ω)) ^ (n + 1) := by
    unfold hatAvg_sq
    exact (measurable_const.add (Finset.measurable_sum _ fun α _ =>
      (hX.measurable α.1 α.2).pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + hatAvg_sq (X ω)) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := hatAvg_sq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add (integrable_const _) hSi',
      integral_const_mul, integral_finsetSum _ fun α _ => hXi α]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum : ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      cd * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ _α : Fin M × Fin N, ((N : ℝ) ^ (n + 1))⁻¹ * C' :=
          Finset.sum_le_sum fun α _ => hXle α
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM1 : cd ^ n * (cd * (((N : ℝ) ^ (n + 1))⁻¹ * C')) = (M : ℝ) ^ (n + 1) * C' := by
    rw [hcdMN]
    field_simp
    ring
  have hM2 : (M : ℝ) ^ (n + 1) ≤ τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
  have hNn : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN1r
  have hτn : 0 ≤ τ⁻¹ ^ (n + 1) := by positivity
  calc ∫ ω, (1 + hatAvg_sq (X ω)) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have h5 := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith
    _ ≤ hatAvg_KS τ C (n + 1) * (N : ℝ) ^ (n + 1) := by
        unfold hatAvg_KS
        rw [← hC']
        set P := (N : ℝ) ^ (n + 1)
        set T := τ⁻¹ ^ (n + 1)
        have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
        have hA : 1 + T * P * C' ≤ 2 * ((1 + T) * (1 + C') * P) := by
          nlinarith [mul_nonneg hτn hC'0, mul_nonneg (mul_nonneg hτn hC'0) (sub_nonneg.2 hNn)]
        calc 2 ^ n * (1 + T * P * C') ≤ 2 ^ n * (2 * ((1 + T) * (1 + C') * P)) :=
              mul_le_mul_of_nonneg_left hA h2n
          _ = 2 ^ (n + 1) * (1 + T) * (1 + C') * P := by ring

/-- `V = ∑_j |X_{jμ}|`, the `ℓ¹` norm of the column `μ`. -/
private def hatAvg_V (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) : ℝ := ∑ j, |A j μ|

private theorem hatAvg_V_nonneg (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) : 0 ≤ hatAvg_V A μ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `1 + V ≤ (1 + M)(1 + ‖X‖_F²)`. -/
private theorem hatAvg_V_le (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) :
    1 + hatAvg_V A μ ≤ (1 + M) * (1 + hatAvg_sq A) := by
  have h1 : hatAvg_V A μ ≤ ∑ j : Fin M, (1 + A j μ ^ 2) :=
    Finset.sum_le_sum fun j _ => by nlinarith [sq_abs (A j μ), abs_nonneg (A j μ)]
  have h2 : ∑ j : Fin M, A j μ ^ 2 ≤ hatAvg_sq A := by
    unfold hatAvg_sq
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun j _ => Finset.single_le_sum (fun ν _ => sq_nonneg (A j ν))
      (Finset.mem_univ μ)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have := hatAvg_sq_nonneg A
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- `|⟨c, X_μ⟩| ≤ R V` for the coefficient vectors of `A⁺(w, σ)` when `|G^{(μ)}_{st}| ≤ R`. -/
private theorem hatAvg_form_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {R : ℝ}
    (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hv : tagV σ = 0) :
    ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map
        fun c => linForm c fun j => A j μ).prod‖ ≤ (R * hatAvg_V A μ) ^ tagDeg n w σ := by
  rw [← tagForms_length Sig A z (eI (Sum.inr ν)) i μ]
  refine hatAvg_list_prod_le _ _ fun c hc => ?_
  obtain ⟨s, -, hc'⟩ := hatAvg_tagForms_mem Sig A z hν i n w σ hv c hc
  have key : ∀ f : Fin M → ℂ, (∀ j, ‖f j‖ ≤ R) →
      ‖∑ j, f j * ((A j μ : ℝ) : ℂ)‖ ≤ R * hatAvg_V A μ := by
    intro f hf
    unfold hatAvg_V
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hf j) (abs_nonneg _)
  rcases hc' with rfl | rfl
  · rw [hatAvg_linForm_colC]; exact key _ fun j => hR _ _
  · rw [hatAvg_linForm_rowC]; exact key _ fun j => hR _ _

/-- The rough bound `|A_{e_ν, i, μ}(w, σ)| ≤ W^{3(n+1)}`, `W = (R + K')(1 + R)(1 + V)`, when
`|G^{(μ)}_{st}| ≤ R`, `|Π_{st}| ≤ K'`. -/
private theorem hatAvg_tagA_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {R K' : ℝ}
    (hR1 : 1 ≤ R) (hK'0 : 0 ≤ K') (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hv : tagV σ = 0) :
    ‖tagA Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤
      ((R + K') * (1 + R) * (1 + hatAvg_V A μ)) ^ (3 * (n + 1)) := by
  have hV := hatAvg_V_nonneg A μ
  set W := (R + K') * (1 + R) * (1 + hatAvg_V A μ) with hW
  have hRK : 1 ≤ R + K' := by linarith
  have hW1 : 1 ≤ W := by
    have h2 : 1 ≤ 1 + R := by linarith
    have h3 : 1 ≤ 1 + hatAvg_V A μ := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ W := by rw [hW]; gcongr
  rw [tagA_eq_scal_mul, norm_mul]
  have hs := hatAvg_tagScal_rough Sig A z hν i hR1 hK'0 hR hK' n w σ
  have hf := hatAvg_form_rough Sig A z hν i hR n w σ hv
  have hd := hatAvg_tagDeg_le n w σ
  have hRV : R * hatAvg_V A μ ≤ W := by
    have : R * hatAvg_V A μ ≤ (1 + R) * (1 + hatAvg_V A μ) := by nlinarith
    calc R * hatAvg_V A μ ≤ (1 + R) * (1 + hatAvg_V A μ) := this
      _ ≤ (R + K') * ((1 + R) * (1 + hatAvg_V A μ)) :=
          le_mul_of_one_le_left (by positivity) hRK
      _ = W := by rw [hW]; ring
  have hRW : R + K' ≤ W := by
    rw [hW, mul_assoc]
    refine le_mul_of_one_le_right (by linarith) ?_
    nlinarith
  have h1 : (R + K') ^ (n + 1) ≤ W ^ (n + 1) := pow_le_pow_left₀ (by linarith) hRW _
  have h2 : (R * hatAvg_V A μ) ^ tagDeg n w σ ≤ W ^ (2 * (n + 1)) :=
    (pow_le_pow_left₀ (by positivity) hRV _).trans (pow_le_pow_right₀ hW1 hd)
  calc ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ *
        ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map fun c => linForm c fun j => A j μ).prod‖
      ≤ W ^ (n + 1) * W ^ (2 * (n + 1)) :=
        mul_le_mul (hs.trans h1) (hf.trans h2) (norm_nonneg _) (by positivity)
    _ = W ^ (3 * (n + 1)) := by rw [← pow_add]; ring_nf

/-! ## The column law, the split along an event, `Ψ` -/

/-- The law of the column `μ` has mean `0` and the moments bounded by (moments of X-1). -/
private theorem hatAvg_colLaw {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N)
    (hN : 1 ≤ N) (j : Fin M) :
    IsProbabilityMeasure (entryLaw X (j, μ)) ∧ ∫ y, y ∂(entryLaw X (j, μ)) = 0 ∧
    ∀ n : ℕ, Integrable (fun y => |y| ^ n) (entryLaw X (j, μ)) ∧
      ∫ y, |Real.sqrt N * y| ^ n ∂(entryLaw X (j, μ)) ≤ C n := by
  have hm := hX.measurable j μ
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have e : entryLaw X (j, μ) = (ℙ : Measure Ω).map fun ω => X ω j μ := rfl
  rw [e]
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_,
    fun n => ⟨?_, ?_⟩⟩
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    exact hX.mean j μ
  · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    have h := (hX.integrable_moment n j μ).const_mul ((Real.sqrt N)⁻¹ ^ n)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc]
    rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul]
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    exact hX.moment n j μ

/-- `y ≤ s y² + (4s)⁻¹` for `s > 0`. -/
private theorem hatAvg_amgm {s : ℝ} (hs : 0 < s) (y : ℝ) : y ≤ s * y ^ 2 + (4 * s)⁻¹ := by
  have h : s * y ^ 2 + (4 * s)⁻¹ - y = (2 * s * y - 1) ^ 2 / (4 * s) := by
    field_simp
    ring
  have : 0 ≤ (2 * s * y - 1) ^ 2 / (4 * s) := by positivity
  linarith

/-- Splitting `E|f|` along an event `Ξ`: if `|f| ≤ g` on `Ξ`, then
`|E f| ≤ E g + s E|f|² + P(Ξᶜ)/(4s)` for every `s > 0`. -/
private theorem hatAvg_split {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {f : Ω → ℂ} {g : Ω → ℝ} {Ξ : Set Ω} {s : ℝ} (hs : 0 < s)
    (hfi : Integrable fun ω => ‖f ω‖) (hf2i : Integrable fun ω => ‖f ω‖ ^ 2) (hgi : Integrable g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hon : ∀ ω ∈ Ξ, ‖f ω‖ ≤ g ω) :
    ‖∫ ω, f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  have hpt : ∀ ω, ‖f ω‖ ≤ g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    by_cases hω : ω ∈ Ξ
    · have := hon ω hω
      have : 0 ≤ s * ‖f ω‖ ^ 2 := by positivity
      linarith
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hmem]
      have := hatAvg_amgm hs ‖f ω‖
      linarith [hg0 ω]
  have hI : Integrable fun ω => Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    (integrable_const _).indicator (measurableSet_toMeasurable _ _)
  have h1 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 := hgi.add (hf2i.const_mul s)
  have h2 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    h1.add hI
  have e1 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω) =
      (∫ ω, (g ω + s * ‖f ω‖ ^ 2)) + ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    integral_add h1 hI
  have e2 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2) = (∫ ω, g ω) + ∫ ω, s * ‖f ω‖ ^ 2 :=
    integral_add hgi (hf2i.const_mul s)
  have e3 : ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω = (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    rw [integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable, smul_eq_mul]
  have hint : ∫ ω, ‖f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    refine (integral_mono hfi h2 hpt).trans (le_of_eq ?_)
    rw [e1, e2, e3, integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans hint

private theorem hatAvg_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

/-- `Ψ ≥ 1/(Nη) ≥ τ/N` on `𝐃(τ, N)`. -/
private theorem hatAvg_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : τ / N ≤ Psi N σ z := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := hz.1
  have hητ : z.im ≤ τ⁻¹ := hz.2.2.2.2
  unfold Psi
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

/-- `Ψ² ≥ Im m/(Nη) ≥ (K_m N)⁻¹` on `𝐃(τ, N)` (Lemma 4.10). -/
private theorem hatAvg_Psi_sq_ge {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (mBoundConst τ * N)⁻¹ ≤ Psi N (specOf Sig) z ^ 2 := by
  have hzD := hset.domain.1 hz
  obtain ⟨-, -, hm3⟩ := gen_prop_m_specDomain (hatAvg_density hset hN) hzD
  have hC := mBoundConst_pos hset.pos
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  set x := Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hsq : x ^ 2 = (mFun N (specOf Sig) z).im / (N * z.im) := Real.sq_sqrt (by positivity)
  have hle : x ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  have h1 : (mBoundConst τ * N)⁻¹ ≤ (mFun N (specOf Sig) z).im / (N * z.im) := by
    rw [le_div_iff₀ hpos]
    calc (mBoundConst τ * N)⁻¹ * (N * z.im) = (mBoundConst τ)⁻¹ * z.im := by
          field_simp
      _ ≤ (mFun N (specOf Sig) z).im := hm3
  calc (mBoundConst τ * N)⁻¹ ≤ x ^ 2 := by rw [hsq]; exact h1
    _ ≤ Psi N (specOf Sig) z ^ 2 := pow_le_pow_left₀ hx0 hle 2

/-- `Ψ ≤ (√C_m + 1) N^{−τ/2}` on `S` (Lemma 4.10, `N η ≥ N^τ`). -/
private theorem hatAvg_Psi_decay {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    Psi N (specOf Sig) z ≤ (Real.sqrt (mBoundConst τ) + 1) * (N : ℝ) ^ (-τ / 2) := by
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain (hatAvg_density hset hN) hzD
  have hC := mBoundConst_pos hτ
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  have haC : (mFun N (specOf Sig) z).im ≤ mBoundConst τ := le_trans (Complex.im_le_norm _) hm2
  have hNη : (N : ℝ) ^ τ ≤ N * z.im := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
    rw [← h1]; exact mul_le_mul_of_nonneg_left hzD.2.2.2.1 hNp.le
  have hNτ : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp τ
  have hpos : 0 < (N : ℝ) * z.im := lt_of_lt_of_le hNτ hNη
  have hh : ((N : ℝ) ^ (-τ / 2)) ^ 2 = ((N : ℝ) ^ τ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_neg hNp.le]; ring_nf
  have hh0 : 0 ≤ (N : ℝ) ^ (-τ / 2) := Real.rpow_nonneg hNp.le _
  have hh1 : (N : ℝ) ^ (-τ / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  unfold Psi
  have h1 : Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) ≤
      Real.sqrt (mBoundConst τ) * (N : ℝ) ^ (-τ / 2) := by
    rw [← Real.sqrt_sq hh0, ← Real.sqrt_mul hC.le]
    refine Real.sqrt_le_sqrt ?_
    rw [hh, div_le_iff₀ hpos]
    calc (mFun N (specOf Sig) z).im ≤ mBoundConst τ := haC
      _ = mBoundConst τ * ((N : ℝ) ^ τ)⁻¹ * (N : ℝ) ^ τ := by field_simp
      _ ≤ mBoundConst τ * ((N : ℝ) ^ τ)⁻¹ * (N * z.im) := by gcongr
  have h2 : 1 / ((N : ℝ) * z.im) ≤ (N : ℝ) ^ (-τ / 2) := by
    calc 1 / ((N : ℝ) * z.im) ≤ ((N : ℝ) ^ τ)⁻¹ := by
          rw [one_div]; exact inv_anti₀ hNτ hNη
      _ = ((N : ℝ) ^ (-τ / 2)) ^ 2 := hh.symm
      _ ≤ (N : ℝ) ^ (-τ / 2) := by nlinarith
  linarith

/-- `F̃ ≤ |m_N| + |m| ≤ R + C_m` when `|G_{νν}| ≤ R`. -/
private theorem hatAvg_Ft_le {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} {R Cm : ℝ} (hN : 1 ≤ N) (hR : ∀ s t, ‖G Sig A z s t‖ ≤ R)
    (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) : Ft Sig A z ≤ R + Cm := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Ft mN
  refine (norm_sub_le _ _).trans (add_le_add ?_ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν, G Sig A z (Sum.inr ν) (Sum.inr ν)‖ ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, R :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => hR _ _))
          (by positivity)
    _ = R := by simp; field_simp

/-! ## The coefficients at `ν = μ` and at `ν ≠ μ` on the a priori event -/

/-- `a_k − â_k = N⁻¹ a_k(e_μ)`: the term `ν = μ` of the average. -/
private theorem hatAvg_avg_sub (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (k : ℕ) :
    avgCoeff Sig A z i μ k - avgCoeffHat Sig A z i μ k =
      (N : ℂ)⁻¹ * resCoeff Sig A z (eI (Sum.inr μ)) i μ k := by
  unfold avgCoeff avgCoeffHat
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ)]
  ring

/-- `a_0(e_ν) = G_{νν} − m`. -/
private theorem hatAvg_resCoeff_zero (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ ν : Fin N) :
    resCoeff Sig A z (eI (Sum.inr ν)) i μ 0 =
      G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z := by
  simp only [resCoeff, pow_zero, one_mul, mul_one]
  rw [hatAvg_vbar_inr, ent_eI_eI]
  simp [PiZ, piMat]

/-- `|N⁻¹ ∑_{ν ≠ μ} f(ν)| ≤ B` when every `|f(ν)| ≤ B`. -/
private theorem hatAvg_avg_le {μ : Fin N} {f : Fin N → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ν, ν ≠ μ → ‖f ν‖ ≤ B) : ‖(N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, f ν‖ ≤ B := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν ∈ Finset.univ.erase μ, f ν‖ ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, B := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        exact (Finset.sum_le_sum fun ν hν => h ν (Finset.ne_of_mem_erase hν)).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => hB)
    _ = B := by simp; field_simp

/-- The sum over the two words of length one. -/
private theorem hatAvg_sum_word1 (f : Word 1 → ℂ) :
    ∑ w : Word 1, f w = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp
  rfl

/-- The factors `G_{xy}`, `x, y ∈ {i, μ}`, of the words at `v = e_μ`: at most `K`, and at most
`K b` off the diagonal. -/
private theorem hatAvg_factor_le {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {K b : ℝ} (hK1 : 1 ≤ K) (hb0 : 0 ≤ b)
    (hii : ‖G Sig A z (Sum.inl i) (Sum.inl i)‖ ≤ K)
    (hmm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K)
    (him : ‖G Sig A z (Sum.inl i) (Sum.inr μ)‖ ≤ b)
    (hmi : ‖G Sig A z (Sum.inr μ) (Sum.inl i)‖ ≤ b) :
    (∀ x y : Bool, ‖G Sig A z (letterS i μ x) (letterT i μ y)‖ ≤ K * (if x = y then b else 1)) ∧
    (∀ y : Bool, ‖G Sig A z (Sum.inr μ) (letterT i μ y)‖ ≤ K * (if y then b else 1)) ∧
    (∀ x : Bool, ‖G Sig A z (letterS i μ x) (Sum.inr μ)‖ ≤ K * (if x then 1 else b)) := by
  have hKb : b ≤ K * b := le_mul_of_one_le_left hb0 hK1
  refine ⟨fun x y => ?_, fun y => ?_, fun x => ?_⟩
  · cases x <;> cases y <;> simp [letterS, letterT] <;> linarith
  · cases y <;> simp [letterT] <;> linarith
  · cases x <;> simp [letterS] <;> linarith

/-- The words at `v = e_μ`: `|A_{e_μ}(w)| ≤ K^{n+1} ∏_l (b or 1)`, with `b` for the factors off
the diagonal. -/
private theorem hatAvg_wordA_mu {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {K b : ℝ} (hK1 : 1 ≤ K) (hb0 : 0 ≤ b)
    (hii : ‖G Sig A z (Sum.inl i) (Sum.inl i)‖ ≤ K)
    (hmm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K)
    (him : ‖G Sig A z (Sum.inl i) (Sum.inr μ)‖ ≤ b)
    (hmi : ‖G Sig A z (Sum.inr μ) (Sum.inl i)‖ ≤ b) (k : ℕ) (w : Word (k + 1)) :
    ‖wordA Sig A z (eI (Sum.inr μ)) i μ (k + 1) w‖ ≤ K ^ (k + 2) *
      ((if w 0 then b else 1) * (∏ l : Fin k, if w l.castSucc = w l.succ then b else 1) *
        (if w (Fin.last k) then 1 else b)) := by
  obtain ⟨h1, h2, h3⟩ := hatAvg_factor_le A z i μ hK1 hb0 hii hmm him hmi
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hite : ∀ c : Bool, 0 ≤ (if c then b else (1 : ℝ)) := fun c => by
    cases c <;> simp [hb0]
  have hite' : ∀ c : Bool, 0 ≤ (if c then (1 : ℝ) else b) := fun c => by
    cases c <;> simp [hb0]
  have hiteP : ∀ c : Prop, [Decidable c] → 0 ≤ (if c then b else (1 : ℝ)) := fun c _ => by
    split_ifs <;> linarith
  simp only [wordA, hatAvg_vbar_inr, ent_eI_eI]
  rw [norm_mul, norm_mul, norm_prod]
  have hmid : ∏ l : Fin k, ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖ ≤
      K ^ k * ∏ l : Fin k, (if w l.castSucc = w l.succ then b else 1) := by
    calc _ ≤ ∏ l : Fin k, K * (if w l.castSucc = w l.succ then b else 1) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => h1 _ _
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hP0 : 0 ≤ ∏ l : Fin k, (if w l.castSucc = w l.succ then b else (1 : ℝ)) :=
    Finset.prod_nonneg fun l _ => hiteP _
  calc (‖G Sig A z (Sum.inr μ) (letterT i μ (w 0))‖ *
        ∏ l : Fin k, ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖) *
        ‖G Sig A z (letterS i μ (w (Fin.last k))) (Sum.inr μ)‖
      ≤ (K * (if w 0 then b else 1)) *
          (K ^ k * ∏ l : Fin k, (if w l.castSucc = w l.succ then b else 1)) *
          (K * (if w (Fin.last k) then 1 else b)) := by
        refine mul_le_mul (mul_le_mul (h2 _) hmid (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg hK0 (hite _))) (h3 _) (norm_nonneg _) ?_
        exact mul_nonneg (mul_nonneg hK0 (hite _)) (mul_nonneg (pow_nonneg hK0 _) hP0)
    _ = _ := by ring

/-- The coefficients at `v = e_μ` on the a priori event: `|a_k(e_μ)| ≤ 8 K^5 b` for
`k ≤ 3`, except the word `𝛍𝐢𝐢𝛍` at `k = 2`. -/
private theorem hatAvg_resCoeff_mu {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {K b : ℝ}
    (hK1 : 1 ≤ K) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hii : ‖G Sig A z (Sum.inl i) (Sum.inl i)‖ ≤ K)
    (hmm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ K)
    (him : ‖G Sig A z (Sum.inl i) (Sum.inr μ)‖ ≤ b)
    (hmi : ‖G Sig A z (Sum.inr μ) (Sum.inl i)‖ ≤ b)
    (hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b) (k : ℕ)
    (hk : k ≤ 3) :
    ‖resCoeff Sig A z (eI (Sum.inr μ)) i μ k -
      (if k = 2 then G Sig A z (Sum.inr μ) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inl i) *
        G Sig A z (Sum.inr μ) (Sum.inr μ) else 0)‖ ≤ 8 * K ^ 5 * b := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hW := hatAvg_wordA_mu A z i μ hK1 hb0 hii hmm him hmi
  have hbb : b * b ≤ b := by nlinarith
  have hbbb : b * (b * b) ≤ b := by nlinarith
  have hK5 : ∀ j ≤ 5, K ^ j ≤ K ^ 5 := fun j hj => pow_le_pow_right₀ hK1 hj
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [hatAvg_resCoeff_zero]
    simp only [show (0 : ℕ) ≠ 2 by norm_num, ↓reduceIte, sub_zero]
    calc _ ≤ b := hgm
      _ ≤ 8 * K ^ 5 * b := by
          have : 1 ≤ K ^ 5 := one_le_pow₀ hK1
          nlinarith
  · rw [resCoeff_eq_sum_wordA hSig A hz]
    simp only [show (1 : ℕ) ≠ 2 by norm_num, ↓reduceIte, sub_zero, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
    have hw : ∀ w : Word 1, ‖wordA Sig A z (eI (Sum.inr μ)) i μ 1 w‖ ≤ K ^ 2 * b := by
      intro w
      refine (hW 0 w).trans ?_
      have e : w (Fin.last 0) = w 0 := rfl
      rw [e, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK0 _)
      cases w 0 <;> simp
    calc ‖∑ w : Word 1, wordA Sig A z (eI (Sum.inr μ)) i μ 1 w‖
        ≤ ∑ _w : Word 1, K ^ 2 * b := (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => hw w)
      _ = 2 * (K ^ 2 * b) := by simp
      _ ≤ 8 * K ^ 5 * b := by
          nlinarith [mul_le_mul_of_nonneg_right (hK5 2 (by norm_num)) hb0,
            mul_nonneg (pow_nonneg hK0 5) hb0]
  · rw [resCoeff_eq_sum_wordA hSig A hz]
    simp only [↓reduceIte, neg_one_sq, one_mul]
    set FT : Word 2 := ![false, true] with hFT
    have hFTv : wordA Sig A z (eI (Sum.inr μ)) i μ 2 FT =
        G Sig A z (Sum.inr μ) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inl i) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) := by
      simp [wordA, hFT, hatAvg_vbar_inr, ent_eI_eI, letterT, letterS]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ FT), hFTv, add_sub_cancel_left]
    have hw : ∀ w ∈ Finset.univ.erase FT, ‖wordA Sig A z (eI (Sum.inr μ)) i μ 2 w‖ ≤
        K ^ 3 * b := by
      intro w hw
      have hne : w ≠ FT := Finset.ne_of_mem_erase hw
      refine (hW 1 w).trans ?_
      have e : w (Fin.last 1) = w 1 := rfl
      rw [e, Fin.prod_univ_one]
      have e0 : w (Fin.castSucc (0 : Fin 1)) = w 0 := rfl
      have e1 : w (Fin.succ (0 : Fin 1)) = w 1 := rfl
      rw [e0, e1]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK0 _)
      have hnot : ¬(w 0 = false ∧ w 1 = true) := by
        rintro ⟨h0, h1⟩
        apply hne
        funext l
        fin_cases l
        · simpa [hFT] using h0
        · simpa [hFT] using h1
      revert hnot
      cases w 0 <;> cases w 1 <;> simp <;> nlinarith
    calc ‖∑ w ∈ Finset.univ.erase FT, wordA Sig A z (eI (Sum.inr μ)) i μ 2 w‖
        ≤ ∑ _w ∈ Finset.univ.erase FT, K ^ 3 * b := (norm_sum_le _ _).trans (Finset.sum_le_sum hw)
      _ ≤ ∑ _w : Word 2, K ^ 3 * b :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => mul_nonneg (pow_nonneg hK0 _) hb0
      _ = 4 * (K ^ 3 * b) := by simp
      _ ≤ 8 * K ^ 5 * b := by
          nlinarith [mul_le_mul_of_nonneg_right (hK5 3 (by norm_num)) hb0,
            mul_nonneg (pow_nonneg hK0 5) hb0]
  · rw [resCoeff_eq_sum_wordA hSig A hz]
    simp only [show (3 : ℕ) ≠ 2 by norm_num, ↓reduceIte, sub_zero, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
    have hw : ∀ w : Word 3, ‖wordA Sig A z (eI (Sum.inr μ)) i μ 3 w‖ ≤ K ^ 4 * b := by
      intro w
      refine (hW 2 w).trans ?_
      have e : w (Fin.last 2) = w 2 := rfl
      rw [e, Fin.prod_univ_two]
      have e0 : w (Fin.castSucc (0 : Fin 2)) = w 0 := rfl
      have e1 : w (Fin.succ (0 : Fin 2)) = w 1 := rfl
      have e2 : w (Fin.castSucc (1 : Fin 2)) = w 1 := rfl
      have e3 : w (Fin.succ (1 : Fin 2)) = w 2 := rfl
      rw [e0, e1, e2, e3]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK0 _)
      cases w 0 <;> cases w 1 <;> cases w 2 <;> simp <;> nlinarith
    calc ‖∑ w : Word 3, wordA Sig A z (eI (Sum.inr μ)) i μ 3 w‖
        ≤ ∑ _w : Word 3, K ^ 4 * b := (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => hw w)
      _ = 8 * (K ^ 4 * b) := by simp
      _ ≤ 8 * K ^ 5 * b := by
          nlinarith [mul_le_mul_of_nonneg_right (hK5 4 (by norm_num)) hb0,
            mul_nonneg (pow_nonneg hK0 5) hb0]

/-! ## The column forms of `â_0`, `â_1` and of the word `𝛍𝐢𝐢𝛍` -/

/-- `(G^{(μ)} y)_ν = ∑_j G^{(μ)}_{νj} y_j`. -/
private def hatAvg_al (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ ν : Fin N) (y : Fin M → ℝ) : ℂ :=
  linForm (colC Sig A z (eI (Sum.inr ν)) μ) y

/-- `(yᵀ G^{(μ)})_ν = ∑_j y_j G^{(μ)}_{jν}`. -/
private def hatAvg_be (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ ν : Fin N) (y : Fin M → ℝ) : ℂ :=
  linForm (rowC Sig A z (eI (Sum.inr ν)) μ) y

/-- `Ŝ = N⁻¹ ∑_{ν ≠ μ} (G^{(μ)}_{νν} − m)`. -/
private def hatAvg_Sh (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
    (Gmu Sig A z μ (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z)

/-- `q(y) = N⁻¹ ∑_{ν ≠ μ} (G^{(μ)} y)_ν (yᵀ G^{(μ)})_ν`. -/
private def hatAvg_q (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (y : Fin M → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, hatAvg_al Sig A z μ ν y * hatAvg_be Sig A z μ ν y

/-- `L(y) = N⁻¹ ∑_{ν ≠ μ} (G^{(μ)}_{νi} (yᵀ G^{(μ)})_ν + (G^{(μ)} y)_ν G^{(μ)}_{iν})`. -/
private def hatAvg_Lf (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (y : Fin M → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
    (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * hatAvg_be Sig A z μ ν y +
      hatAvg_al Sig A z μ ν y * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν))

/-- `ℓ = N⁻¹ m² G^{(μ)}_{ii}`. -/
private def hatAvg_ell (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * (mFun N (specOf Sig) z ^ 2 * Gmu Sig A z μ (Sum.inl i) (Sum.inl i))

/-- The leading coefficients `λ_0 = Ŝ + m q`, `λ_1 = m L`. -/
private def hatAvg_lam (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (y : Fin M → ℝ) (k : ℕ) : ℂ :=
  if k = 0 then hatAvg_Sh Sig A z μ + mFun N (specOf Sig) z * hatAvg_q Sig A z μ y
  else if k = 1 then mFun N (specOf Sig) z * hatAvg_Lf Sig A z i μ y else 0

/-- The leading part of `f_3(a) − f_3(â)`: the word `𝛍𝐢𝐢𝛍` at `ν = μ` with `G_μμ → m`,
`G_{ii} → G^{(μ)}_{ii}`, against the leading parts of `â_0`, `â_1`. -/
private def hatAvg_Lead (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (p : ℕ) (y : Fin M → ℝ) : ℂ :=
  ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
    conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) *
      ∏ r ∈ Finset.univ.erase r₁, conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r))

/-- `a_1(e_ν) = −(G_{νi} G_{μν} + G_{νμ} G_{iν})`. -/
private theorem hatAvg_resCoeff_one {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ ν : Fin N) :
    resCoeff Sig A z (eI (Sum.inr ν)) i μ 1 =
      -(G Sig A z (Sum.inr ν) (Sum.inl i) * G Sig A z (Sum.inr μ) (Sum.inr ν) +
        G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inr ν)) := by
  rw [resCoeff_eq_sum_wordA hSig A hz, hatAvg_sum_word1]
  simp [wordA, hatAvg_vbar_inr, ent_eI_eI, letterT, letterS]

/-- `G_{νν} − m − (G^{(μ)}_{νν} − m) − m (G^{(μ)}y)_ν (yᵀG^{(μ)})_ν = (G_μμ − m)(…)` at the
column of `A`, `ν ≠ μ` (Gstu). -/
private theorem hatAvg_term0 {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) {μ ν : Fin N} (hν : ν ≠ μ) :
    (G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z) -
        (Gmu Sig A z μ (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z) -
        mFun N (specOf Sig) z * (hatAvg_al Sig A z μ ν (fun j => A j μ) *
          hatAvg_be Sig A z μ ν (fun j => A j μ)) =
      (G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z) *
        (hatAvg_al Sig A z μ ν (fun j => A j μ) * hatAvg_be Sig A z μ ν (fun j => A j μ)) := by
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  have hg : G Sig A z (Sum.inr μ) (Sum.inr μ) ≠ 0 := G_diag_ne_zero hSig A hz _
  have hs := Gstu hSig A hz (Sum.inr μ) _ _ hne hne
  have hc := hatAvg_G_col hSig A hz μ _ hne
  have hr := hatAvg_G_row hSig A hz μ _ hne
  rw [Gmu, hs, hc, hr]
  unfold hatAvg_al hatAvg_be
  field_simp
  ring

/-- `a_1(e_ν) − m (G^{(μ)}_{νi} (yᵀG^{(μ)})_ν + (G^{(μ)}y)_ν G^{(μ)}_{iν})` at the column of `A`,
`ν ≠ μ` (Gstu). -/
private theorem hatAvg_term1 {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) {μ ν : Fin N}
    (hν : ν ≠ μ) :
    resCoeff Sig A z (eI (Sum.inr ν)) i μ 1 - mFun N (specOf Sig) z *
        (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * hatAvg_be Sig A z μ ν (fun j => A j μ) +
          hatAvg_al Sig A z μ ν (fun j => A j μ) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)) =
      (G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z) *
        (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * hatAvg_be Sig A z μ ν (fun j => A j μ) +
          hatAvg_al Sig A z μ ν (fun j => A j μ) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)) +
        (G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inl i) *
            hatAvg_be Sig A z μ ν (fun j => A j μ) +
          hatAvg_al Sig A z μ ν (fun j => A j μ) * G Sig A z (Sum.inl i) (Sum.inr μ) *
            G Sig A z (Sum.inr μ) (Sum.inr ν)) := by
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  have hie : (Sum.inl i : Fin M ⊕ Fin N) ≠ Sum.inr μ := Sum.inl_ne_inr
  have hg : G Sig A z (Sum.inr μ) (Sum.inr μ) ≠ 0 := G_diag_ne_zero hSig A hz _
  have h1 := Gstu hSig A hz (Sum.inr μ) _ _ hne hie
  have h2 := Gstu hSig A hz (Sum.inr μ) _ _ hie hne
  have hc := hatAvg_G_col hSig A hz μ _ hne
  have hr := hatAvg_G_row hSig A hz μ _ hne
  have hal : hatAvg_al Sig A z μ ν (fun j => A j μ) =
      -G Sig A z (Sum.inr ν) (Sum.inr μ) / G Sig A z (Sum.inr μ) (Sum.inr μ) := by
    unfold hatAvg_al; rw [hc]; field_simp
  have hbe : hatAvg_be Sig A z μ ν (fun j => A j μ) =
      -G Sig A z (Sum.inr μ) (Sum.inr ν) / G Sig A z (Sum.inr μ) (Sum.inr μ) := by
    unfold hatAvg_be; rw [hr]; field_simp
  rw [hatAvg_resCoeff_one hSig A hz, Gmu, h1, h2, hal, hbe]
  field_simp
  ring

/-- `G_μμ G_{ii} G_μμ − m² G^{(μ)}_{ii} = (G_μμ² − m²) G^{(μ)}_{ii} + G_μμ G_{iμ} G_{μi}`. -/
private theorem hatAvg_term2 {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) :
    G Sig A z (Sum.inr μ) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inl i) *
        G Sig A z (Sum.inr μ) (Sum.inr μ) -
        mFun N (specOf Sig) z ^ 2 * Gmu Sig A z μ (Sum.inl i) (Sum.inl i) =
      (G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z) *
          (G Sig A z (Sum.inr μ) (Sum.inr μ) + mFun N (specOf Sig) z) *
          Gmu Sig A z μ (Sum.inl i) (Sum.inl i) +
        G Sig A z (Sum.inr μ) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inr μ) *
          G Sig A z (Sum.inr μ) (Sum.inl i) := by
  have hie : (Sum.inl i : Fin M ⊕ Fin N) ≠ Sum.inr μ := Sum.inl_ne_inr
  have hg : G Sig A z (Sum.inr μ) (Sum.inr μ) ≠ 0 := G_diag_ne_zero hSig A hz _
  have h1 := Gstu hSig A hz (Sum.inr μ) _ _ hie hie
  rw [Gmu, h1]
  field_simp
  ring

/-! ## One shape `κ`: `∏ c(a) − ∏ c(â)` minus its leading part -/

/-- For `∑_r κ_r = 3` and `κ_{r₁} = 2`, every other `κ_r ≤ 1`. -/
private theorem hatAvg_kappa_le {p : ℕ} {κ : Fin p → ℕ} (hκ : ∑ r, κ r = 3) {r₁ : Fin p}
    (h₁ : κ r₁ = 2) {r : Fin p} (hr : r ≠ r₁) : κ r ≤ 1 := by
  have h2 : ∑ r' ∈ ({r₁, r} : Finset (Fin p)), κ r' ≤ ∑ r', κ r' :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair (Ne.symm hr)] at h2
  omega

/-- One shape `κ ∈ T(p, 3)`: with `â'_k = â_k + [k = 2] e`, `|a_k − â'_k| ≤ d`, `|e − ℓ| ≤ d₂`,
`|â_k − λ_k| ≤ d₃` (`k ≤ 1`), all factors at most `B` and `|ℓ| ≤ E`,
`|∏ c(a_κ) − ∏ c(â_κ) − ∑_{κ_{r₁} = 2} c(ℓ) ∏_{r ≠ r₁} c(λ_{κ_r})| ≤
p d B^{p−1} + d₂ B^{p−1} + p E d₃ B^{p−2}`. -/
private theorem hatAvg_kappa {p : ℕ} (cs : Fin p → Bool) (κ : Fin p → ℕ) (hκ : ∑ r, κ r = 3)
    (a â lam : ℕ → ℂ) (e ℓ : ℂ) {B E d d₂ d₃ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (ha : ∀ k ≤ 3, ‖a k‖ ≤ B) (hâ : ∀ k ≤ 3, ‖â k‖ ≤ B) (hâ' : ‖â 2 + e‖ ≤ B)
    (had : ∀ k ≤ 3, ‖a k - (â k + if k = 2 then e else 0)‖ ≤ d)
    (hlam : ∀ k ≤ 1, ‖lam k‖ ≤ B) (hd₃ : ∀ k ≤ 1, ‖â k - lam k‖ ≤ d₃)
    (hℓ : ‖ℓ‖ ≤ E) (hd₂ : ‖e - ℓ‖ ≤ d₂) :
    ‖(∏ r, conjIf (cs r) (a (κ r))) - (∏ r, conjIf (cs r) (â (κ r))) -
        ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
          conjIf (cs r₁) ℓ * ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (lam (κ r))‖ ≤
      p * d * B ^ (p - 1) + (d₂ * B ^ (p - 1) + p * (E * d₃ * B ^ (p - 2))) := by
  have hκ3 : ∀ r, κ r ≤ 3 := fun r =>
    hκ ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  set â' : ℕ → ℂ := fun k => â k + if k = 2 then e else 0 with hâ'def
  have hâ'B : ∀ r, ‖â' (κ r)‖ ≤ B := by
    intro r
    simp only [hâ'def]
    split_ifs with h
    · rw [h]; exact hâ'
    · rw [add_zero]; exact hâ _ (hκ3 r)
  have hd : 0 ≤ d := (norm_nonneg _).trans (had 0 (by norm_num))
  have hd₃0 : 0 ≤ d₃ := (norm_nonneg _).trans (hd₃ 0 (by norm_num))
  have hd₂0 : 0 ≤ d₂ := (norm_nonneg _).trans hd₂
  -- the part `∏ c(a) − ∏ c(â')`
  have hX : ‖(∏ r, conjIf (cs r) (a (κ r))) - ∏ r, conjIf (cs r) (â' (κ r))‖ ≤
      p * d * B ^ (p - 1) := by
    have h := hatAvg_prod_sub Finset.univ (fun r => conjIf (cs r) (a (κ r)))
      (fun r => conjIf (cs r) (â' (κ r))) (fun _ => B) (fun _ => d) (fun _ _ => hB)
      (fun r _ => by rw [hatAvg_norm_conjIf]; exact ha _ (hκ3 r))
      (fun r _ => by rw [hatAvg_norm_conjIf]; exact hâ'B r)
      (fun r _ => by rw [← hatAvg_conjIf_sub, hatAvg_norm_conjIf]; exact had _ (hκ3 r))
    refine h.trans (le_of_eq ?_)
    simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
    ring
  -- the part `∏ c(â') − ∏ c(â) − (leading part)`
  have hY : ‖(∏ r, conjIf (cs r) (â' (κ r))) - (∏ r, conjIf (cs r) (â (κ r))) -
      ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        conjIf (cs r₁) ℓ * ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (lam (κ r))‖ ≤
      d₂ * B ^ (p - 1) + p * (E * d₃ * B ^ (p - 2)) := by
    by_cases hex : ∃ r₁, κ r₁ = 2
    · obtain ⟨r₁, h₁⟩ := hex
      have hfil : Finset.univ.filter (fun r => κ r = 2) = {r₁} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          by_contra hr
          have := hatAvg_kappa_le hκ h₁ hr
          omega
        · rintro rfl; exact h₁
      rw [hfil, Finset.sum_singleton]
      have hrest : ∀ r ∈ Finset.univ.erase r₁, â' (κ r) = â (κ r) := by
        intro r hr
        have hle := hatAvg_kappa_le hκ h₁ (Finset.ne_of_mem_erase hr)
        simp only [hâ'def, show κ r ≠ 2 by omega, ↓reduceIte, add_zero]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r₁),
        ← Finset.mul_prod_erase _ (fun r => conjIf (cs r) (â (κ r))) (Finset.mem_univ r₁),
        Finset.prod_congr rfl fun r hr => by rw [hrest r hr]]
      simp only [hâ'def, h₁, ↓reduceIte, hatAvg_conjIf_add]
      set Pa := ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (â (κ r)) with hPa
      set Pl := ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (lam (κ r)) with hPl
      have e1 : (conjIf (cs r₁) (â 2) + conjIf (cs r₁) e) * Pa - conjIf (cs r₁) (â 2) * Pa -
          conjIf (cs r₁) ℓ * Pl = conjIf (cs r₁) (e - ℓ) * Pa + conjIf (cs r₁) ℓ * (Pa - Pl) := by
        rw [hatAvg_conjIf_sub]; ring
      rw [e1]
      have hcard : (Finset.univ.erase r₁).card = p - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have hPa' : ‖Pa‖ ≤ B ^ (p - 1) := by
        rw [hPa, norm_prod, ← hcard, ← Finset.prod_const]
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r hr => ?_
        rw [hatAvg_norm_conjIf]
        exact hâ _ (hκ3 r)
      have hdiff : ‖Pa - Pl‖ ≤ p * (d₃ * B ^ (p - 2)) := by
        have h := hatAvg_prod_sub (Finset.univ.erase r₁) (fun r => conjIf (cs r) (â (κ r)))
          (fun r => conjIf (cs r) (lam (κ r))) (fun _ => B) (fun _ => d₃) (fun _ _ => hB)
          (fun r _ => by rw [hatAvg_norm_conjIf]; exact hâ _ (hκ3 r))
          (fun r hr => by
            rw [hatAvg_norm_conjIf]
            exact hlam _ (hatAvg_kappa_le hκ h₁ (Finset.ne_of_mem_erase hr)))
          (fun r hr => by
            rw [← hatAvg_conjIf_sub, hatAvg_norm_conjIf]
            exact hd₃ _ (hatAvg_kappa_le hκ h₁ (Finset.ne_of_mem_erase hr)))
        refine h.trans ?_
        have e2 : ∀ r ∈ Finset.univ.erase r₁,
            d₃ * ∏ r' ∈ (Finset.univ.erase r₁).erase r, (fun _ => B) r' = d₃ * B ^ (p - 2) := by
          intro r hr
          rw [Finset.prod_const, Finset.card_erase_of_mem hr, hcard]
          congr 2
        rw [Finset.sum_congr rfl e2, Finset.sum_const, hcard, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
        exact this
      calc ‖conjIf (cs r₁) (e - ℓ) * Pa + conjIf (cs r₁) ℓ * (Pa - Pl)‖
          ≤ d₂ * B ^ (p - 1) + E * (p * (d₃ * B ^ (p - 2))) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul, hatAvg_norm_conjIf]
              exact mul_le_mul hd₂ hPa' (norm_nonneg _) hd₂0
            · rw [norm_mul, hatAvg_norm_conjIf]
              exact mul_le_mul hℓ hdiff (norm_nonneg _) hE
        _ = d₂ * B ^ (p - 1) + p * (E * d₃ * B ^ (p - 2)) := by ring
    · simp only [not_exists] at hex
      have hfil : Finset.univ.filter (fun r => κ r = 2) = ∅ := by
        ext r; simp [hex r]
      have heq : ∀ r, â' (κ r) = â (κ r) := fun r => by
        simp only [hâ'def, hex r, ↓reduceIte, add_zero]
      simp only [hfil, Finset.sum_empty, heq, sub_self, norm_zero]
      positivity
  have e0 : (∏ r, conjIf (cs r) (a (κ r))) - (∏ r, conjIf (cs r) (â (κ r))) -
      ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        conjIf (cs r₁) ℓ * ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (lam (κ r)) =
      ((∏ r, conjIf (cs r) (a (κ r))) - ∏ r, conjIf (cs r) (â' (κ r))) +
        ((∏ r, conjIf (cs r) (â' (κ r))) - (∏ r, conjIf (cs r) (â (κ r))) -
          ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
            conjIf (cs r₁) ℓ * ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (lam (κ r))) := by ring
  rw [e0]
  exact (norm_add_le _ _).trans (add_le_add hX hY)

/-! ## The pointwise bound of `f_3(a) − f_3(â)` minus its leading part on the a priori event -/

/-- `|â_{k+1}| ≤ 2^{k+1} 8 b² K^k` when `|G_{st}| ≤ K` and the entries `G_{νi}`, `G_{iν}`,
`G_{νμ}`, `G_{μν}`, `ν ≠ μ`, are at most `b` ((wt_A_estimate) at `ν ≠ μ`). -/
private theorem hatAvg_hat_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b K : ℝ}
    (hK : 0 ≤ K) (hGK : ∀ s t, ‖G Sig A z s t‖ ≤ K)
    (hoff : ∀ ν, ν ≠ μ → ‖G Sig A z (Sum.inr ν) (Sum.inl i)‖ ≤ b ∧
      ‖G Sig A z (Sum.inl i) (Sum.inr ν)‖ ≤ b ∧ ‖G Sig A z (Sum.inr ν) (Sum.inr μ)‖ ≤ b ∧
      ‖G Sig A z (Sum.inr μ) (Sum.inr ν)‖ ≤ b) (k : ℕ) :
    ‖avgCoeffHat Sig A z i μ (k + 1)‖ ≤ 2 ^ (k + 1) * (8 * b ^ 2 * K ^ k) := by
  unfold avgCoeffHat
  refine hatAvg_avg_le (by positivity) fun ν hν => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hoff ν hν
  rw [resCoeff_eq_sum_wordA hSig A hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hw : ∀ w : Word (k + 1), ‖wordA Sig A z (eI (Sum.inr ν)) i μ (k + 1) w‖ ≤
      8 * b ^ 2 * K ^ k := by
    intro w
    refine (wordA_le_R A z _ i μ hK (fun _ _ => hGK _ _) k w).trans ?_
    rw [hatAvg_vbar_inr, ent_eI_eI, ent_eI_eI, ent_eI_eI, ent_eI_eI]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hK k)
    have e1 := add_le_add h1 h2
    have e2 := add_le_add h3 h4
    have e1' := pow_le_pow_left₀ (by positivity) e1 2
    have e2' := pow_le_pow_left₀ (by positivity) e2 2
    have e3 : (b + b) ^ 2 + (b + b) ^ 2 = 8 * b ^ 2 := by ring
    linarith
  calc ‖∑ w : Word (k + 1), wordA Sig A z (eI (Sum.inr ν)) i μ (k + 1) w‖
      ≤ ∑ _w : Word (k + 1), 8 * b ^ 2 * K ^ k :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => hw w)
    _ = 2 ^ (k + 1) * (8 * b ^ 2 * K ^ k) := by simp

/-- `N⁻¹ ∑ f − (N⁻¹ ∑ g + c N⁻¹ ∑ h) = N⁻¹ ∑ (f − g − c h)` over `ν ≠ μ`. -/
private theorem hatAvg_avg_comb (μ : Fin N) (c : ℂ) (f g h : Fin N → ℂ) :
    (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, f ν -
        ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, g ν +
          c * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, h ν)) =
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, (f ν - g ν - c * h ν) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `N⁻¹ ∑ f − c N⁻¹ ∑ h = N⁻¹ ∑ (f − c h)` over `ν ≠ μ`. -/
private theorem hatAvg_avg_comb' (μ : Fin N) (c : ℂ) (f h : Fin N → ℂ) :
    (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, f ν -
        c * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, h ν) =
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, (f ν - c * h ν) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `|â_0| ≤ F̃ + N⁻¹ |G_μμ − m|`. -/
private theorem hatAvg_hat0_le (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {b : ℝ}
    (hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b) :
    ‖avgCoeffHat Sig A z i μ 0‖ ≤ Ft Sig A z + (N : ℝ)⁻¹ * b := by
  have hN1 : 1 ≤ N := Fin.pos μ
  have h := hatAvg_avg_sub Sig A z i μ 0
  rw [avgCoeff_zero Sig A z i μ hN1, hatAvg_resCoeff_zero] at h
  have e : avgCoeffHat Sig A z i μ 0 = (mN Sig A z - mFun N (specOf Sig) z) -
      (N : ℂ)⁻¹ * (G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z) := by
    rw [← h]; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hgm (by positivity)

/-- `|â_0 − λ_0| ≤ L² b³` on the a priori event. -/
private theorem hatAvg_lam0_sub {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b L : ℝ}
    (hb0 : 0 ≤ b) (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖)
    (hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b) :
    ‖avgCoeffHat Sig A z i μ 0 - hatAvg_lam Sig A z i μ (fun j => A j μ) 0‖ ≤ L ^ 2 * b ^ 3 := by
  have e : avgCoeffHat Sig A z i μ 0 - hatAvg_lam Sig A z i μ (fun j => A j μ) 0 =
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        ((resCoeff Sig A z (eI (Sum.inr ν)) i μ 0 -
          (Gmu Sig A z μ (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z)) -
          mFun N (specOf Sig) z * (hatAvg_al Sig A z μ ν (fun j => A j μ) *
            hatAvg_be Sig A z μ ν (fun j => A j μ))) := by
    simp only [hatAvg_lam, ↓reduceIte, avgCoeffHat, hatAvg_Sh, hatAvg_q]
    exact hatAvg_avg_comb μ _ _ _ _
  rw [e]
  refine hatAvg_avg_le (by positivity) fun ν hν => ?_
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  obtain ⟨h1, h2⟩ := hatAvg_form_event hSig A hz μ hG hμ _ hne
  rw [hatAvg_resCoeff_zero, hatAvg_term0 hSig A hz hν, norm_mul, norm_mul]
  calc _ ≤ b * (L * b * (L * b)) :=
        mul_le_mul hgm (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity) hb0
    _ = L ^ 2 * b ^ 3 := by ring

/-- On the a priori event: `|G^{(μ)}_{νi}|, |G^{(μ)}_{iν}| ≤ (1 + L) b` for `ν ≠ μ`. -/
private theorem hatAvg_Gmu_off {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b L : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) {ν : Fin N} (hν : ν ≠ μ) :
    ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i)‖ ≤ (1 + L) * b ∧
      ‖Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤ (1 + L) * b := by
  have hminor := minor_entry_bound hSig A hz μ hb0 hb1 hL hG hμ
  have hie : (Sum.inl i : Fin M ⊕ Fin N) ≠ Sum.inr μ := Sum.inl_ne_inr
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  have h1 := hminor _ _ hne hie
  have h2 := hminor _ _ hie hne
  have e1 : PiZ N Sig z (Sum.inr ν) (Sum.inl i) = 0 := by simp [PiZ, piMat]
  have e2 : PiZ N Sig z (Sum.inl i) (Sum.inr ν) = 0 := by simp [PiZ, piMat]
  rw [e1, sub_zero] at h1
  rw [e2, sub_zero] at h2
  exact ⟨h1, h2⟩

/-- `|L| ≤ 2 (1 + L) L b²` on the a priori event. -/
private theorem hatAvg_Lf_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b L : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) :
    ‖hatAvg_Lf Sig A z i μ (fun j => A j μ)‖ ≤ 2 * (1 + L) * L * b ^ 2 := by
  unfold hatAvg_Lf
  refine hatAvg_avg_le (by positivity) fun ν hν => ?_
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  obtain ⟨h1, h2⟩ := hatAvg_form_event hSig A hz μ hG hμ _ hne
  obtain ⟨h3, h4⟩ := hatAvg_Gmu_off hSig A hz i μ hb0 hb1 hL hG hμ hν
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc _ ≤ (1 + L) * b * (L * b) + L * b * ((1 + L) * b) :=
        add_le_add (mul_le_mul h3 h2 (norm_nonneg _) (by positivity))
          (mul_le_mul h1 h4 (norm_nonneg _) (by positivity))
    _ = 2 * (1 + L) * L * b ^ 2 := by ring

/-- `|â_1 − λ_1| ≤ (2 (1 + L) L + 2 L) b³` on the a priori event. -/
private theorem hatAvg_lam1_sub {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b L : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖)
    (hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b) :
    ‖avgCoeffHat Sig A z i μ 1 - hatAvg_lam Sig A z i μ (fun j => A j μ) 1‖ ≤
      (2 * (1 + L) * L + 2 * L) * b ^ 3 := by
  have e : avgCoeffHat Sig A z i μ 1 - hatAvg_lam Sig A z i μ (fun j => A j μ) 1 =
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        (resCoeff Sig A z (eI (Sum.inr ν)) i μ 1 - mFun N (specOf Sig) z *
          (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * hatAvg_be Sig A z μ ν (fun j => A j μ) +
            hatAvg_al Sig A z μ ν (fun j => A j μ) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν))) := by
    simp only [hatAvg_lam, one_ne_zero, ↓reduceIte, avgCoeffHat, hatAvg_Lf]
    exact hatAvg_avg_comb' μ _ _ _
  rw [e]
  refine hatAvg_avg_le (by positivity) fun ν hν => ?_
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  rw [hatAvg_term1 hSig A hz i hν]
  obtain ⟨h1, h2⟩ := hatAvg_form_event hSig A hz μ hG hμ _ hne
  obtain ⟨h3, h4⟩ := hatAvg_Gmu_off hSig A hz i μ hb0 hb1 hL hG hμ hν
  have hoff0 : ∀ s t, PiZ N Sig z s t = 0 → ‖G Sig A z s t‖ ≤ b := fun s t h => by
    simpa [h] using hG s t
  have h7 := hoff0 (Sum.inr ν) (Sum.inr μ) (by simp [PiZ, piMat, hν])
  have h8 := hoff0 (Sum.inr μ) (Sum.inr ν) (by simp [PiZ, piMat, Ne.symm hν])
  have him := hoff0 (Sum.inl i) (Sum.inr μ) (by simp [PiZ, piMat])
  have hmi := hoff0 (Sum.inr μ) (Sum.inl i) (by simp [PiZ, piMat])
  have hA : ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * hatAvg_be Sig A z μ ν (fun j => A j μ) +
      hatAvg_al Sig A z μ ν (fun j => A j μ) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤
      2 * (1 + L) * L * b ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc _ ≤ (1 + L) * b * (L * b) + L * b * ((1 + L) * b) :=
          add_le_add (mul_le_mul h3 h2 (norm_nonneg _) (by positivity))
            (mul_le_mul h1 h4 (norm_nonneg _) (by positivity))
      _ = 2 * (1 + L) * L * b ^ 2 := by ring
  have hB2 : ‖G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inl i) *
        hatAvg_be Sig A z μ ν (fun j => A j μ) +
      hatAvg_al Sig A z μ ν (fun j => A j μ) * G Sig A z (Sum.inl i) (Sum.inr μ) *
        G Sig A z (Sum.inr μ) (Sum.inr ν)‖ ≤ 2 * L * b ^ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc _ ≤ b * b * (L * b) + L * b * b * b :=
          add_le_add (mul_le_mul (mul_le_mul h7 hmi (norm_nonneg _) hb0) h2 (norm_nonneg _)
            (by positivity))
            (mul_le_mul (mul_le_mul h1 him (norm_nonneg _) (by positivity)) h8 (norm_nonneg _)
              (by positivity))
      _ = 2 * L * b ^ 3 := by ring
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  calc _ ≤ b * (2 * (1 + L) * L * b ^ 2) + 2 * L * b ^ 3 :=
        add_le_add (mul_le_mul hgm hA (norm_nonneg _) hb0) hB2
    _ = (2 * (1 + L) * L + 2 * L) * b ^ 3 := by ring

/-- `|N⁻¹ G_μμ G_{ii} G_μμ − ℓ| ≤ N⁻¹ ((K + C_m)(K + L) + K) b`, `K = K_Π + 1`, on the a priori
event. -/
private theorem hatAvg_e_sub {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N)
    {b L Cm KP : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L) (hCm : 0 ≤ Cm)
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ KP + 1 + L ∧
    ‖(N : ℂ)⁻¹ * (G Sig A z (Sum.inr μ) (Sum.inr μ) * G Sig A z (Sum.inl i) (Sum.inl i) *
        G Sig A z (Sum.inr μ) (Sum.inr μ)) - hatAvg_ell Sig A z i μ‖ ≤
      (N : ℝ)⁻¹ * (((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * b) := by
  have hNi0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hGK : ∀ s t, ‖G Sig A z s t‖ ≤ KP + 1 := by
    intro s t
    have h1 : ‖G Sig A z s t‖ ≤ ‖G Sig A z s t - PiZ N Sig z s t‖ + ‖PiZ N Sig z s t‖ := by
      have := norm_add_le (G Sig A z s t - PiZ N Sig z s t) (PiZ N Sig z s t)
      rwa [sub_add_cancel] at this
    linarith [hG s t, hPi s t]
  have hK0 : 0 ≤ KP + 1 := (norm_nonneg _).trans (hGK (Sum.inl i) (Sum.inl i))
  have hie : (Sum.inl i : Fin M ⊕ Fin N) ≠ Sum.inr μ := Sum.inl_ne_inr
  have hGmuii : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ KP + 1 + L := by
    have h1 := minor_entry_bound hSig A hz μ hb0 hb1 hL hG hμ _ _ hie hie
    have h2 : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤
        ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i) - PiZ N Sig z (Sum.inl i) (Sum.inl i)‖ +
          ‖PiZ N Sig z (Sum.inl i) (Sum.inl i)‖ := by
      have := norm_add_le (Gmu Sig A z μ (Sum.inl i) (Sum.inl i) -
        PiZ N Sig z (Sum.inl i) (Sum.inl i)) (PiZ N Sig z (Sum.inl i) (Sum.inl i))
      rwa [sub_add_cancel] at this
    have h3 : (1 + L) * b ≤ 1 + L := by
      have := mul_le_mul_of_nonneg_left hb1 (by linarith : (0 : ℝ) ≤ 1 + L)
      linarith
    have h4 := hPi (Sum.inl i) (Sum.inl i)
    have h5 : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i) - PiZ N Sig z (Sum.inl i) (Sum.inl i)‖ ≤
        (1 + L) * b := h1
    linarith
  refine ⟨hGmuii, ?_⟩
  have hoff0 : ∀ s t, PiZ N Sig z s t = 0 → ‖G Sig A z s t‖ ≤ b := fun s t h => by
    simpa [h] using hG s t
  have him := hoff0 (Sum.inl i) (Sum.inr μ) (by simp [PiZ, piMat])
  have hmi := hoff0 (Sum.inr μ) (Sum.inl i) (by simp [PiZ, piMat])
  have hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b := by
    have := hG (Sum.inr μ) (Sum.inr μ); simpa [PiZ, piMat] using this
  unfold hatAvg_ell
  rw [← mul_sub, hatAvg_term2 hSig A hz i μ, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hNi0
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hgpm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) + mFun N (specOf Sig) z‖ ≤ KP + 1 + Cm :=
    (norm_add_le _ _).trans (add_le_add (hGK _ _) hm)
  calc _ ≤ b * (KP + 1 + Cm) * (KP + 1 + L) + (KP + 1) * b * b :=
        add_le_add (mul_le_mul (mul_le_mul hgm hgpm (norm_nonneg _) hb0) hGmuii (norm_nonneg _)
          (by positivity)) (mul_le_mul (mul_le_mul (hGK _ _) him (norm_nonneg _) hK0) hmi
            (norm_nonneg _) (by positivity))
    _ ≤ b * (KP + 1 + Cm) * (KP + 1 + L) + (KP + 1) * b * 1 := by gcongr
    _ = ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * b := by ring

/-- The constant `C_B` of the factor bound `|a_k|, |â_k|, |λ_k| ≤ C_B (F̃ + b²)`. -/
private def hatAvg_CB (L Cm KP c₂ : ℝ) : ℝ :=
  1 + c₂ ^ 2 + L ^ 2 + 64 * (KP + 1) ^ 2 + c₂ ^ 2 * (8 * (KP + 1) ^ 5 + (KP + 1) ^ 3) +
    2 * Cm * (1 + L) * L

/-- The constant of the pointwise bound of `f_3(a) − f_3(â)` minus its leading part. -/
private def hatAvg_K0 (p : ℕ) (L Cm KP c₂ : ℝ) : ℝ :=
  4 ^ p * ((8 * p * (KP + 1) ^ 5 * c₂ + ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * c₂ +
    p * c₂ * ((KP + 1) ^ 3 + Cm ^ 2 * (KP + 1 + L)) * (2 * (1 + L) * L + 2 * L + L ^ 2)) *
      hatAvg_CB L Cm KP c₂ ^ p)

/-- The exponent count of one shape: with `N⁻¹ = ε²`, `ε ≤ c₂ b` and `b² ≤ W`, the bound of
`hatAvg_kappa` is at most `ε (8 p K⁵ c₂ + C₂ c₂ + p c₂ E' C₃) C_B^p W^p`. -/
private theorem hatAvg_arith {p : ℕ} (hp : 2 ≤ p) {ε b W CB K C₂ E' C₃ c₂ : ℝ}
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hbW : b ^ 2 ≤ W) (hCB : 1 ≤ CB) (hK : 0 ≤ K) (hC₂ : 0 ≤ C₂)
    (hE' : 0 ≤ E') (hC₃ : 0 ≤ C₃) (hc₂ : 0 ≤ c₂) (hεb : ε ≤ c₂ * b) :
    p * (ε ^ 2 * (8 * K ^ 5 * b)) * (CB * W) ^ (p - 1) +
      ((ε ^ 2 * (C₂ * b)) * (CB * W) ^ (p - 1) +
        p * ((ε ^ 2 * E') * (C₃ * b ^ 3) * (CB * W) ^ (p - 2))) ≤
      ε * ((8 * p * K ^ 5 * c₂ + C₂ * c₂ + p * c₂ * E' * C₃) * CB ^ p * W ^ p) := by
  have hW : 0 ≤ W := (sq_nonneg b).trans hbW
  have hCB0 : 0 ≤ CB := zero_le_one.trans hCB
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hεb' : ε * b ≤ c₂ * W := by
    calc ε * b ≤ c₂ * b * b := mul_le_mul_of_nonneg_right hεb hb
      _ = c₂ * b ^ 2 := by ring
      _ ≤ c₂ * W := mul_le_mul_of_nonneg_left hbW hc₂
  have h1 : ε ^ 2 * b ≤ ε * (c₂ * W) := by
    calc ε ^ 2 * b = ε * (ε * b) := by ring
      _ ≤ ε * (c₂ * W) := mul_le_mul_of_nonneg_left hεb' hε
  have h3 : ε ^ 2 * b ^ 3 ≤ ε * (c₂ * W ^ 2) := by
    calc ε ^ 2 * b ^ 3 = ε * ((ε * b) * b ^ 2) := by ring
      _ ≤ ε * ((c₂ * W) * W) := by
          refine mul_le_mul_of_nonneg_left ?_ hε
          exact mul_le_mul hεb' hbW (sq_nonneg _) (by positivity)
      _ = ε * (c₂ * W ^ 2) := by ring
  have hP1 : (CB * W) ^ (p - 1) ≤ CB ^ p * W ^ (p - 1) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCB (by omega)) (pow_nonneg hW _)
  have hP2 : (CB * W) ^ (p - 2) ≤ CB ^ p * W ^ (p - 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCB (by omega)) (pow_nonneg hW _)
  have hW1 : W * W ^ (p - 1) = W ^ p := by
    rw [← pow_succ']; congr 1; omega
  have hW2 : W ^ 2 * W ^ (p - 2) = W ^ p := by
    rw [← pow_add]; congr 1; omega
  have t1 : p * (ε ^ 2 * (8 * K ^ 5 * b)) * (CB * W) ^ (p - 1) ≤
      ε * (8 * p * K ^ 5 * c₂ * CB ^ p * W ^ p) := by
    calc p * (ε ^ 2 * (8 * K ^ 5 * b)) * (CB * W) ^ (p - 1)
        = p * (8 * K ^ 5) * (ε ^ 2 * b) * (CB * W) ^ (p - 1) := by ring
      _ ≤ p * (8 * K ^ 5) * (ε * (c₂ * W)) * (CB ^ p * W ^ (p - 1)) := by gcongr
      _ = ε * (8 * p * K ^ 5 * c₂ * CB ^ p * (W * W ^ (p - 1))) := by ring
      _ = ε * (8 * p * K ^ 5 * c₂ * CB ^ p * W ^ p) := by rw [hW1]
  have t2 : (ε ^ 2 * (C₂ * b)) * (CB * W) ^ (p - 1) ≤ ε * (C₂ * c₂ * CB ^ p * W ^ p) := by
    calc (ε ^ 2 * (C₂ * b)) * (CB * W) ^ (p - 1) = C₂ * (ε ^ 2 * b) * (CB * W) ^ (p - 1) := by
          ring
      _ ≤ C₂ * (ε * (c₂ * W)) * (CB ^ p * W ^ (p - 1)) := by gcongr
      _ = ε * (C₂ * c₂ * CB ^ p * (W * W ^ (p - 1))) := by ring
      _ = ε * (C₂ * c₂ * CB ^ p * W ^ p) := by rw [hW1]
  have t3 : p * ((ε ^ 2 * E') * (C₃ * b ^ 3) * (CB * W) ^ (p - 2)) ≤
      ε * (p * c₂ * E' * C₃ * CB ^ p * W ^ p) := by
    calc p * ((ε ^ 2 * E') * (C₃ * b ^ 3) * (CB * W) ^ (p - 2))
        = p * E' * C₃ * (ε ^ 2 * b ^ 3) * (CB * W) ^ (p - 2) := by ring
      _ ≤ p * E' * C₃ * (ε * (c₂ * W ^ 2)) * (CB ^ p * W ^ (p - 2)) := by gcongr
      _ = ε * (p * c₂ * E' * C₃ * CB ^ p * (W ^ 2 * W ^ (p - 2))) := by ring
      _ = ε * (p * c₂ * E' * C₃ * CB ^ p * W ^ p) := by rw [hW2]
  calc _ ≤ ε * (8 * p * K ^ 5 * c₂ * CB ^ p * W ^ p) +
        (ε * (C₂ * c₂ * CB ^ p * W ^ p) + ε * (p * c₂ * E' * C₃ * CB ^ p * W ^ p)) :=
        add_le_add t1 (add_le_add t2 t3)
    _ = _ := by ring

/-- On the a priori event `|G_{st} − Π_{st}| ≤ b ≤ 1`, with `1 ≤ L |G_μμ|`, `|m| ≤ C_m`,
`|Π_{st}| ≤ K_Π` and `N^{−1/2} ≤ c₂ b`:
`|f_3(a) − f_3(â) − (leading part)| ≤ N^{−1/2} K₀ (F̃ + b²)^p`. -/
private theorem hatAvg_point {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {p : ℕ}
    (hp : 2 ≤ p) {b₀ L Cm KP c₂ : ℝ} (hb₀1 : b₀ ≤ 1) (hL : 0 ≤ L) (hCm : 0 ≤ Cm)
    (hKP : 0 ≤ KP) (hc₂ : 0 ≤ c₂) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b₀)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) (hNb : (Real.sqrt N)⁻¹ ≤ c₂ * b₀) :
    ‖(fCoeff p (avgCoeff Sig A z i μ) 3 - fCoeff p (avgCoeffHat Sig A z i μ) 3) -
        hatAvg_Lead Sig A z i μ p (fun j => A j μ)‖ ≤
      (Real.sqrt N)⁻¹ * (hatAvg_K0 p L Cm KP c₂ * (Ft Sig A z + b₀ ^ 2) ^ p) := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb₀ : 0 ≤ b₀ := (norm_nonneg _).trans (hG (Sum.inr μ) (Sum.inr μ))
  set ε := (Real.sqrt N)⁻¹ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hNε : (N : ℝ)⁻¹ = ε ^ 2 := by
    rw [hεdef, inv_pow, Real.sq_sqrt hNr.le]
  have hNi : (N : ℝ)⁻¹ ≤ c₂ ^ 2 * b₀ ^ 2 := by
    rw [hNε, ← mul_pow]; exact pow_le_pow_left₀ hε0 hNb 2
  have hNi0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  set K := KP + 1 with hKdef
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ) with hg
  set W := Ft Sig A z + b₀ ^ 2 with hWdef
  have hF0 : 0 ≤ Ft Sig A z := norm_nonneg _
  have hW0 : 0 ≤ W := by positivity
  have hbW : b₀ ^ 2 ≤ W := by rw [hWdef]; linarith
  -- the entries of `G`
  have hGK : ∀ s t, ‖G Sig A z s t‖ ≤ K := by
    intro s t
    have h1 : ‖G Sig A z s t‖ ≤ ‖G Sig A z s t - PiZ N Sig z s t‖ + ‖PiZ N Sig z s t‖ := by
      have := norm_add_le (G Sig A z s t - PiZ N Sig z s t) (PiZ N Sig z s t)
      rwa [sub_add_cancel] at this
    linarith [hG s t, hPi s t]
  have hoff0 : ∀ s t, PiZ N Sig z s t = 0 → ‖G Sig A z s t‖ ≤ b₀ := fun s t h => by
    simpa [h] using hG s t
  have hoff : ∀ ν, ν ≠ μ → ‖G Sig A z (Sum.inr ν) (Sum.inl i)‖ ≤ b₀ ∧
      ‖G Sig A z (Sum.inl i) (Sum.inr ν)‖ ≤ b₀ ∧ ‖G Sig A z (Sum.inr ν) (Sum.inr μ)‖ ≤ b₀ ∧
      ‖G Sig A z (Sum.inr μ) (Sum.inr ν)‖ ≤ b₀ := fun ν hν =>
    ⟨hoff0 _ _ (by simp [PiZ, piMat]), hoff0 _ _ (by simp [PiZ, piMat]),
      hoff0 _ _ (by simp [PiZ, piMat, hν]), hoff0 _ _ (by simp [PiZ, piMat, Ne.symm hν])⟩
  have him := hoff0 (Sum.inl i) (Sum.inr μ) (by simp [PiZ, piMat])
  have hmi := hoff0 (Sum.inr μ) (Sum.inl i) (by simp [PiZ, piMat])
  have hgm : ‖g - mFun N (specOf Sig) z‖ ≤ b₀ := by
    have := hG (Sum.inr μ) (Sum.inr μ); simpa [PiZ, piMat, hg] using this
  -- the coefficients
  have hres := hatAvg_resCoeff_mu hSig A hz i μ hK1 hb₀ hb₀1 (hGK _ _) (hGK _ _) him hmi hgm
  have hggg : ‖g * G Sig A z (Sum.inl i) (Sum.inl i) * g‖ ≤ K ^ 3 := by
    rw [norm_mul, norm_mul]
    calc ‖g‖ * ‖G Sig A z (Sum.inl i) (Sum.inl i)‖ * ‖g‖ ≤ K * K * K :=
          mul_le_mul (mul_le_mul (hGK _ _) (hGK _ _) (norm_nonneg _) hK0) (hGK _ _)
            (norm_nonneg _) (by positivity)
      _ = K ^ 3 := by ring
  have hresle : ∀ k ≤ 3, ‖resCoeff Sig A z (eI (Sum.inr μ)) i μ k‖ ≤ 8 * K ^ 5 * b₀ + K ^ 3 := by
    intro k hk
    have h2 : ‖(if k = 2 then g * G Sig A z (Sum.inl i) (Sum.inl i) * g else 0)‖ ≤ K ^ 3 := by
      split_ifs
      · exact hggg
      · simp only [norm_zero]; positivity
    have := norm_add_le (resCoeff Sig A z (eI (Sum.inr μ)) i μ k -
      (if k = 2 then g * G Sig A z (Sum.inl i) (Sum.inl i) * g else 0))
      (if k = 2 then g * G Sig A z (Sum.inl i) (Sum.inl i) * g else 0)
    rw [sub_add_cancel] at this
    linarith [hres k hk]
  have hhat3 : ∀ k, 1 ≤ k → k ≤ 3 → ‖avgCoeffHat Sig A z i μ k‖ ≤ 64 * K ^ 2 * b₀ ^ 2 := by
    intro k hk1 hk3
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (hatAvg_hat_le hSig A hz i μ hK0 hGK hoff k').trans ?_
    have h2 : (2 : ℝ) ^ (k' + 1) ≤ 8 := by
      calc (2 : ℝ) ^ (k' + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 8 := by norm_num
    have hK2 : K ^ k' ≤ K ^ 2 := pow_le_pow_right₀ hK1 (by omega)
    calc 2 ^ (k' + 1) * (8 * b₀ ^ 2 * K ^ k') ≤ 8 * (8 * b₀ ^ 2 * K ^ 2) :=
          mul_le_mul h2 (by gcongr) (by positivity) (by norm_num)
      _ = 64 * K ^ 2 * b₀ ^ 2 := by ring
  have hhat0 := hatAvg_hat0_le Sig A z i μ hgm
  have hlam0 := hatAvg_lam0_sub hSig A hz i μ hb₀ hL hG hμ hgm
  have hLf := hatAvg_Lf_le hSig A hz i μ hb₀ hb₀1 hL hG hμ
  have hlam1 := hatAvg_lam1_sub hSig A hz i μ hb₀ hb₀1 hL hG hμ hgm
  obtain ⟨hGmuii, hesub⟩ := hatAvg_e_sub hSig A hz i μ hb₀ hb₀1 hL hCm hG hμ hm hPi
  -- the constant `C_B`
  set CB := hatAvg_CB L Cm KP c₂ with hCB
  have hc₅ : 0 ≤ c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) := by positivity
  have hc₆ : 0 ≤ 2 * Cm * (1 + L) * L := by positivity
  have hCBe : CB = 1 + c₂ ^ 2 + L ^ 2 + 64 * K ^ 2 + c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) +
      2 * Cm * (1 + L) * L := by rw [hCB, hatAvg_CB]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hc2 : 0 ≤ c₂ ^ 2 := sq_nonneg c₂
  have hK2 : 0 ≤ 64 * K ^ 2 := by positivity
  have hCB1 : 1 ≤ CB := by rw [hCBe]; linarith
  have hNb₀ : (N : ℝ)⁻¹ * b₀ ≤ c₂ ^ 2 * b₀ ^ 2 := by
    calc (N : ℝ)⁻¹ * b₀ ≤ (N : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hb₀1 hNi0
      _ ≤ c₂ ^ 2 * b₀ ^ 2 := by rw [mul_one]; exact hNi
  have hc2W : c₂ ^ 2 * b₀ ^ 2 ≤ c₂ ^ 2 * W := mul_le_mul_of_nonneg_left hbW hc2
  have hc2F : 0 ≤ c₂ ^ 2 * Ft Sig A z := mul_nonneg hc2 hF0
  have hWe : (1 + c₂ ^ 2) * W = Ft Sig A z + b₀ ^ 2 + c₂ ^ 2 * W := by rw [hWdef]; ring
  have hhat0B : ‖avgCoeffHat Sig A z i μ 0‖ ≤ (1 + c₂ ^ 2) * W := by
    have hb2 : 0 ≤ b₀ ^ 2 := sq_nonneg _
    linarith
  have hK2W : 64 * K ^ 2 * b₀ ^ 2 ≤ 64 * K ^ 2 * W := mul_le_mul_of_nonneg_left hbW hK2
  have hâB : ∀ k ≤ 3, ‖avgCoeffHat Sig A z i μ k‖ ≤ CB * W := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · refine hhat0B.trans (mul_le_mul_of_nonneg_right ?_ hW0)
      rw [hCBe]; linarith
    · refine (hhat3 k hk1 hk).trans (hK2W.trans (mul_le_mul_of_nonneg_right ?_ hW0))
      rw [hCBe]; linarith
  have hNres : ∀ k ≤ 3, (N : ℝ)⁻¹ * ‖resCoeff Sig A z (eI (Sum.inr μ)) i μ k‖ ≤
      c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W := by
    intro k hk
    have h := hresle k hk
    have hK5 : 0 ≤ K ^ 5 := by positivity
    have hK3 : 0 ≤ K ^ 3 := by positivity
    have hb8 : 8 * K ^ 5 * b₀ + K ^ 3 ≤ 8 * K ^ 5 + K ^ 3 := by
      have := mul_le_mul_of_nonneg_left hb₀1 (by positivity : (0 : ℝ) ≤ 8 * K ^ 5)
      linarith
    calc (N : ℝ)⁻¹ * ‖resCoeff Sig A z (eI (Sum.inr μ)) i μ k‖
        ≤ (c₂ ^ 2 * b₀ ^ 2) * (8 * K ^ 5 + K ^ 3) :=
          mul_le_mul hNi (h.trans hb8) (norm_nonneg _) (by positivity)
      _ = (8 * K ^ 5 + K ^ 3) * (c₂ ^ 2 * b₀ ^ 2) := by ring
      _ ≤ (8 * K ^ 5 + K ^ 3) * (c₂ ^ 2 * W) := mul_le_mul_of_nonneg_left hc2W (by positivity)
      _ = c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W := by ring
  have haB : ∀ k ≤ 3, ‖avgCoeff Sig A z i μ k‖ ≤ CB * W := by
    intro k hk
    have e : avgCoeff Sig A z i μ k = avgCoeffHat Sig A z i μ k +
        (N : ℂ)⁻¹ * resCoeff Sig A z (eI (Sum.inr μ)) i μ k := by
      rw [← hatAvg_avg_sub]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h2 := hNres k hk
    have hs : ‖avgCoeffHat Sig A z i μ k‖ ≤ (1 + c₂ ^ 2 + 64 * K ^ 2) * W := by
      have e : (1 + c₂ ^ 2 + 64 * K ^ 2) * W = (1 + c₂ ^ 2) * W + 64 * K ^ 2 * W := by ring
      have h64 : 0 ≤ 64 * K ^ 2 * W := by positivity
      have h1c : 0 ≤ (1 + c₂ ^ 2) * W := by positivity
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · linarith [hhat0B]
      · have h1 := (hhat3 k hk1 hk).trans hK2W
        linarith
    have : (1 + c₂ ^ 2 + 64 * K ^ 2) * W + c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W ≤ CB * W := by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ hW0
      rw [hCBe]; linarith
    linarith
  have heB : ‖(N : ℂ)⁻¹ * (g * G Sig A z (Sum.inl i) (Sum.inl i) * g)‖ ≤ (N : ℝ)⁻¹ * K ^ 3 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hggg hNi0
  have hâ'B : ‖avgCoeffHat Sig A z i μ 2 + (N : ℂ)⁻¹ * (g * G Sig A z (Sum.inl i) (Sum.inl i) * g)‖
      ≤ CB * W := by
    refine (norm_add_le _ _).trans ?_
    have h1 := (hhat3 2 (by norm_num) (by norm_num)).trans hK2W
    have h2 : (N : ℝ)⁻¹ * K ^ 3 ≤ c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W := by
      have := hNres 0 (by norm_num)
      have hK3 : 0 ≤ K ^ 3 := by positivity
      calc (N : ℝ)⁻¹ * K ^ 3 ≤ (c₂ ^ 2 * b₀ ^ 2) * (8 * K ^ 5 + K ^ 3) :=
            mul_le_mul hNi (by have : 0 ≤ 8 * K ^ 5 := by positivity
                               linarith) hK3 (by positivity)
        _ = (8 * K ^ 5 + K ^ 3) * (c₂ ^ 2 * b₀ ^ 2) := by ring
        _ ≤ (8 * K ^ 5 + K ^ 3) * (c₂ ^ 2 * W) := mul_le_mul_of_nonneg_left hc2W (by positivity)
        _ = c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W := by ring
    have : 64 * K ^ 2 * W + c₂ ^ 2 * (8 * K ^ 5 + K ^ 3) * W ≤ CB * W := by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ hW0
      rw [hCBe]; linarith
    linarith [heB.trans h2]
  have hlamB : ∀ k ≤ 1, ‖hatAvg_lam Sig A z i μ (fun j => A j μ) k‖ ≤ CB * W := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have h := norm_sub_le_norm_sub_add_norm_sub (hatAvg_lam Sig A z i μ (fun j => A j μ) 0)
        (avgCoeffHat Sig A z i μ 0) 0
      simp only [sub_zero] at h
      rw [norm_sub_rev] at h
      have h3 : L ^ 2 * b₀ ^ 3 ≤ L ^ 2 * W := by
        refine mul_le_mul_of_nonneg_left ?_ hL2
        exact (pow_le_pow_of_le_one hb₀ hb₀1 (by norm_num : 2 ≤ 3)).trans hbW
      have : L ^ 2 * W + (1 + c₂ ^ 2) * W ≤ CB * W := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ hW0
        rw [hCBe]; linarith
      linarith
    · simp only [hatAvg_lam, one_ne_zero, ↓reduceIte]
      rw [norm_mul]
      have h1 : ‖mFun N (specOf Sig) z‖ * ‖hatAvg_Lf Sig A z i μ (fun j => A j μ)‖ ≤
          Cm * (2 * (1 + L) * L * b₀ ^ 2) := mul_le_mul hm hLf (norm_nonneg _) hCm
      have h2 : Cm * (2 * (1 + L) * L * b₀ ^ 2) ≤ 2 * Cm * (1 + L) * L * W := by
        have := mul_le_mul_of_nonneg_left hbW hc₆
        have e : Cm * (2 * (1 + L) * L * b₀ ^ 2) = 2 * Cm * (1 + L) * L * b₀ ^ 2 := by ring
        linarith
      have : 2 * Cm * (1 + L) * L * W ≤ CB * W := by
        refine mul_le_mul_of_nonneg_right ?_ hW0
        rw [hCBe]; linarith
      linarith
  have hC3 : ∀ k ≤ 1, ‖avgCoeffHat Sig A z i μ k - hatAvg_lam Sig A z i μ (fun j => A j μ) k‖ ≤
      (2 * (1 + L) * L + 2 * L + L ^ 2) * b₀ ^ 3 := by
    intro k hk
    have h3 : 0 ≤ b₀ ^ 3 := by positivity
    have hA : 0 ≤ (2 * (1 + L) * L + 2 * L) * b₀ ^ 3 := by positivity
    have hB : 0 ≤ L ^ 2 * b₀ ^ 3 := by positivity
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have e : (2 * (1 + L) * L + 2 * L + L ^ 2) * b₀ ^ 3 =
          (2 * (1 + L) * L + 2 * L) * b₀ ^ 3 + L ^ 2 * b₀ ^ 3 := by ring
      linarith
    · have e : (2 * (1 + L) * L + 2 * L + L ^ 2) * b₀ ^ 3 =
          (2 * (1 + L) * L + 2 * L) * b₀ ^ 3 + L ^ 2 * b₀ ^ 3 := by ring
      linarith
  have hd : ∀ k ≤ 3, ‖avgCoeff Sig A z i μ k - (avgCoeffHat Sig A z i μ k +
      if k = 2 then (N : ℂ)⁻¹ * (g * G Sig A z (Sum.inl i) (Sum.inl i) * g) else 0)‖ ≤
      (N : ℝ)⁻¹ * (8 * K ^ 5 * b₀) := by
    intro k hk
    have e1 : avgCoeff Sig A z i μ k - (avgCoeffHat Sig A z i μ k +
        if k = 2 then (N : ℂ)⁻¹ * (g * G Sig A z (Sum.inl i) (Sum.inl i) * g) else 0) =
        (N : ℂ)⁻¹ * (resCoeff Sig A z (eI (Sum.inr μ)) i μ k -
          (if k = 2 then g * G Sig A z (Sum.inl i) (Sum.inl i) * g else 0)) := by
      have h := hatAvg_avg_sub Sig A z i μ k
      split_ifs <;> linear_combination h
    rw [e1, norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hres k hk) hNi0
  set E' := K ^ 3 + Cm ^ 2 * (KP + 1 + L) with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hℓE : ‖hatAvg_ell Sig A z i μ‖ ≤ (N : ℝ)⁻¹ * E' := by
    unfold hatAvg_ell
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ hNi0
    have h1 : ‖mFun N (specOf Sig) z‖ ^ 2 ≤ Cm ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
    have h2 := mul_le_mul h1 hGmuii (norm_nonneg _) (sq_nonneg Cm)
    have : 0 ≤ K ^ 3 := by positivity
    linarith
  -- the sum over the shapes
  have hkap : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3,
      ‖(∏ r, conjIf (hatAvg_cs p r) (avgCoeff Sig A z i μ (κ r))) -
          (∏ r, conjIf (hatAvg_cs p r) (avgCoeffHat Sig A z i μ (κ r))) -
          ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
            conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) *
              ∏ r ∈ Finset.univ.erase r₁, conjIf (hatAvg_cs p r)
                (hatAvg_lam Sig A z i μ (fun j => A j μ) (κ r))‖ ≤
        ε * ((8 * p * K ^ 5 * c₂ + ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * c₂ +
          p * c₂ * E' * (2 * (1 + L) * L + 2 * L + L ^ 2)) * CB ^ p * W ^ p) := by
    intro κ hκ
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    have h := hatAvg_kappa (hatAvg_cs p) κ hκ (avgCoeff Sig A z i μ) (avgCoeffHat Sig A z i μ)
      (hatAvg_lam Sig A z i μ (fun j => A j μ))
      ((N : ℂ)⁻¹ * (g * G Sig A z (Sum.inl i) (Sum.inl i) * g)) (hatAvg_ell Sig A z i μ)
      (by positivity : 0 ≤ CB * W) (by positivity : 0 ≤ (N : ℝ)⁻¹ * E') haB hâB hâ'B hd hlamB
      hC3 hℓE hesub
    refine h.trans ?_
    rw [hNε]
    have := hatAvg_arith (p := p) hp hε0 hb₀ hbW hCB1 hK0
      (by positivity : 0 ≤ (KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) hE'0
      (by positivity : 0 ≤ 2 * (1 + L) * L + 2 * L + L ^ 2) hc₂ hNb
    refine le_of_le_of_eq this ?_
    rfl
  have hsum : (fCoeff p (avgCoeff Sig A z i μ) 3 - fCoeff p (avgCoeffHat Sig A z i μ) 3) -
      hatAvg_Lead Sig A z i μ p (fun j => A j μ) =
      ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3,
        ((∏ r, conjIf (hatAvg_cs p r) (avgCoeff Sig A z i μ (κ r))) -
          (∏ r, conjIf (hatAvg_cs p r) (avgCoeffHat Sig A z i μ (κ r))) -
          ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
            conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) *
              ∏ r ∈ Finset.univ.erase r₁, conjIf (hatAvg_cs p r)
                (hatAvg_lam Sig A z i μ (fun j => A j μ) (κ r))) := by
    rw [hatAvg_fCoeff_eq, hatAvg_fCoeff_eq, hatAvg_Lead, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hkap).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := hatAvg_card_T p 3
  have h4 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  rw [h4] at hcard
  have hX0 : 0 ≤ ε * ((8 * p * K ^ 5 * c₂ + ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * c₂ +
      p * c₂ * E' * (2 * (1 + L) * L + 2 * L + L ^ 2)) * CB ^ p * W ^ p) := by positivity
  calc ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) *
        (ε * ((8 * p * K ^ 5 * c₂ + ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * c₂ +
          p * c₂ * E' * (2 * (1 + L) * L + 2 * L + L ^ 2)) * CB ^ p * W ^ p))
      ≤ 4 ^ p * (ε * ((8 * p * K ^ 5 * c₂ + ((KP + 1 + Cm) * (KP + 1 + L) + (KP + 1)) * c₂ +
          p * c₂ * E' * (2 * (1 + L) * L + 2 * L + L ^ 2)) * CB ^ p * W ^ p)) :=
        mul_le_mul_of_nonneg_right hcard hX0
    _ = ε * (hatAvg_K0 p L Cm KP c₂ * W ^ p) := by
        rw [hatAvg_K0, hE', hKdef, ← hCB]; ring

/-! ## The column expectation of the leading part (A+_avg) -/

private theorem hatAvg_rpow_half (N : ℕ) : (N : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg N)]
  congr 1
  ring

/-- The coefficients of `L(y) = ∑_j ℓ_j y_j`. -/
private def hatAvg_lc (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (j : Fin M) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
    (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * Gmu Sig A z μ (Sum.inl j) (Sum.inr ν) +
      Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν))

/-- The kernel of `q(y) = ∑_{j j'} y_j Q_{j j'} y_{j'}`. -/
private def hatAvg_qk (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (j j' : Fin M) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
    Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * Gmu Sig A z μ (Sum.inl j') (Sum.inr ν)

private theorem hatAvg_Lf_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (y : Fin M → ℝ) :
    hatAvg_Lf Sig A z i μ y = ∑ j, hatAvg_lc Sig A z i μ j * (y j : ℂ) := by
  unfold hatAvg_Lf hatAvg_lc hatAvg_al hatAvg_be
  simp only [hatAvg_linForm_colC, hatAvg_linForm_rowC]
  calc (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) *
            ∑ j, Gmu Sig A z μ (Sum.inl j) (Sum.inr ν) * (y j : ℂ) +
          (∑ j, Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * (y j : ℂ)) *
            Gmu Sig A z μ (Sum.inl i) (Sum.inr ν))
      = (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, ∑ j,
          (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * Gmu Sig A z μ (Sum.inl j) (Sum.inr ν) +
            Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)) *
            (y j : ℂ) := by
        congr 1
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (N : ℂ)⁻¹ * ∑ j, ∑ ν ∈ Finset.univ.erase μ,
          (Gmu Sig A z μ (Sum.inr ν) (Sum.inl i) * Gmu Sig A z μ (Sum.inl j) (Sum.inr ν) +
            Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)) *
            (y j : ℂ) := by rw [Finset.sum_comm]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul]
        ring

private theorem hatAvg_q_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (y : Fin M → ℝ) :
    hatAvg_q Sig A z μ y = ∑ j, ∑ j', (y j : ℂ) * hatAvg_qk Sig A z μ j j' * (y j' : ℂ) := by
  unfold hatAvg_q hatAvg_qk hatAvg_al hatAvg_be
  simp only [hatAvg_linForm_colC, hatAvg_linForm_rowC]
  calc (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        (∑ j, Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) * (y j : ℂ)) *
          ∑ j', Gmu Sig A z μ (Sum.inl j') (Sum.inr ν) * (y j' : ℂ)
      = (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, ∑ j, ∑ j',
          (y j : ℂ) * (Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) *
            Gmu Sig A z μ (Sum.inl j') (Sum.inr ν)) * (y j' : ℂ) := by
        congr 1
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    _ = (N : ℂ)⁻¹ * ∑ j, ∑ j', ∑ ν ∈ Finset.univ.erase μ,
          (y j : ℂ) * (Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) *
            Gmu Sig A z μ (Sum.inl j') (Sum.inr ν)) * (y j' : ℂ) := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring

private theorem hatAvg_conjIf_lin (c : Bool) (a : Fin M → ℂ) (y : Fin M → ℝ) :
    conjIf c (∑ j, a j * (y j : ℂ)) = ∑ j, conjIf c (a j) * (y j : ℂ) := by
  rw [hatAvg_conjIf_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hatAvg_conjIf_mul, hatAvg_conjIf_ofReal]

private theorem hatAvg_conjIf_quad (c : Bool) (Q : Fin M → Fin M → ℂ) (y : Fin M → ℝ) :
    conjIf c (∑ j, ∑ j', (y j : ℂ) * Q j j' * (y j' : ℂ)) =
      ∑ j, ∑ j', (y j : ℂ) * conjIf c (Q j j') * (y j' : ℂ) := by
  rw [hatAvg_conjIf_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hatAvg_conjIf_sum]
  exact Finset.sum_congr rfl fun j' _ => by
    rw [hatAvg_conjIf_mul, hatAvg_conjIf_mul, hatAvg_conjIf_ofReal, hatAvg_conjIf_ofReal]

/-- (A+_avg) for the leading part, deterministic core: one linear form with coefficients at most
`2β²` against `|J|` quadratic forms with entries at most `β²` (each possibly conjugated):
`|E (∑_j c_j y_j) ∏_{r ∈ J} (q_r(y) or its conjugate)| ≤ K' N^{−1/2} 2β² β^{2|J|}`
(`colPoly_bound_two` with one linear form). -/
private theorem hatAvg_colPoly (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)]
      (c : Fin M → ℂ) (Q : Fin M → Fin M → ℂ) (cs : Fin p → Bool) (J : Finset (Fin p)) (β : ℝ),
      1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 0 < β → 2 * β ^ 2 ≤ 1 →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ j, ‖c j‖ ≤ 2 * β ^ 2) → (∀ j j', ‖Q j j'‖ ≤ β ^ 2) →
      ‖∫ y, (∑ j, c j * (y j : ℂ)) *
          ∏ r ∈ J, conjIf (cs r) (∑ j, ∑ j', (y j : ℂ) * Q j j' * (y j' : ℂ))
          ∂(Measure.pi ρ)‖ ≤ K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * (β ^ 2) ^ J.card := by
  choose Kf hKf0 hKf using fun k : ℕ => colPoly_bound_two C τ hτ 1 0 k
  have hK'0 : 0 ≤ ∑ k ∈ Finset.range (p + 1), Kf k := Finset.sum_nonneg fun k _ => hKf0 k
  refine ⟨∑ k ∈ Finset.range (p + 1), Kf k, hK'0, ?_⟩
  intro M N ρ _ c Q cs J β hN hM hβ hβ2 hmean hρ hc hQ
  set k := J.card with hk
  have hkp : k ≤ p := by
    calc k ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_le_univ J
      _ = p := by simp
  set e := J.equivFin with he
  have hβ20 : 0 < β ^ 2 := by positivity
  set B : Fin k → Fin M → Fin M → ℂ := fun t j j' =>
    ((β ^ 2 : ℝ) : ℂ)⁻¹ * conjIf (cs (e.symm t)) (Q j j') with hB
  have hBle : ∀ t j j', ‖B t j j'‖ ≤ 1 := by
    intro t j j'
    simp only [hB, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ20, hatAvg_norm_conjIf]
    rw [inv_mul_le_iff₀ hβ20, mul_one]
    exact hQ j j'
  have hprod : ∀ y : Fin M → ℝ,
      ∏ r ∈ J, conjIf (cs r) (∑ j, ∑ j', (y j : ℂ) * Q j j' * (y j' : ℂ)) =
        ((β ^ 2 : ℝ) : ℂ) ^ k * ∏ t : Fin k, ∑ j, ∑ j', (y j : ℂ) * B t j j' * (y j' : ℂ) := by
    intro y
    rw [← Finset.prod_coe_sort J]
    rw [← e.symm.prod_comp]
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [hatAvg_conjIf_quad, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [hB]
    have : ((β ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ20.ne'
    field_simp
  have h := hKf k M N ρ (fun _ => c) (fun l => Fin.elim0 l) B 1 (2 * β ^ 2) hN hM le_rfl
    (by positivity) hβ2 hmean hρ (fun _ j => hc j) (fun l => Fin.elim0 l) (fun l => Fin.elim0 l)
    (fun l => Fin.elim0 l) hBle (by decide) (by norm_num)
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one, one_pow, add_zero, show ¬((0 : ℕ) = 3) by norm_num, ↓reduceIte,
    tsub_zero, pow_one] at h
  have e1 : (fun y : Fin M → ℝ => (∑ j, c j * (y j : ℂ)) *
      ∏ r ∈ J, conjIf (cs r) (∑ j, ∑ j', (y j : ℂ) * Q j j' * (y j' : ℂ))) =
      fun y => ((β ^ 2 : ℝ) : ℂ) ^ k * ((∑ j, c j * (y j : ℂ)) *
        ∏ t : Fin k, ∑ j, ∑ j', (y j : ℂ) * B t j j' * (y j' : ℂ)) := by
    funext y; rw [hprod]; ring
  rw [e1, integral_const_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hβ20, hatAvg_rpow_half] at *
  have hKk : Kf k ≤ ∑ k ∈ Finset.range (p + 1), Kf k :=
    Finset.single_le_sum (fun k _ => hKf0 k) (Finset.mem_range.2 (by omega))
  calc (β ^ 2) ^ k * ‖∫ y, (∑ j, c j * (y j : ℂ)) *
        ∏ t : Fin k, ∑ j, ∑ j', (y j : ℂ) * B t j j' * (y j' : ℂ) ∂(Measure.pi ρ)‖
      ≤ (β ^ 2) ^ k * (Kf k * (Real.sqrt N)⁻¹ * (2 * β ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ (β ^ 2) ^ k * ((∑ k ∈ Finset.range (p + 1), Kf k) * (Real.sqrt N)⁻¹ * (2 * β ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- For `∑_r κ_r = 3` and `κ_{r₁} = 2` there is exactly one `r₂ ≠ r₁` with `κ_{r₂} = 1`, and
`κ_r = 0` for the other `r`. -/
private theorem hatAvg_kappa_two {p : ℕ} {κ : Fin p → ℕ} (hκ : ∑ r, κ r = 3) {r₁ : Fin p}
    (h₁ : κ r₁ = 2) : ∃ r₂ ∈ Finset.univ.erase r₁, κ r₂ = 1 ∧
      ∀ r ∈ (Finset.univ.erase r₁).erase r₂, κ r = 0 := by
  have hs : ∑ r ∈ Finset.univ.erase r₁, κ r = 1 := by
    have := Finset.add_sum_erase Finset.univ κ (Finset.mem_univ r₁)
    omega
  obtain ⟨r₂, hr₂, hpos⟩ : ∃ r₂ ∈ Finset.univ.erase r₁, 0 < κ r₂ := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have : ∑ r ∈ Finset.univ.erase r₁, κ r = 0 :=
      Finset.sum_eq_zero fun r hr => Nat.le_zero.1 (h r hr)
    omega
  have hs2 := Finset.add_sum_erase (Finset.univ.erase r₁) κ hr₂
  refine ⟨r₂, hr₂, by omega, fun r hr => ?_⟩
  have := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr (f := κ)
  omega

/-- The column expectation of one term of the leading part: `κ_{r₁} = 2`, `κ_{r₂} = 1`:
`|E ∏_{r ≠ r₁} c(λ_{κ_r})| ≤ (1 + C_m)^p 2^p K' N^{−1/2} 2β² (|Ŝ| + β²)^{p−2}`. -/
private theorem hatAvg_P_col {p : ℕ} (hp : 2 ≤ p) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (ρ : Fin M → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ρ j)] {β Cm K' : ℝ} (hβ : 0 < β) (hCm : 0 ≤ Cm) (hK' : 0 ≤ K')
    (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (hlc : ∀ j, ‖hatAvg_lc Sig A z i μ j‖ ≤ 2 * β ^ 2)
    (hcol : ∀ (c : Fin M → ℂ) (J : Finset (Fin p)), (∀ j, ‖c j‖ ≤ 2 * β ^ 2) →
      ‖∫ y, (∑ j, c j * (y j : ℂ)) * ∏ r ∈ J, conjIf (hatAvg_cs p r)
          (∑ j, ∑ j', (y j : ℂ) * hatAvg_qk Sig A z μ j j' * (y j' : ℂ)) ∂(Measure.pi ρ)‖ ≤
        K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * (β ^ 2) ^ J.card)
    (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) (κ : Fin p → ℕ) (hκ : ∑ r, κ r = 3) (r₁ : Fin p)
    (h₁ : κ r₁ = 2) :
    ‖∫ y, ∏ r ∈ Finset.univ.erase r₁, conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r))
        ∂(Measure.pi ρ)‖ ≤
      (1 + Cm) ^ p * 2 ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) *
        (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2)) := by
  obtain ⟨r₂, hr₂, h₂, h0⟩ := hatAvg_kappa_two hκ h₁
  set R := (Finset.univ.erase r₁).erase r₂ with hR
  set m := mFun N (specOf Sig) z with hmdef
  set S := hatAvg_Sh Sig A z μ with hS
  set cs := hatAvg_cs p with hcs
  have hRc : R.card = p - 2 := by
    rw [hR, Finset.card_erase_of_mem hr₂, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  -- the expansion of the product
  set qf : (Fin M → ℝ) → ℂ := fun y => ∑ j, ∑ j', (y j : ℂ) * hatAvg_qk Sig A z μ j j' * (y j' : ℂ)
    with hqf
  set lf : (Fin M → ℝ) → ℂ := fun y => ∑ j, conjIf (cs r₂) (hatAvg_lc Sig A z i μ j) * (y j : ℂ)
    with hlf
  set cJ : Finset (Fin p) → ℂ := fun J => conjIf (cs r₂) m * (∏ r ∈ J, conjIf (cs r) m) *
    ∏ r ∈ R \ J, conjIf (cs r) S with hcJ
  have hexp : ∀ y, ∏ r ∈ Finset.univ.erase r₁, conjIf (cs r) (hatAvg_lam Sig A z i μ y (κ r)) =
      ∑ J ∈ R.powerset, cJ J * (lf y * ∏ r ∈ J, conjIf (cs r) (qf y)) := by
    intro y
    rw [← Finset.mul_prod_erase _ _ hr₂]
    have hl1 : hatAvg_lam Sig A z i μ y (κ r₂) = m * hatAvg_Lf Sig A z i μ y := by
      simp [hatAvg_lam, h₂, hmdef]
    have hl0 : ∀ r ∈ R, conjIf (cs r) (hatAvg_lam Sig A z i μ y (κ r)) =
        conjIf (cs r) m * conjIf (cs r) (qf y) + conjIf (cs r) S := by
      intro r hr
      simp only [hatAvg_lam, h0 r hr, ↓reduceIte, hatAvg_conjIf_add, hatAvg_conjIf_mul, hS, hmdef,
        hqf, hatAvg_q_eq]
      ring
    rw [Finset.prod_congr rfl hl0, Finset.prod_add, hl1, hatAvg_conjIf_mul, hatAvg_Lf_eq,
      hatAvg_conjIf_lin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [hcJ, hlf, Finset.prod_mul_distrib]
    ring
  -- integrability
  have hqM : hatAvg_Mom ρ qf := hatAvg_Mom_sum _ fun j _ => hatAvg_Mom_sum _ fun j' _ =>
    hatAvg_Mom_mul (hatAvg_Mom_mul (hatAvg_Mom_coord hρ j) (hatAvg_Mom_const _))
      (hatAvg_Mom_coord hρ j')
  have hlM : hatAvg_Mom ρ lf := hatAvg_Mom_sum _ fun j _ =>
    hatAvg_Mom_mul (hatAvg_Mom_const _) (hatAvg_Mom_coord hρ j)
  have hTM : ∀ J : Finset (Fin p), Integrable (fun y => lf y * ∏ r ∈ J, conjIf (cs r) (qf y))
      (Measure.pi ρ) := fun J =>
    (hatAvg_Mom_mul hlM (hatAvg_Mom_prod _ fun r _ => hatAvg_Mom_conjIf _ hqM)).integrable
  rw [integral_congr_ae (ae_of_all _ hexp),
    integral_finsetSum _ fun J _ => (hTM J).const_mul _]
  simp only [integral_const_mul]
  -- the bound of each term
  have hX0 : 0 ≤ ‖S‖ + β ^ 2 := by positivity
  have hterm : ∀ J ∈ R.powerset, ‖cJ J * ∫ y, lf y * ∏ r ∈ J, conjIf (cs r) (qf y)
      ∂(Measure.pi ρ)‖ ≤
      (1 + Cm) ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * (‖S‖ + β ^ 2) ^ (p - 2)) := by
    intro J hJ
    have hJR : J ⊆ R := Finset.mem_powerset.1 hJ
    have hJc : J.card ≤ R.card := Finset.card_le_card hJR
    have hcJb : ‖cJ J‖ ≤ (1 + Cm) ^ p * ‖S‖ ^ (R \ J).card := by
      simp only [hcJ, norm_mul, norm_prod, hatAvg_norm_conjIf, Finset.prod_const]
      have h1 : ‖m‖ * ‖m‖ ^ J.card ≤ (1 + Cm) ^ p := by
        rw [← pow_succ']
        calc ‖m‖ ^ (J.card + 1) ≤ (1 + Cm) ^ (J.card + 1) :=
              pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
          _ ≤ (1 + Cm) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hI := hcol (fun j => conjIf (cs r₂) (hatAvg_lc Sig A z i μ j)) J
      (fun j => by rw [hatAvg_norm_conjIf]; exact hlc j)
    have hpow : (β ^ 2) ^ J.card * ‖S‖ ^ (R \ J).card ≤ (‖S‖ + β ^ 2) ^ (p - 2) := by
      have hsd : (R \ J).card = R.card - J.card := Finset.card_sdiff_of_subset hJR
      calc (β ^ 2) ^ J.card * ‖S‖ ^ (R \ J).card
          ≤ (‖S‖ + β ^ 2) ^ J.card * (‖S‖ + β ^ 2) ^ (R \ J).card := by
            gcongr
            · linarith [norm_nonneg S]
            · linarith [sq_nonneg β]
        _ = (‖S‖ + β ^ 2) ^ (p - 2) := by
            rw [← pow_add, hsd, hRc]; congr 1; omega
    rw [norm_mul]
    calc ‖cJ J‖ * ‖∫ y, lf y * ∏ r ∈ J, conjIf (cs r) (qf y) ∂(Measure.pi ρ)‖
        ≤ ((1 + Cm) ^ p * ‖S‖ ^ (R \ J).card) *
            (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * (β ^ 2) ^ J.card) :=
          mul_le_mul hcJb hI (norm_nonneg _) (by positivity)
      _ = (1 + Cm) ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2)) *
            ((β ^ 2) ^ J.card * ‖S‖ ^ (R \ J).card) := by ring
      _ ≤ (1 + Cm) ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2)) * (‖S‖ + β ^ 2) ^ (p - 2) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, hRc]
  have h2 : ((2 ^ (p - 2) : ℕ) : ℝ) ≤ 2 ^ p := by
    push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc ((2 ^ (p - 2) : ℕ) : ℝ) * ((1 + Cm) ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) *
        (‖S‖ + β ^ 2) ^ (p - 2)))
      ≤ 2 ^ p * ((1 + Cm) ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) *
        (‖S‖ + β ^ 2) ^ (p - 2))) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

/-- The leading part is a polynomial in the column: all its moments are finite. -/
private theorem hatAvg_lam_Mom (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)]
    (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j)) (k : ℕ) :
    hatAvg_Mom ρ fun y => hatAvg_lam Sig A z i μ y k := by
  have hal : ∀ ν, hatAvg_Mom ρ fun y => hatAvg_al Sig A z μ ν y := fun ν =>
    hatAvg_Mom_linForm hρ _
  have hbe : ∀ ν, hatAvg_Mom ρ fun y => hatAvg_be Sig A z μ ν y := fun ν =>
    hatAvg_Mom_linForm hρ _
  have hq : hatAvg_Mom ρ fun y => hatAvg_q Sig A z μ y :=
    hatAvg_Mom_mul (hatAvg_Mom_const _) (hatAvg_Mom_sum _ fun ν _ => hatAvg_Mom_mul (hal ν) (hbe ν))
  have hL : hatAvg_Mom ρ fun y => hatAvg_Lf Sig A z i μ y :=
    hatAvg_Mom_mul (hatAvg_Mom_const _) (hatAvg_Mom_sum _ fun ν _ =>
      hatAvg_Mom_add (hatAvg_Mom_mul (hatAvg_Mom_const _) (hbe ν))
        (hatAvg_Mom_mul (hal ν) (hatAvg_Mom_const _)))
  unfold hatAvg_lam
  split_ifs
  · exact hatAvg_Mom_add (hatAvg_Mom_const _) (hatAvg_Mom_mul (hatAvg_Mom_const _) hq)
  · exact hatAvg_Mom_mul (hatAvg_Mom_const _) hL
  · exact hatAvg_Mom_const _

/-- (A+_avg) for the leading part on the `X^{(μ)}`-measurable event:
`|E_μ (leading part)| ≤ K_L (1 + C_m)^{p+2} K_g N⁻¹ N^{−1/2} β² (|Ŝ| + β²)^{p−2}`. -/
private theorem hatAvg_lead_col (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ KL : ℝ, 0 ≤ KL ∧ ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (ρ : Fin M → Measure ℝ)
      [∀ j, IsProbabilityMeasure (ρ j)] (β Cm Kg : ℝ), 1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 0 < β →
      2 * β ^ 2 ≤ 1 → 0 ≤ Cm → (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ β ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ β) →
      ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ Kg → ‖mFun N (specOf Sig) z‖ ≤ Cm →
      ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(Measure.pi ρ)‖ ≤
        KL * (1 + Cm) ^ (p + 2) * Kg * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ *
          (β ^ 2 * (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2)))) := by
  obtain ⟨K', hK'0, hK'⟩ := hatAvg_colPoly C τ hτ p
  refine ⟨4 ^ p * p * 2 ^ p * 2 * K', by positivity, ?_⟩
  intro M N Sig A z i μ ρ _ β Cm Kg hN hM hβ hβ2 hCm hmean hρ hGν hGii hm
  have hρi : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) := fun j n => (hρ j n).1
  have hKg : 0 ≤ Kg := (norm_nonneg _).trans hGii
  have hlc : ∀ j, ‖hatAvg_lc Sig A z i μ j‖ ≤ 2 * β ^ 2 := by
    intro j
    unfold hatAvg_lc
    refine hatAvg_avg_le (by positivity) fun ν hν => ?_
    obtain ⟨h1, h2⟩ := hGν ν hν i
    obtain ⟨h3, h4⟩ := hGν ν hν j
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc _ ≤ β * β + β * β :=
          add_le_add (mul_le_mul h1 h4 (norm_nonneg _) hβ.le)
            (mul_le_mul h3 h2 (norm_nonneg _) hβ.le)
      _ = 2 * β ^ 2 := by ring
  have hqk : ∀ j j', ‖hatAvg_qk Sig A z μ j j'‖ ≤ β ^ 2 := by
    intro j j'
    unfold hatAvg_qk
    refine hatAvg_avg_le (by positivity) fun ν hν => ?_
    rw [norm_mul]
    calc _ ≤ β * β := mul_le_mul (hGν ν hν j).1 (hGν ν hν j').2 (norm_nonneg _) hβ.le
      _ = β ^ 2 := by ring
  have hcol : ∀ (c : Fin M → ℂ) (J : Finset (Fin p)), (∀ j, ‖c j‖ ≤ 2 * β ^ 2) →
      ‖∫ y, (∑ j, c j * (y j : ℂ)) * ∏ r ∈ J, conjIf (hatAvg_cs p r)
          (∑ j, ∑ j', (y j : ℂ) * hatAvg_qk Sig A z μ j j' * (y j' : ℂ)) ∂(Measure.pi ρ)‖ ≤
        K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * (β ^ 2) ^ J.card := fun c J hc =>
    hK' M N ρ c (hatAvg_qk Sig A z μ) (hatAvg_cs p) J β hN hM hβ hβ2 hmean hρ hc hqk
  set X := ‖hatAvg_Sh Sig A z μ‖ + β ^ 2 with hX
  set T := (1 + Cm) ^ p * 2 ^ p * (K' * (Real.sqrt N)⁻¹ * (2 * β ^ 2) * X ^ (p - 2)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hP : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∀ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
      ‖∫ y, ∏ r ∈ Finset.univ.erase r₁, conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r))
        ∂(Measure.pi ρ)‖ ≤ T := by
    intro κ hκ r₁ hr₁
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    exact hatAvg_P_col hp Sig A z i μ ρ hβ hCm hK'0 hρi hlc hcol hm κ hκ r₁
      (Finset.mem_filter.1 hr₁).2
  have hℓ : ‖hatAvg_ell Sig A z i μ‖ ≤ (N : ℝ)⁻¹ * ((1 + Cm) ^ 2 * Kg) := by
    unfold hatAvg_ell
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ hGii (norm_nonneg _) (by positivity))
      (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hPM : ∀ κ : Fin p → ℕ, ∀ r₁ : Fin p, hatAvg_Mom ρ fun y =>
      conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) * ∏ r ∈ Finset.univ.erase r₁,
        conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r)) := fun κ r₁ =>
    hatAvg_Mom_mul (hatAvg_Mom_const _) (hatAvg_Mom_prod _ fun r _ =>
      hatAvg_Mom_conjIf _ (hatAvg_lam_Mom Sig A z i μ ρ hρi _))
  unfold hatAvg_Lead
  rw [integral_finsetSum _ fun κ _ => (hatAvg_Mom_sum _ fun r₁ _ => hPM κ r₁).integrable]
  have hinner : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3,
      ‖∫ y, ∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) * ∏ r ∈ Finset.univ.erase r₁,
          conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r)) ∂(Measure.pi ρ)‖ ≤
        p * ((N : ℝ)⁻¹ * ((1 + Cm) ^ 2 * Kg) * T) := by
    intro κ hκ
    rw [integral_finsetSum _ fun r₁ _ => (hPM κ r₁).integrable]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        ‖∫ y, conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) * ∏ r ∈ Finset.univ.erase r₁,
          conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ y (κ r)) ∂(Measure.pi ρ)‖ ≤
          (N : ℝ)⁻¹ * ((1 + Cm) ^ 2 * Kg) * T := by
      intro r₁ hr₁
      rw [integral_const_mul, norm_mul, hatAvg_norm_conjIf]
      exact mul_le_mul hℓ (hP κ hκ r₁ hr₁) (norm_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (Finset.univ.filter (fun r => κ r = 2)).card ≤ p := by
      calc _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
        _ = p := by simp
    exact_mod_cast this
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hinner).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := hatAvg_card_T p 3
  have h4 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  rw [h4] at hcard
  calc ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) * (p * ((N : ℝ)⁻¹ * ((1 + Cm) ^ 2 * Kg) * T))
      ≤ 4 ^ p * (p * ((N : ℝ)⁻¹ * ((1 + Cm) ^ 2 * Kg) * T)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hT]; ring

/-! ## The `X^{(μ)}`-measurable event, measurability, rough bounds -/

/-- The `X^{(μ)}`-measurable event of §9: `|G^{(μ)}_{st} − Π_{st}| ≤ β` for `s, t ≠ μ`. -/
private def hatAvg_Good (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (β : ℝ) : Prop :=
  ∀ s t, s ≠ Sum.inr μ → t ≠ Sum.inr μ → ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β

private theorem hatAvg_Good_updCol (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (β : ℝ) (y : Fin M → ℝ) :
    hatAvg_Good Sig (updCol A μ y) z μ β ↔ hatAvg_Good Sig A z μ β := by
  unfold hatAvg_Good
  rw [Gmu_updCol]

/-- The entries of `G^{(μ)}` on the `X^{(μ)}`-measurable event. -/
private theorem hatAvg_good_entries {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N} {β KP : ℝ}
    (hGood : hatAvg_Good Sig A z μ β) (hβ : 0 ≤ β) (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ KP + β) ∧
    (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ β ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ β) := by
  have hKP : 0 ≤ KP := (norm_nonneg _).trans (hPi (Sum.inr μ) (Sum.inr μ))
  refine ⟨fun s t => ?_, fun ν hν j => ?_⟩
  · by_cases hs : s = Sum.inr μ
    · rw [hs, hatAvg_Gmu_row]; simp only [norm_zero]; linarith
    by_cases ht : t = Sum.inr μ
    · rw [ht, hatAvg_Gmu_col]; simp only [norm_zero]; linarith
    have h1 := hGood s t hs ht
    have h2 := norm_add_le (Gmu Sig A z μ s t - PiZ N Sig z s t) (PiZ N Sig z s t)
    rw [sub_add_cancel] at h2
    linarith [hPi s t]
  · have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
    have h1 := hGood _ _ hne (Sum.inl_ne_inr (a := j) (b := μ))
    have h2 := hGood _ _ (Sum.inl_ne_inr (a := j) (b := μ)) hne
    have e1 : PiZ N Sig z (Sum.inr ν) (Sum.inl j) = 0 := by simp [PiZ, piMat]
    have e2 : PiZ N Sig z (Sum.inl j) (Sum.inr ν) = 0 := by simp [PiZ, piMat]
    rw [e1, sub_zero] at h1
    rw [e2, sub_zero] at h2
    exact ⟨h1, h2⟩

/-- On the `X^{(μ)}`-measurable event: `|Ŝ| ≤ β`. -/
private theorem hatAvg_Sh_good {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N} {β : ℝ}
    (hGood : hatAvg_Good Sig A z μ β) (hβ : 0 ≤ β) : ‖hatAvg_Sh Sig A z μ‖ ≤ β := by
  unfold hatAvg_Sh
  refine hatAvg_avg_le hβ fun ν hν => ?_
  have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
  have h := hGood _ _ hne hne
  have e : PiZ N Sig z (Sum.inr ν) (Sum.inr ν) = mFun N (specOf Sig) z := by simp [PiZ, piMat]
  rwa [e] at h

/-- The leading part depends on the matrix through `G^{(μ)}` and the column `μ` only. -/
private theorem hatAvg_Lead_updCol (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (p : ℕ) (y : Fin M → ℝ) :
    hatAvg_Lead Sig (updCol A μ y) z i μ p (fun j => updCol A μ y j μ) =
      hatAvg_Lead Sig A z i μ p y := by
  have hy : (fun j => updCol A μ y j μ) = y := funext fun j => by simp [updCol]
  have hG := Gmu_updCol Sig A z μ y
  have hc : ∀ x, colC Sig (updCol A μ y) z x μ = colC Sig A z x μ := fun x => by
    funext j; simp only [colC, hG]
  have hr : ∀ x, rowC Sig (updCol A μ y) z x μ = rowC Sig A z x μ := fun x => by
    funext j; simp only [rowC, hG]
  rw [hy]
  simp only [hatAvg_Lead, hatAvg_lam, hatAvg_Sh, hatAvg_q, hatAvg_Lf, hatAvg_ell, hatAvg_al,
    hatAvg_be, hc, hr, hG]

section MeasHat

variable {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im)
include hSig hz

private theorem hatAvg_meas_Good (μ : Fin N) (β : ℝ) :
    MeasurableSet {A : Matrix (Fin M) (Fin N) ℝ | hatAvg_Good Sig A z μ β} := by
  have e : {A : Matrix (Fin M) (Fin N) ℝ | hatAvg_Good Sig A z μ β} =
      ⋂ s : Fin M ⊕ Fin N, ⋂ t : Fin M ⊕ Fin N,
        {A | s ≠ Sum.inr μ → t ≠ Sum.inr μ → ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} := by
    ext A; simp [hatAvg_Good]
  rw [e]
  refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun t => ?_
  by_cases h : s ≠ Sum.inr μ ∧ t ≠ Sum.inr μ
  · have e2 : {A : Matrix (Fin M) (Fin N) ℝ | s ≠ Sum.inr μ → t ≠ Sum.inr μ →
        ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} =
        {A | ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} := by
      ext A; simp [h.1, h.2]
    rw [e2]
    exact measurableSet_le ((hatAvg_cont_Gmu hSig hz μ s t).sub continuous_const).norm.measurable
      measurable_const
  · have e2 : {A : Matrix (Fin M) (Fin N) ℝ | s ≠ Sum.inr μ → t ≠ Sum.inr μ →
        ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} = Set.univ := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro hs ht; exact absurd ⟨hs, ht⟩ h
    rw [e2]; exact MeasurableSet.univ

omit hSig hz in
private theorem hatAvg_cont_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => by
    simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem hatAvg_cont_resCoeff (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => resCoeff Sig A z v i μ k := by
  have hG := hatAvg_cont_G (N := N) hSig hz
  unfold resCoeff
  refine continuous_const.mul ((hatAvg_cont_ent _ _).comp ?_)
  exact (hG.matrix_mul ((continuous_const.matrix_mul hG).pow k)).sub continuous_const

private theorem hatAvg_cont_D (i : Fin M) (μ : Fin N) (p : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      fCoeff p (avgCoeff Sig A z i μ) 3 - fCoeff p (avgCoeffHat Sig A z i μ) 3 := by
  have h1 : ∀ k, Continuous fun A : Matrix (Fin M) (Fin N) ℝ => avgCoeff Sig A z i μ k :=
    fun k => continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      hatAvg_cont_resCoeff hSig hz _ i μ k)
  have h2 : ∀ k, Continuous fun A : Matrix (Fin M) (Fin N) ℝ => avgCoeffHat Sig A z i μ k :=
    fun k => continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      hatAvg_cont_resCoeff hSig hz _ i μ k)
  have hf : ∀ a : Matrix (Fin M) (Fin N) ℝ → ℕ → ℂ, (∀ k, Continuous fun A => a A k) →
      Continuous fun A => fCoeff p (a A) 3 := by
    intro a ha
    unfold fCoeff
    refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
    split_ifs
    · exact ha _
    · exact Complex.continuous_conj.comp (ha _)
  exact (hf _ h1).sub (hf _ h2)

private theorem hatAvg_cont_Lead (i : Fin M) (μ : Fin N) (p : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_Lead Sig A z i μ p (fun j => A j μ) := by
  have hGm := hatAvg_cont_Gmu hSig hz μ
  have hal : ∀ ν, Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_al Sig A z μ ν (fun j => A j μ) := fun ν => hatAvg_cont_colC hSig hz μ _
  have hbe : ∀ ν, Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_be Sig A z μ ν (fun j => A j μ) := fun ν => hatAvg_cont_rowC hSig hz μ _
  have hS : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hatAvg_Sh Sig A z μ :=
    continuous_const.mul (continuous_finsetSum _ fun ν _ => (hGm _ _).sub continuous_const)
  have hq : Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_q Sig A z μ (fun j => A j μ) :=
    continuous_const.mul (continuous_finsetSum _ fun ν _ => (hal ν).mul (hbe ν))
  have hL : Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_Lf Sig A z i μ (fun j => A j μ) :=
    continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      ((hGm _ _).mul (hbe ν)).add ((hal ν).mul (hGm _ _)))
  have hℓ : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hatAvg_ell Sig A z i μ :=
    continuous_const.mul (continuous_const.mul (hGm _ _))
  have hlam : ∀ k, Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      hatAvg_lam Sig A z i μ (fun j => A j μ) k := by
    intro k
    unfold hatAvg_lam
    split_ifs
    · exact hS.add (continuous_const.mul hq)
    · exact continuous_const.mul hL
    · exact continuous_const
  have hcj : ∀ (c : Bool) {f : Matrix (Fin M) (Fin N) ℝ → ℂ}, Continuous f →
      Continuous fun A => conjIf c (f A) := by
    intro c f hf
    cases c
    · simpa [conjIf] using hf
    · simp only [conjIf, ite_true]; exact Complex.continuous_conj.comp hf
  unfold hatAvg_Lead
  exact continuous_finsetSum _ fun κ _ => continuous_finsetSum _ fun r₁ _ =>
    (hcj _ hℓ).mul (continuous_finsetProd _ fun r _ => hcj _ (hlam _))

end MeasHat

/-- `|f_n| ≤ (n + 1)^p y^p` when `|a_k| ≤ y` for all `k ≤ n`. -/
private theorem hatAvg_fCoeff_le (p : ℕ) {a : ℕ → ℂ} {y : ℝ} (hy : 0 ≤ y) (n : ℕ)
    (ha : ∀ k ≤ n, ‖a k‖ ≤ y) : ‖fCoeff p a n‖ ≤ ((n : ℝ) + 1) ^ p * y ^ p := by
  rw [hatAvg_fCoeff_eq]
  calc _ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ‖∏ r : Fin p,
        conjIf (hatAvg_cs p r) (a (κ r))‖ := norm_sum_le _ _
    _ ≤ ∑ _κ ∈ Finset.Nat.antidiagonalTuple p n, y ^ p := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [norm_prod]
        calc _ ≤ ∏ _r : Fin p, y := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
                have hk : κ r ≤ n := by
                  have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
                  omega
                rw [hatAvg_norm_conjIf]; exact ha _ hk
          _ = y ^ p := by simp
    _ = ((Finset.Nat.antidiagonalTuple p n).card : ℝ) * y ^ p := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hatAvg_card_T p n) (pow_nonneg hy p)

/-- The deterministic bound of `f_3(a) − f_3(â)` from `|G_{st}| ≤ R`, `|Π_{st}| ≤ K_Π`. -/
private theorem hatAvg_D_rough {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (p : ℕ)
    {R KP : ℝ} (hR0 : 0 ≤ R) (hKP : 0 ≤ KP) (hR : ∀ s t, ‖G Sig A z s t‖ ≤ R)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    ‖fCoeff p (avgCoeff Sig A z i μ) 3 - fCoeff p (avgCoeffHat Sig A z i μ) 3‖ ≤
      2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p) := by
  have hB1 : 1 ≤ R + KP + 1 := by linarith
  have hres : ∀ ν : Fin N, ∀ k ≤ 3, ‖resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤
      8 * (R + KP + 1) ^ 4 := by
    intro ν k hk
    have h0 : Fv Sig A z (eI (Sum.inr ν)) ≤ R + KP + 1 := by
      unfold Fv
      rw [hatAvg_vbar_inr, ent_eI_eI, Matrix.sub_apply]
      have := norm_sub_le (G Sig A z (Sum.inr ν) (Sum.inr ν)) (PiZ N Sig z (Sum.inr ν) (Sum.inr ν))
      linarith [hR (Sum.inr ν) (Sum.inr ν), hPi (Sum.inr ν) (Sum.inr ν)]
    have h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig (eI (Sum.inr ν))) (eI (letterT i μ b))‖ ≤
        R + KP + 1 := fun b => by
      rw [hatAvg_vbar_inr, ent_eI_eI]; linarith [hR (Sum.inr ν) (letterT i μ b)]
    have h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig (eI (Sum.inr ν)))‖ ≤
        R + KP + 1 := fun b => by
      rw [hatAvg_vbar_inr, ent_eI_eI]; linarith [hR (letterS i μ b) (Sum.inr ν)]
    have h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ R + KP + 1 := fun b b' => by
      linarith [hR (letterS i μ b) (letterT i μ b')]
    refine (norm_resCoeff_le hSig A hz _ i μ h0 h1 h2 h3 k).trans ?_
    have e1 : (2 : ℝ) ^ k ≤ 8 := by
      calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
        _ = 8 := by norm_num
    exact mul_le_mul e1 (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by norm_num)
  have havg : ∀ (s : Finset (Fin N)), ∀ k ≤ 3,
      ‖(N : ℂ)⁻¹ * ∑ ν ∈ s, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤ 8 * (R + KP + 1) ^ 4 := by
    intro s k hk
    have hN : 0 < N := Fin.pos μ
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ ν ∈ s, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖
        ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, 8 * (R + KP + 1) ^ 4 := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
          exact (Finset.sum_le_sum fun ν _ => hres ν k hk).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun _ _ _ => by positivity)
      _ = 8 * (R + KP + 1) ^ 4 := by simp; field_simp
  have h1 := hatAvg_fCoeff_le p (by positivity : (0 : ℝ) ≤ 8 * (R + KP + 1) ^ 4) 3
    (a := avgCoeff Sig A z i μ) fun k hk => havg Finset.univ k hk
  have h2 := hatAvg_fCoeff_le p (by positivity : (0 : ℝ) ≤ 8 * (R + KP + 1) ^ 4) 3
    (a := avgCoeffHat Sig A z i μ) fun k hk => havg _ k hk
  have h4 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  rw [h4, ← mul_pow] at h1 h2
  calc _ ≤ ‖fCoeff p (avgCoeff Sig A z i μ) 3‖ + ‖fCoeff p (avgCoeffHat Sig A z i μ) 3‖ :=
        norm_sub_le _ _
    _ ≤ (4 * (8 * (R + KP + 1) ^ 4)) ^ p + (4 * (8 * (R + KP + 1) ^ 4)) ^ p := add_le_add h1 h2
    _ = 2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p) := by rw [mul_pow (4 : ℝ)]; ring

/-- The bound of the leading part on the `X^{(μ)}`-measurable event, `β ≤ 1`:
`|(leading part)| ≤ 4^p p (1 + C_m)² K (2 (1 + C_m) K² (1 + V)²)^p`, `K = K_Π + 1`,
`V = ∑_j |X_{jμ}|`. -/
private theorem hatAvg_Lead_rough {Sig : Matrix (Fin M) (Fin M) ℝ}
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (i : Fin M) (μ : Fin N) (p : ℕ) {β KP Cm : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hKP : 0 ≤ KP) (hCm : 0 ≤ Cm) (hGood : hatAvg_Good Sig A z μ β)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) :
    ‖hatAvg_Lead Sig A z i μ p (fun j => A j μ)‖ ≤
      4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) *
        (2 * (1 + Cm) * (KP + 1) ^ 2 * (1 + hatAvg_V A μ) ^ 2) ^ p := by
  obtain ⟨hK, -⟩ := hatAvg_good_entries hGood hβ hPi
  have hN : 0 < N := Fin.pos μ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set K := KP + 1 with hKdef
  have hK' : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K := fun s t => (hK s t).trans (by linarith)
  have hK0 : 0 ≤ K := by linarith
  set V := hatAvg_V A μ with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hform : ∀ (s : Fin M ⊕ Fin N), ‖∑ j, Gmu Sig A z μ s (Sum.inl j) * ((A j μ : ℝ) : ℂ)‖ ≤
      K * V ∧ ‖∑ j, Gmu Sig A z μ (Sum.inl j) s * ((A j μ : ℝ) : ℂ)‖ ≤ K * V := by
    intro s
    constructor
    · refine (norm_sum_le _ _).trans ?_
      rw [hV, hatAvg_V, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hK' _ _) (abs_nonneg _)
    · refine (norm_sum_le _ _).trans ?_
      rw [hV, hatAvg_V, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hK' _ _) (abs_nonneg _)
  have hal : ∀ ν, ‖hatAvg_al Sig A z μ ν (fun j => A j μ)‖ ≤ K * V := fun ν => by
    unfold hatAvg_al; rw [hatAvg_linForm_colC]; exact (hform _).1
  have hbe : ∀ ν, ‖hatAvg_be Sig A z μ ν (fun j => A j μ)‖ ≤ K * V := fun ν => by
    unfold hatAvg_be; rw [hatAvg_linForm_rowC]; exact (hform _).2
  have hKV : 0 ≤ K * V := mul_nonneg hK0 hV0
  have hq : ‖hatAvg_q Sig A z μ (fun j => A j μ)‖ ≤ (K * V) ^ 2 := by
    unfold hatAvg_q
    refine hatAvg_avg_le (by positivity) fun ν _ => ?_
    rw [norm_mul, sq]
    exact mul_le_mul (hal ν) (hbe ν) (norm_nonneg _) hKV
  have hLf : ‖hatAvg_Lf Sig A z i μ (fun j => A j μ)‖ ≤ 2 * K * (K * V) := by
    unfold hatAvg_Lf
    refine hatAvg_avg_le (by positivity) fun ν _ => ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc _ ≤ K * (K * V) + K * V * K :=
          add_le_add (mul_le_mul (hK' _ _) (hbe ν) (norm_nonneg _) hK0)
            (mul_le_mul (hal ν) (hK' _ _) (norm_nonneg _) hKV)
      _ = 2 * K * (K * V) := by ring
  have hS : ‖hatAvg_Sh Sig A z μ‖ ≤ 1 := (hatAvg_Sh_good hGood hβ).trans hβ1
  set Λ := 2 * (1 + Cm) * K ^ 2 * (1 + V) ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hlam : ∀ k, ‖hatAvg_lam Sig A z i μ (fun j => A j μ) k‖ ≤ Λ := by
    intro k
    have hK1 : 1 ≤ K := by linarith
    have hV1 : V ^ 2 ≤ (1 + V) ^ 2 := pow_le_pow_left₀ hV0 (by linarith) 2
    have hV2 : V ≤ (1 + V) ^ 2 := by nlinarith
    have hK2 : K ≤ K ^ 2 := by nlinarith
    have h1V : 1 ≤ (1 + V) ^ 2 := one_le_pow₀ (by linarith)
    have hK2' : 1 ≤ K ^ 2 := one_le_pow₀ hK1
    unfold hatAvg_lam
    split_ifs
    · refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h3 : ‖mFun N (specOf Sig) z‖ * ‖hatAvg_q Sig A z μ (fun j => A j μ)‖ ≤
          Cm * (K ^ 2 * (1 + V) ^ 2) := by
        refine mul_le_mul hm (hq.trans ?_) (norm_nonneg _) hCm
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hV1 (by positivity)
      have h4 : 1 ≤ K ^ 2 * (1 + V) ^ 2 := one_le_mul_of_one_le_of_one_le hK2' h1V
      have h5 : 0 ≤ Cm * (K ^ 2 * (1 + V) ^ 2) := by positivity
      calc _ ≤ 1 + Cm * (K ^ 2 * (1 + V) ^ 2) := add_le_add hS h3
        _ ≤ Λ := by rw [hΛ]; nlinarith
    · rw [norm_mul]
      have h3 : ‖mFun N (specOf Sig) z‖ * ‖hatAvg_Lf Sig A z i μ (fun j => A j μ)‖ ≤
          Cm * (2 * K ^ 2 * (1 + V) ^ 2) := by
        refine mul_le_mul hm (hLf.trans ?_) (norm_nonneg _) hCm
        have : K * V ≤ K * (1 + V) ^ 2 := mul_le_mul_of_nonneg_left hV2 hK0
        calc 2 * K * (K * V) ≤ 2 * K * (K * (1 + V) ^ 2) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = 2 * K ^ 2 * (1 + V) ^ 2 := by ring
      have h5 : 0 ≤ 2 * K ^ 2 * (1 + V) ^ 2 := by positivity
      calc _ ≤ Cm * (2 * K ^ 2 * (1 + V) ^ 2) := h3
        _ ≤ Λ := by rw [hΛ]; nlinarith
    · simp only [norm_zero]; exact hΛ0
  have hℓ : ‖hatAvg_ell Sig A z i μ‖ ≤ (1 + Cm) ^ 2 * K := by
    unfold hatAvg_ell
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, norm_pow]
    have h1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNr
    have h2 : ‖mFun N (specOf Sig) z‖ ^ 2 ≤ (1 + Cm) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    calc (N : ℝ)⁻¹ * (‖mFun N (specOf Sig) z‖ ^ 2 * ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖)
        ≤ 1 * ((1 + Cm) ^ 2 * K) :=
          mul_le_mul h1 (mul_le_mul h2 (hK' _ _) (norm_nonneg _) (by positivity))
            (by positivity) zero_le_one
      _ = (1 + Cm) ^ 2 * K := one_mul _
  have hΛ1 : 1 ≤ Λ := by
    have hK1 : 1 ≤ K := by linarith
    have h1 : 1 ≤ (1 + V) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
    have h3 : 1 ≤ 2 * (1 + Cm) := by linarith
    rw [hΛ]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ 2 * (1 + Cm) * K ^ 2 * (1 + V) ^ 2 := by gcongr
  unfold hatAvg_Lead
  refine (norm_sum_le _ _).trans ?_
  have hinner : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3,
      ‖∑ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) * ∏ r ∈ Finset.univ.erase r₁,
          conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ (fun j => A j μ) (κ r))‖ ≤
        p * ((1 + Cm) ^ 2 * K * Λ ^ p) := by
    intro κ _
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ r₁ ∈ Finset.univ.filter (fun r => κ r = 2),
        ‖conjIf (hatAvg_cs p r₁) (hatAvg_ell Sig A z i μ) * ∏ r ∈ Finset.univ.erase r₁,
          conjIf (hatAvg_cs p r) (hatAvg_lam Sig A z i μ (fun j => A j μ) (κ r))‖ ≤
          (1 + Cm) ^ 2 * K * Λ ^ p := by
      intro r₁ _
      rw [norm_mul, hatAvg_norm_conjIf, norm_prod]
      refine mul_le_mul hℓ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      calc ∏ r ∈ Finset.univ.erase r₁, ‖conjIf (hatAvg_cs p r)
            (hatAvg_lam Sig A z i μ (fun j => A j μ) (κ r))‖
          ≤ ∏ _r ∈ Finset.univ.erase r₁, Λ :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
              rw [hatAvg_norm_conjIf]; exact hlam _
        _ = Λ ^ (p - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin]
        _ ≤ Λ ^ p := pow_le_pow_right₀ hΛ1 (Nat.sub_le p 1)
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (Finset.univ.filter (fun r => κ r = 2)).card ≤ p := by
      calc _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
        _ = p := by simp
    exact_mod_cast this
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := hatAvg_card_T p 3
  have h4 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  rw [h4] at hcard
  calc ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) * (p * ((1 + Cm) ^ 2 * K * Λ ^ p))
      ≤ 4 ^ p * (p * ((1 + Cm) ^ 2 * K * Λ ^ p)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hΛ]; ring

/-! ## (avg_pf_claim) for `n = 3`, the removal of `ν = μ`, at one `(i, μ)` -/

/-- On the a priori event: `|Ŝ| ≤ F̃ + N⁻¹ b + (L² + C_m L²) b²`. -/
private theorem hatAvg_Sh_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b L Cm : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L) (hCm : 0 ≤ Cm)
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) :
    ‖hatAvg_Sh Sig A z μ‖ ≤ Ft Sig A z + (N : ℝ)⁻¹ * b + (L ^ 2 + Cm * L ^ 2) * b ^ 2 := by
  have hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b := by
    have := hG (Sum.inr μ) (Sum.inr μ); simpa [PiZ, piMat] using this
  have h0 := hatAvg_hat0_le Sig A z i μ hgm
  have h1 := hatAvg_lam0_sub hSig A hz i μ hb0 hL hG hμ hgm
  have hq : ‖hatAvg_q Sig A z μ (fun j => A j μ)‖ ≤ L ^ 2 * b ^ 2 := by
    unfold hatAvg_q
    refine hatAvg_avg_le (by positivity) fun ν hν => ?_
    have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
    obtain ⟨h2, h3⟩ := hatAvg_form_event hSig A hz μ hG hμ _ hne
    rw [norm_mul]
    calc _ ≤ L * b * (L * b) := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = L ^ 2 * b ^ 2 := by ring
  have hmq : ‖mFun N (specOf Sig) z * hatAvg_q Sig A z μ (fun j => A j μ)‖ ≤
      Cm * (L ^ 2 * b ^ 2) := by
    rw [norm_mul]; exact mul_le_mul hm hq (norm_nonneg _) hCm
  simp only [hatAvg_lam, ↓reduceIte] at h1
  have e : hatAvg_Sh Sig A z μ = avgCoeffHat Sig A z i μ 0 -
      (avgCoeffHat Sig A z i μ 0 - (hatAvg_Sh Sig A z μ + mFun N (specOf Sig) z *
        hatAvg_q Sig A z μ (fun j => A j μ))) -
      mFun N (specOf Sig) z * hatAvg_q Sig A z μ (fun j => A j μ) := by ring
  rw [e]
  have hb3 : b ^ 3 ≤ b ^ 2 := pow_le_pow_of_le_one hb0 hb1 (by norm_num)
  have hL3 : L ^ 2 * b ^ 3 ≤ L ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_left hb3 (sq_nonneg L)
  calc _ ≤ ‖avgCoeffHat Sig A z i μ 0‖ + ‖avgCoeffHat Sig A z i μ 0 - (hatAvg_Sh Sig A z μ +
        mFun N (specOf Sig) z * hatAvg_q Sig A z μ (fun j => A j μ))‖ +
        ‖mFun N (specOf Sig) z * hatAvg_q Sig A z μ (fun j => A j μ)‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ Ft Sig A z + (N : ℝ)⁻¹ * b + L ^ 2 * b ^ 2 + Cm * (L ^ 2 * b ^ 2) := by linarith
    _ = Ft Sig A z + (N : ℝ)⁻¹ * b + (L ^ 2 + Cm * L ^ 2) * b ^ 2 := by ring

/-- The column part: `|E 1_{Ξ_μ} (leading part)|` through `E = E^{(μ)} E_μ` (`integral_colSplit`),
with `|E_μ (leading part)| ≤ K_b (|Ŝ| + β²)^{p−2}` on the `X^{(μ)}`-measurable event and
`|Ŝ| ≤ F̃ + c₃ b²` on the a priori event `Ξ`. -/
private theorem hatAvg_T1 {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) (p : ℕ) {β Kb c₃ b₀ PΞ : ℝ} (Ξ : Set Ω) (Env : Matrix (Fin M) (Fin N) ℝ → ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hKb : 0 ≤ Kb) (hc₃ : 0 ≤ c₃)
    (hmain : ∀ A, hatAvg_Good Sig A z μ β →
      ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(colLaw X μ)‖ ≤
        Kb * (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2))
    (hΞ : ∀ ω ∈ Ξ, hatAvg_Good Sig (X ω) z μ β ∧
      ‖hatAvg_Sh Sig (X ω) z μ‖ ≤ Ft Sig (X ω) z + c₃ * b₀ ^ 2)
    (hPΞ : (ℙ Ξᶜ).toReal ≤ PΞ)
    (hEnvI : Integrable fun ω => Env (X ω)) (hEnv0 : ∀ A, 0 ≤ Env A)
    (hEnv : ∀ A, hatAvg_Good Sig A z μ β → ‖hatAvg_Lead Sig A z i μ p (fun j => A j μ)‖ ≤ Env A)
    (hFtI : Integrable fun ω => (Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2) ^ (p - 2)) :
    ‖∫ ω, (if hatAvg_Good Sig (X ω) z μ β then
        hatAvg_Lead Sig (X ω) z i μ p (fun j => X ω j μ) else 0)‖ ≤
      Kb * (∫ ω, (Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2) ^ (p - 2)) + Kb * 2 ^ p * PΞ := by
  set F₁ : Matrix (Fin M) (Fin N) ℝ → ℂ := fun A =>
    if hatAvg_Good Sig A z μ β then hatAvg_Lead Sig A z i μ p (fun j => A j μ) else 0 with hF₁
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  have hGm := hatAvg_meas_Good (N := N) hSig hz μ β
  have hF₁m : Measurable F₁ :=
    Measurable.ite hGm (hatAvg_cont_Lead hSig hz i μ p).measurable measurable_const
  have hF₁i : Integrable fun ω => F₁ (X ω) := by
    refine hEnvI.mono' (hF₁m.comp hXm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [hF₁]
    split_ifs with h
    · exact hEnv _ h
    · rw [norm_zero]; exact hEnv0 _
  have hsplit := integral_colSplit hX μ hF₁m hF₁i
  set B₁ : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A =>
    if hatAvg_Good Sig A z μ β then Kb * (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2) else 0
    with hB₁
  have hpt : ∀ A, ‖∫ y, F₁ (updCol A μ y) ∂(colLaw X μ)‖ ≤ B₁ A := by
    intro A
    by_cases hA : hatAvg_Good Sig A z μ β
    · have e1 : (fun y => F₁ (updCol A μ y)) = fun y => hatAvg_Lead Sig A z i μ p y := by
        funext y
        simp only [hF₁, hatAvg_Good_updCol, hA, ite_true]
        exact hatAvg_Lead_updCol Sig A z i μ p y
      rw [e1]; simp only [hB₁, hA, ite_true]; exact hmain A hA
    · have e1 : (fun y => F₁ (updCol A μ y)) = fun _ => 0 := by
        funext y; simp only [hF₁, hatAvg_Good_updCol, hA, ite_false]
      rw [e1]; simp [hB₁, hA]
  have hSc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hatAvg_Sh Sig A z μ :=
    continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      (hatAvg_cont_Gmu hSig hz μ _ _).sub continuous_const)
  have hB₁m : Measurable fun ω => B₁ (X ω) := by
    have h : Measurable B₁ := by
      refine Measurable.ite hGm ?_ measurable_const
      exact (continuous_const.mul ((hSc.norm.add continuous_const).pow _)).measurable
    exact h.comp hXm
  have hB₁b : ∀ A, B₁ A ≤ Kb * 2 ^ p := by
    intro A
    simp only [hB₁]
    split_ifs with hA
    · have hS := hatAvg_Sh_good hA hβ0
      have h1 : ‖hatAvg_Sh Sig A z μ‖ + β ^ 2 ≤ 2 := by
        have : β ^ 2 ≤ 1 := pow_le_one₀ hβ0 hβ1
        linarith
      have h2 : (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2) ≤ 2 ^ p :=
        (pow_le_pow_left₀ (by positivity) h1 _).trans
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le p 2))
      exact mul_le_mul_of_nonneg_left h2 hKb
    · positivity
  have hB₁0 : ∀ A, 0 ≤ B₁ A := fun A => by simp only [hB₁]; split_ifs <;> positivity
  have hB₁i : Integrable fun ω => B₁ (X ω) :=
    (integrable_const (Kb * 2 ^ p)).mono' hB₁m.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hB₁0 _)]; exact hB₁b _)
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  set Gf : Ω → ℝ := fun ω => Kb * (Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2) ^ (p - 2) +
    Kb * 2 ^ p * Bs.indicator (fun _ => (1 : ℝ)) ω with hGf
  have hF0 : ∀ ω, 0 ≤ Ft Sig (X ω) z := fun ω => norm_nonneg _
  have hle : ∀ ω, B₁ (X ω) ≤ Gf ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => (1 : ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hfirst : 0 ≤ Kb * (Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2) ^ (p - 2) := by
      have := hF0 ω; positivity
    by_cases hω : ω ∈ Ξ
    · obtain ⟨hG, hS⟩ := hΞ ω hω
      simp only [hB₁, hG, ite_true, hGf]
      have h1 : ‖hatAvg_Sh Sig (X ω) z μ‖ + β ^ 2 ≤ Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2 := by
        linarith
      have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 (p - 2)) hKb
      have h3 : 0 ≤ Kb * 2 ^ p * Bs.indicator (fun _ => (1 : ℝ)) ω := by positivity
      linarith
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [hGf]
      simp only [Set.indicator_of_mem hmem, mul_one]
      exact (hB₁b _).trans (le_add_of_nonneg_left hfirst)
  have hGfi : Integrable Gf :=
    (hFtI.const_mul _).add
      (((integrable_const _).indicator (measurableSet_toMeasurable _ _)).const_mul _)
  have hGfv : ∫ ω, Gf ω = Kb * (∫ ω, (Ft Sig (X ω) z + c₃ * b₀ ^ 2 + β ^ 2) ^ (p - 2)) +
      Kb * 2 ^ p * (ℙ Ξᶜ).toReal := by
    rw [hGf, integral_add (hFtI.const_mul _)
      (((integrable_const _).indicator (measurableSet_toMeasurable _ _)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable, smul_eq_mul, mul_one]
  calc ‖∫ ω, F₁ (X ω)‖ = ‖∫ ω, ∫ y, F₁ (updCol (X ω) μ y) ∂(colLaw X μ)‖ := by rw [hsplit]
    _ ≤ ∫ ω, ‖∫ y, F₁ (updCol (X ω) μ y) ∂(colLaw X μ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, B₁ (X ω) := integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hB₁i
        (ae_of_all _ fun ω => hpt _)
    _ ≤ ∫ ω, Gf ω := integral_mono hB₁i hGfi hle
    _ = _ := hGfv
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hPΞ (by positivity))

/-- `a² ≤ 2 b² + 2 c²` for `0 ≤ a ≤ b + c`. -/
private theorem hatAvg_sq_le_two {a b c : ℝ} (ha : 0 ≤ a) (h : a ≤ b + c) :
    a ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by
  have h1 : a ^ 2 ≤ (b + c) ^ 2 := pow_le_pow_left₀ ha h 2
  nlinarith [sq_nonneg (b - c)]

/-- The exponent count of the column part: `K N⁻¹ N^{−1/2} β² (x + c₃ b² + β²)^{p−2} ≤
N^{−1/2} K c₂² (1 + L)² 2^p c₅^p (x^p + b^{2p})`, `β = (1 + L) b`, `c₅ = 1 + c₃ + (1 + L)²`. -/
private theorem hatAvg_conv1 {p : ℕ} (hp : 2 ≤ p) {K c₂ c₃ L b x ε Ni : ℝ} (hK : 0 ≤ K)
    (hc₃ : 0 ≤ c₃) (hL : 0 ≤ L) (hx : 0 ≤ x) (hε : 0 ≤ ε) (hNi : Ni ≤ c₂ ^ 2 * b ^ 2) :
    K * (Ni * (ε * ((1 + L) * b) ^ 2)) * (x + c₃ * b ^ 2 + ((1 + L) * b) ^ 2) ^ (p - 2) ≤
      ε * (K * c₂ ^ 2 * (1 + L) ^ 2 * 2 ^ p * (1 + c₃ + (1 + L) ^ 2) ^ p *
        (x ^ p + (b ^ 2) ^ p)) := by
  set c₅ := 1 + c₃ + (1 + L) ^ 2 with hc₅
  have hc₅1 : 1 ≤ c₅ := by have := sq_nonneg (1 + L); linarith
  set Y := x + c₅ * b ^ 2 with hY
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hY0 : 0 ≤ Y := by positivity
  have hbY : b ^ 2 ≤ Y := by
    have : b ^ 2 ≤ c₅ * b ^ 2 := le_mul_of_one_le_left hb2 hc₅1
    linarith
  have hYe : x + c₃ * b ^ 2 + ((1 + L) * b) ^ 2 ≤ Y := by
    have e : x + c₃ * b ^ 2 + ((1 + L) * b) ^ 2 = x + (c₃ + (1 + L) ^ 2) * b ^ 2 := by ring
    rw [e, hY]
    have : (c₃ + (1 + L) ^ 2) * b ^ 2 ≤ c₅ * b ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hb2
    linarith
  have h1 : Ni * (ε * ((1 + L) * b) ^ 2) ≤ ε * (c₂ ^ 2 * (1 + L) ^ 2) * (b ^ 2) ^ 2 := by
    calc Ni * (ε * ((1 + L) * b) ^ 2) ≤ (c₂ ^ 2 * b ^ 2) * (ε * ((1 + L) * b) ^ 2) :=
          mul_le_mul_of_nonneg_right hNi (by positivity)
      _ = ε * (c₂ ^ 2 * (1 + L) ^ 2) * (b ^ 2) ^ 2 := by ring
  have h2 : (x + c₃ * b ^ 2 + ((1 + L) * b) ^ 2) ^ (p - 2) ≤ Y ^ (p - 2) :=
    pow_le_pow_left₀ (by positivity) hYe _
  have h3 : (b ^ 2) ^ 2 * Y ^ (p - 2) ≤ Y ^ p := by
    calc (b ^ 2) ^ 2 * Y ^ (p - 2) ≤ Y ^ 2 * Y ^ (p - 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb2 hbY 2) (by positivity)
      _ = Y ^ p := by rw [← pow_add]; congr 1; omega
  have h4 : Y ^ p ≤ 2 ^ p * c₅ ^ p * (x ^ p + (b ^ 2) ^ p) := by
    have h5 := hatAvg_pow_add_le hx (by positivity : 0 ≤ c₅ * b ^ 2) p
    have h6 : x ^ p ≤ c₅ ^ p * x ^ p := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc₅1)
    calc Y ^ p ≤ 2 ^ p * (x ^ p + (c₅ * b ^ 2) ^ p) := h5
      _ = 2 ^ p * (x ^ p + c₅ ^ p * (b ^ 2) ^ p) := by rw [mul_pow]
      _ ≤ 2 ^ p * (c₅ ^ p * x ^ p + c₅ ^ p * (b ^ 2) ^ p) := by gcongr
      _ = 2 ^ p * c₅ ^ p * (x ^ p + (b ^ 2) ^ p) := by ring
  calc K * (Ni * (ε * ((1 + L) * b) ^ 2)) * (x + c₃ * b ^ 2 + ((1 + L) * b) ^ 2) ^ (p - 2)
      ≤ K * (ε * (c₂ ^ 2 * (1 + L) ^ 2) * (b ^ 2) ^ 2) * Y ^ (p - 2) := by gcongr
    _ = K * ε * (c₂ ^ 2 * (1 + L) ^ 2) * ((b ^ 2) ^ 2 * Y ^ (p - 2)) := by ring
    _ ≤ K * ε * (c₂ ^ 2 * (1 + L) ^ 2) * (2 ^ p * c₅ ^ p * (x ^ p + (b ^ 2) ^ p)) := by
        exact mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = _ := by ring

/-- (avg_pf_claim) for `n = 3`, the removal of `ν = μ`, at one `(i, μ)`: the leading part through
the column expectation, the rest on the a priori event `Ξ`, and the complement of `Ξ` through
the rough bounds. -/
private theorem hatAvg_per {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) {p : ℕ} (hp : 2 ≤ p) {τ b₀ L Cm KP c₂ R KL s PΞ : ℝ} (Ξ : Set Ω)
    (hτ : 0 < τ) (hM : (M : ℝ) ≤ τ⁻¹ * N) (hb₀1 : b₀ ≤ 1) (hL : 0 ≤ L) (hCm : 0 ≤ Cm)
    (hKP : 0 ≤ KP) (hc₂ : 0 ≤ c₂) (hβ0 : 0 < (1 + L) * b₀) (hβ2 : 2 * ((1 + L) * b₀) ^ 2 ≤ 1)
    (hR0 : 0 ≤ R) (hKL : 0 ≤ KL) (hs : 0 < s)
    (hKLp : ∀ (A : Matrix (Fin M) (Fin N) ℝ) (ρ : Fin M → Measure ℝ)
      [∀ j, IsProbabilityMeasure (ρ j)], (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ (1 + L) * b₀ ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ (1 + L) * b₀) →
      ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ KP + 1 →
      ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(Measure.pi ρ)‖ ≤
        KL * (1 + Cm) ^ (p + 2) * (KP + 1) * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ *
          (((1 + L) * b₀) ^ 2 * (‖hatAvg_Sh Sig A z μ‖ + ((1 + L) * b₀) ^ 2) ^ (p - 2)))))
    (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP)
    (hNb : (Real.sqrt N)⁻¹ ≤ c₂ * b₀) (hR : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t,
      ‖G Sig A z s t‖ ≤ R)
    (hΞ : ∀ ω ∈ Ξ, (∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀) ∧
      1 ≤ L * ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)‖)
    (hPΞ : (ℙ Ξᶜ).toReal ≤ PΞ) :
    ‖∫ ω, (fCoeff p (avgCoeff Sig (X ω) z i μ) 3 - fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3)‖ ≤
      (Real.sqrt N)⁻¹ * (2 ^ p * (hatAvg_K0 p L Cm KP c₂ + KL * (1 + Cm) ^ (p + 2) * (KP + 1) *
          c₂ ^ 2 * (1 + L) ^ 2 * (1 + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) + (1 + L) ^ 2) ^ p) *
        ((∫ ω, Ft Sig (X ω) z ^ p) + (b₀ ^ 2) ^ p)) +
      s * (2 * (2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p)) ^ 2 +
        2 * (4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) * (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p) ^ 2 *
          (1 + (M : ℝ)) ^ (4 * p) * (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p))) +
      PΞ * (4 * s)⁻¹ + KL * (1 + Cm) ^ (p + 2) * (KP + 1) * 2 ^ p * PΞ := by
  have hN1 : 1 ≤ N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hb₀ : 0 < b₀ := by
    by_contra h
    have h' : b₀ ≤ 0 := le_of_not_gt h
    have : (1 + L) * b₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h'
    linarith
  set β := (1 + L) * b₀ with hβdef
  have hβ1 : β ≤ 1 := by nlinarith
  set ε := (Real.sqrt N)⁻¹ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hNε : (N : ℝ)⁻¹ = ε ^ 2 := by rw [hε, inv_pow, Real.sq_sqrt hNr.le]
  have hNi : (N : ℝ)⁻¹ ≤ c₂ ^ 2 * b₀ ^ 2 := by
    rw [hNε, ← mul_pow]; exact pow_le_pow_left₀ hε0 hNb 2
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  set F : Ω → ℝ := fun ω => Ft Sig (X ω) z with hF
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => norm_nonneg _
  have hFle : ∀ ω, F ω ≤ R + Cm := fun ω => hatAvg_Ft_le (X ω) hN1 (hR (X ω)) hm
  have hFm : Measurable F := (((measurable_mN Sig z).comp hXm).sub_const _).norm
  have hbdd : ∀ (c : ℝ) (q : ℕ), 0 ≤ c → Integrable fun ω => (F ω + c) ^ q := by
    intro c q hc
    refine (integrable_const ((R + Cm + c) ^ q)).mono'
      ((hFm.add_const c).pow_const q).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by have := hF0 ω; positivity)]
    exact pow_le_pow_left₀ (by have := hF0 ω; positivity) (by linarith [hFle ω]) q
  have hFpI : Integrable fun ω => F ω ^ p := by
    simpa using hbdd 0 p le_rfl
  -- the two parts
  set D : Matrix (Fin M) (Fin N) ℝ → ℂ := fun A =>
    fCoeff p (avgCoeff Sig A z i μ) 3 - fCoeff p (avgCoeffHat Sig A z i μ) 3 with hD
  set F₁ : Matrix (Fin M) (Fin N) ℝ → ℂ := fun A =>
    if hatAvg_Good Sig A z μ β then hatAvg_Lead Sig A z i μ p (fun j => A j μ) else 0 with hF₁
  set RD := 2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p) with hRD
  set RL := 4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) * (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p with hRL
  have hRD0 : 0 ≤ RD := by positivity
  have hRL0 : 0 ≤ RL := by positivity
  set Env : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A =>
    RL * ((1 + (M : ℝ)) ^ (2 * p) * (1 + hatAvg_sq A) ^ (2 * p)) with hEnv
  have hEnv0 : ∀ A, 0 ≤ Env A := fun A => by
    have := hatAvg_sq_nonneg A; simp only [hEnv]; positivity
  have hDm : Measurable D := (hatAvg_cont_D hSig hz i μ p).measurable
  have hDb : ∀ A, ‖D A‖ ≤ RD := fun A => hatAvg_D_rough hSig A hz i μ p hR0 hKP (hR A) hPi
  have hLeadb : ∀ A, hatAvg_Good Sig A z μ β →
      ‖hatAvg_Lead Sig A z i μ p (fun j => A j μ)‖ ≤ Env A := by
    intro A hA
    refine (hatAvg_Lead_rough A i μ p hβ0.le hβ1 hKP hCm hA hPi hm).trans ?_
    have hV := hatAvg_V_le A μ
    have hV0 := hatAvg_V_nonneg A μ
    have e : (2 * (1 + Cm) * (KP + 1) ^ 2 * (1 + hatAvg_V A μ) ^ 2) ^ p =
        (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p * (1 + hatAvg_V A μ) ^ (2 * p) := by
      rw [mul_pow, ← pow_mul]
    rw [e, ← mul_assoc]
    simp only [hEnv, hRL]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hV _
  have hF₁b : ∀ A, ‖F₁ A‖ ≤ Env A := fun A => by
    simp only [hF₁]; split_ifs with h
    · exact hLeadb A h
    · rw [norm_zero]; exact hEnv0 A
  have hGm := hatAvg_meas_Good (N := N) hSig hz μ β
  have hF₁m : Measurable F₁ :=
    Measurable.ite hGm (hatAvg_cont_Lead hSig hz i μ p).measurable measurable_const
  have hmom2 := hatAvg_moment hτ hX hN1 hM (2 * p)
  have hmom4 := hatAvg_moment hτ hX hN1 hM (4 * p)
  have hEnvI : Integrable fun ω => Env (X ω) :=
    (hmom2.1.const_mul _).const_mul _
  have hDi : Integrable fun ω => D (X ω) :=
    (integrable_const RD).mono' (hDm.comp hXm).aestronglyMeasurable
      (ae_of_all _ fun ω => hDb _)
  have hF₁i : Integrable fun ω => F₁ (X ω) :=
    hEnvI.mono' (hF₁m.comp hXm).aestronglyMeasurable (ae_of_all _ fun ω => hF₁b _)
  -- the event facts
  have hc₃ : 0 ≤ c₂ ^ 2 + L ^ 2 + Cm * L ^ 2 := by positivity
  have hΞ' : ∀ ω ∈ Ξ, hatAvg_Good Sig (X ω) z μ β ∧
      ‖hatAvg_Sh Sig (X ω) z μ‖ ≤ Ft Sig (X ω) z + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 := by
    intro ω hω
    obtain ⟨hG, hμ⟩ := hΞ ω hω
    refine ⟨minor_entry_bound hSig (X ω) hz μ hb₀.le hb₀1 hL hG hμ, ?_⟩
    have h1 := hatAvg_Sh_event hSig (X ω) hz i μ hb₀.le hb₀1 hL hCm hG hμ hm
    have h2 : (N : ℝ)⁻¹ * b₀ ≤ c₂ ^ 2 * b₀ ^ 2 :=
      (mul_le_of_le_one_right (by positivity) hb₀1).trans hNi
    have e : (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 = c₂ ^ 2 * b₀ ^ 2 +
        (L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 := by ring
    linarith
  -- the column part
  have hmain : ∀ A, hatAvg_Good Sig A z μ β →
      ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(colLaw X μ)‖ ≤
        (KL * (1 + Cm) ^ (p + 2) * (KP + 1) * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2))) *
          (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2) := by
    intro A hA
    have : ∀ j, IsProbabilityMeasure (entryLaw X (j, μ)) := fun j =>
      (hatAvg_colLaw hX μ hN1 j).1
    obtain ⟨hK, hGν⟩ := hatAvg_good_entries hA hβ0.le hPi
    have h := hKLp A (fun j => entryLaw X (j, μ)) (fun j => (hatAvg_colLaw hX μ hN1 j).2.1)
      (fun j n => (hatAvg_colLaw hX μ hN1 j).2.2 n) hGν ((hK _ _).trans (by linarith))
    refine h.trans (le_of_eq ?_)
    ring
  have hKb : 0 ≤ KL * (1 + Cm) ^ (p + 2) * (KP + 1) * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) := by
    positivity
  have hI3 : Integrable fun ω =>
      (Ft Sig (X ω) z + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 + β ^ 2) ^ (p - 2) := by
    have h := hbdd ((c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 + β ^ 2) (p - 2) (by positivity)
    simpa only [hF, add_assoc] using h
  have hT1 := hatAvg_T1 hX hSig hz i μ p Ξ Env hβ0.le hβ1 hKb hc₃ hmain hΞ' hPΞ hEnvI hEnv0
    hLeadb hI3
  -- the rest on the a priori event and off it
  set f : Ω → ℂ := fun ω => D (X ω) - F₁ (X ω) with hf
  set g : Ω → ℝ := fun ω => ε * (hatAvg_K0 p L Cm KP c₂ * (F ω + b₀ ^ 2) ^ p) with hg
  have hK00 : 0 ≤ hatAvg_K0 p L Cm KP c₂ := by unfold hatAvg_K0 hatAvg_CB; positivity
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by have := hF0 ω; simp only [hg]; positivity
  have hgi : Integrable g := ((hbdd _ p (by positivity)).const_mul _).const_mul _
  have hon : ∀ ω ∈ Ξ, ‖f ω‖ ≤ g ω := by
    intro ω hω
    obtain ⟨hG, hμ⟩ := hΞ ω hω
    have hGood := (hΞ' ω hω).1
    simp only [hf, hF₁, hGood, ite_true, hD, hg]
    exact hatAvg_point hSig (X ω) hz i μ hp hb₀1 hL hCm hKP hc₂ hG hμ hm hPi hNb
  have hfi : Integrable f := hDi.sub hF₁i
  have hfb : ∀ ω, ‖f ω‖ ^ 2 ≤ 2 * RD ^ 2 + 2 * Env (X ω) ^ 2 := by
    intro ω
    have h1 : ‖f ω‖ ≤ RD + Env (X ω) := (norm_sub_le _ _).trans (add_le_add (hDb _) (hF₁b _))
    exact hatAvg_sq_le_two (norm_nonneg _) h1
  have hEnv2 : ∀ ω, Env (X ω) ^ 2 = RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) *
      (1 + hatAvg_sq (X ω)) ^ (4 * p) := by
    intro ω
    simp only [hEnv]
    rw [show 4 * p = 2 * p + 2 * p by ring, pow_add, pow_add]
    ring
  have hE2i : Integrable fun ω => 2 * RD ^ 2 + 2 * Env (X ω) ^ 2 := by
    simp only [hEnv2]
    exact (integrable_const _).add ((hmom4.1.const_mul _).const_mul _)
  have hf2i : Integrable fun ω => ‖f ω‖ ^ 2 :=
    hE2i.mono' (hfi.1.norm.pow 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hfb ω)
  have hf2 : ∫ ω, ‖f ω‖ ^ 2 ≤ 2 * RD ^ 2 + 2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) *
      (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p)) := by
    refine (integral_mono hf2i hE2i hfb).trans ?_
    have e : ∫ ω, (2 * RD ^ 2 + 2 * Env (X ω) ^ 2) = 2 * RD ^ 2 +
        2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) * ∫ ω, (1 + hatAvg_sq (X ω)) ^ (4 * p) := by
      have hpt : ∀ ω, 2 * RD ^ 2 + 2 * Env (X ω) ^ 2 = 2 * RD ^ 2 +
          (2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p)) * (1 + hatAvg_sq (X ω)) ^ (4 * p) := by
        intro ω; rw [hEnv2]; ring
      simp only [hpt]
      rw [integral_add (integrable_const _) (hmom4.1.const_mul _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [integral_const_mul]
    rw [e]
    have h0 : 0 ≤ 2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) := by positivity
    have := mul_le_mul_of_nonneg_left hmom4.2 h0
    linarith
  have hsplit := hatAvg_split hs hfi.norm hf2i hgi hg0 hon
  have hgv : ∫ ω, g ω ≤
      ε * (hatAvg_K0 p L Cm KP c₂ * (2 ^ p * ((∫ ω, F ω ^ p) + (b₀ ^ 2) ^ p))) := by
    simp only [hg]
    rw [integral_const_mul, integral_const_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK00) hε0
    have hpt : ∀ ω, (F ω + b₀ ^ 2) ^ p ≤ 2 ^ p * (F ω ^ p + (b₀ ^ 2) ^ p) := fun ω =>
      hatAvg_pow_add_le (hF0 ω) (sq_nonneg _) p
    refine (integral_mono (hbdd _ p (by positivity))
      ((hFpI.add (integrable_const _)).const_mul _) hpt).trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hFpI (integrable_const _)]
    simp
  -- the column part in the final form
  set c₅ := 1 + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) + (1 + L) ^ 2 with hc₅
  set K₅ := KL * (1 + Cm) ^ (p + 2) * (KP + 1) with hK₅
  have hK₅0 : 0 ≤ K₅ := by positivity
  have hT1v : K₅ * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) *
      (∫ ω, (Ft Sig (X ω) z + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 + β ^ 2) ^ (p - 2)) ≤
      ε * (K₅ * c₂ ^ 2 * (1 + L) ^ 2 * 2 ^ p * c₅ ^ p * ((∫ ω, F ω ^ p) + (b₀ ^ 2) ^ p)) := by
    rw [← integral_const_mul]
    have hpt : ∀ ω, K₅ * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) *
        (Ft Sig (X ω) z + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) * b₀ ^ 2 + β ^ 2) ^ (p - 2) ≤
        ε * (K₅ * c₂ ^ 2 * (1 + L) ^ 2 * 2 ^ p * c₅ ^ p * (F ω ^ p + (b₀ ^ 2) ^ p)) := by
      intro ω
      have h := hatAvg_conv1 hp hK₅0 hc₃ hL (hF0 ω) hε0 hNi
      simp only [hβdef, hF] at h ⊢
      refine h.trans (le_of_eq ?_)
      ring
    refine (integral_mono (hI3.const_mul _)
      (((hFpI.add (integrable_const _)).const_mul _).const_mul _) hpt).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hFpI (integrable_const _)]
    simp
  -- assembly
  have hsum : (fun ω => fCoeff p (avgCoeff Sig (X ω) z i μ) 3 -
      fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3) = fun ω => F₁ (X ω) + f ω := by
    funext ω; simp only [hf, hD]; ring
  rw [hsum, integral_add hF₁i hfi]
  refine (norm_add_le _ _).trans ?_
  have hPΞ0 : 0 ≤ (ℙ Ξᶜ).toReal := ENNReal.toReal_nonneg
  have hoff : (ℙ Ξᶜ).toReal * (4 * s)⁻¹ ≤ PΞ * (4 * s)⁻¹ :=
    mul_le_mul_of_nonneg_right hPΞ (by positivity)
  have hs2 : s * ∫ ω, ‖f ω‖ ^ 2 ≤ s * (2 * RD ^ 2 + 2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) *
      (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p))) := mul_le_mul_of_nonneg_left hf2 hs.le
  have hPΞ0' : 0 ≤ PΞ := le_trans ENNReal.toReal_nonneg hPΞ
  have hKbK : K₅ * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) * 2 ^ p * PΞ ≤ K₅ * 2 ^ p * PΞ := by
    have h1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN1)
    have h2 : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      rw [Real.one_le_sqrt]; exact_mod_cast hN1)
    have h3 : β ^ 2 ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have h4 : (N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2) ≤ 1 := by
      calc (N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2) ≤ 1 * (1 * 1) := by gcongr
        _ = 1 := by ring
    have h5 : 0 ≤ K₅ * 2 ^ p * PΞ := by positivity
    calc K₅ * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) * 2 ^ p * PΞ =
        ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ * β ^ 2)) * (K₅ * 2 ^ p * PΞ) := by ring
      _ ≤ 1 * (K₅ * 2 ^ p * PΞ) := mul_le_mul_of_nonneg_right h4 h5
      _ = K₅ * 2 ^ p * PΞ := one_mul _
  have hT1' := hT1.trans (add_le_add hT1v hKbK)
  have hc5p : 0 ≤ K₅ * c₂ ^ 2 * (1 + L) ^ 2 * 2 ^ p * c₅ ^ p := by positivity
  have hEF : 0 ≤ (∫ ω, F ω ^ p) + (b₀ ^ 2) ^ p := by
    have : 0 ≤ ∫ ω, F ω ^ p := integral_nonneg fun ω => pow_nonneg (hF0 ω) p
    positivity
  calc _ ≤ (ε * (K₅ * c₂ ^ 2 * (1 + L) ^ 2 * 2 ^ p * c₅ ^ p * ((∫ ω, F ω ^ p) + (b₀ ^ 2) ^ p)) +
        K₅ * 2 ^ p * PΞ) + (ε * (hatAvg_K0 p L Cm KP c₂ * (2 ^ p * ((∫ ω, F ω ^ p) +
          (b₀ ^ 2) ^ p))) + s * (2 * RD ^ 2 + 2 * RL ^ 2 * (1 + (M : ℝ)) ^ (4 * p) *
          (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p))) + PΞ * (4 * s)⁻¹) := by
        refine add_le_add hT1' (hsplit.trans ?_)
        linarith
    _ = _ := by simp only [hF, hK₅, hc₅]; ring

/-! ## The choice of `N₀` and the scalar conditions -/

/-- `dPrevTwo τ p ≤ D_a` gives `24p + 1 ≤ D_a − 3`. -/
private theorem hatAvg_D_ge {τ : ℝ} {p : ℕ} {Da : ℝ} (hDa : dPrevTwo τ p ≤ Da) :
    (24 * p + 1 : ℝ) ≤ Da - 3 := by
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk : (1 : ℝ) ≤ (kTau τ : ℝ) + 1 := by
    have := (Nat.cast_nonneg (kTau τ) : (0 : ℝ) ≤ _); linarith
  have h0 : 0 ≤ dPrev p := by unfold dPrev; positivity
  have h1 : dPrev p ≤ dPrevTwo τ p := by
    unfold dPrevTwo; exact le_mul_of_one_le_right h0 hk
  unfold dPrev at h1
  nlinarith

/-- Eventually `A ≤ N^{τ/16}`, `B ≤ N` and `2 ≤ N`. -/
private theorem hatAvg_large {τ : ℝ} (hτ : 0 < τ) (A B : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, A ≤ (N : ℝ) ^ (τ / 16) ∧ B ≤ N ∧ 2 ≤ N := by
  refine ⟨⌈max A 0 ^ (16 / τ)⌉₊ + ⌈B⌉₊ + 2, fun N hN => ⟨?_, ?_, by omega⟩⟩
  · have hA0 : 0 ≤ max A 0 := le_max_right _ _
    have h1 : max A 0 ^ (16 / τ) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈max A 0 ^ (16 / τ)⌉₊ ≤ N by omega))
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h1 (by positivity : 0 ≤ τ / 16)
    rw [← Real.rpow_mul hA0, show 16 / τ * (τ / 16) = 1 by field_simp, Real.rpow_one] at h2
    exact (le_max_left _ _).trans h2
  · exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈B⌉₊ ≤ N by omega))

/-- `N^{−3/2} = N⁻¹ N^{−1/2}`. -/
private theorem hatAvg_rpow_three_half {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) = (N : ℝ)⁻¹ * (Real.sqrt N)⁻¹ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← hatAvg_rpow_half, ← Real.rpow_neg_one, ← Real.rpow_add hNr]
  norm_num

/-- The scalar conditions at one `N ≥ N₀`, for `b = τ⁻² N^{ε_a} Ψ`: `b > 0`,
`2 (1 + 2 C_m) b ≤ 1` and `N^{−1/2} ≤ √C_m τ² b`. -/
private theorem hatAvg_scal {τ εa Cm Ψ : ℝ} {N : ℕ} (hτ : 0 < τ) (hεa : 0 < εa)
    (hεaτ : 16 * εa ≤ τ)
    (hCm : 0 < Cm) (hN2 : 2 ≤ N)
    (hNa : 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) ≤ (N : ℝ) ^ (τ / 16))
    (hΨge : τ / N ≤ Ψ) (hΨdec : Ψ ≤ (Real.sqrt Cm + 1) * (N : ℝ) ^ (-τ / 2))
    (hΨsq : (Cm * N)⁻¹ ≤ Ψ ^ 2) :
    0 < τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ ∧ 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) ≤ 1 ∧
      (Real.sqrt N)⁻¹ ≤ Real.sqrt Cm * τ ^ 2 * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hΨ0 : 0 < Ψ := lt_of_lt_of_le (by positivity) hΨge
  have hNe : 0 < (N : ℝ) ^ εa := Real.rpow_pos_of_pos hN0 _
  refine ⟨by positivity, ?_, ?_⟩
  · have h1 : (N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2) ≤ ((N : ℝ) ^ (τ / 16))⁻¹ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hNt : 0 < (N : ℝ) ^ (τ / 16) := Real.rpow_pos_of_pos hN0 _
    have hB : 0 ≤ 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) := by positivity
    calc 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ)
        ≤ 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa *
            ((Real.sqrt Cm + 1) * (N : ℝ) ^ (-τ / 2))) := by gcongr
      _ = 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) *
            ((N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2)) := by ring
      _ ≤ 2 * (1 + 2 * Cm) * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) * ((N : ℝ) ^ (τ / 16))⁻¹ :=
          mul_le_mul_of_nonneg_left h1 hB
      _ ≤ (N : ℝ) ^ (τ / 16) * ((N : ℝ) ^ (τ / 16))⁻¹ :=
          mul_le_mul_of_nonneg_right hNa (by positivity)
      _ = 1 := mul_inv_cancel₀ hNt.ne'
  · have h1 : (N : ℝ)⁻¹ ≤ Cm * Ψ ^ 2 := by
      have : (N : ℝ)⁻¹ = Cm * (Cm * N)⁻¹ := by field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left hΨsq hCm.le
    have h2 : (Real.sqrt N)⁻¹ ≤ Real.sqrt Cm * Ψ := by
      rw [← Real.sqrt_inv, ← Real.sqrt_sq hΨ0.le, ← Real.sqrt_mul hCm.le]
      exact Real.sqrt_le_sqrt h1
    have h3 : Ψ ≤ τ ^ 2 * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) := by
      have e : τ ^ 2 * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) = (N : ℝ) ^ εa * Ψ := by
        field_simp
      rw [e]
      exact le_mul_of_one_le_left hΨ0.le (Real.one_le_rpow hN1 hεa.le)
    calc (Real.sqrt N)⁻¹ ≤ Real.sqrt Cm * Ψ := h2
      _ ≤ Real.sqrt Cm * (τ ^ 2 * (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ)) :=
          mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- The off-event terms: with `s = N^{−(2p+2)} N^{−(8p+1)}`, `P(Ξᶜ) ≤ N^{−(24p+1)}`,
`T ≤ N^{8p+1}` and `K 2^p ≤ N`: `s T + P(Ξᶜ)/(4s) + K 2^p P(Ξᶜ) ≤ 3 N^{−(2p+2)}`. -/
private theorem hatAvg_tiny {N p : ℕ} (hN1 : 1 ≤ N) (hp : 1 ≤ p) {T K PΞ : ℝ}
    (hT : T ≤ (N : ℝ) ^ (8 * p + 1)) (hK : K * 2 ^ p ≤ N) (hPΞ0 : 0 ≤ PΞ)
    (hPΞ : PΞ ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹) :
    ((N : ℝ) ^ (2 * p + 2) * (N : ℝ) ^ (8 * p + 1))⁻¹ * T +
      PΞ * (4 * ((N : ℝ) ^ (2 * p + 2) * (N : ℝ) ^ (8 * p + 1))⁻¹)⁻¹ + K * 2 ^ p * PΞ ≤
      3 * ((N : ℝ) ^ (2 * p + 2))⁻¹ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (2 * p + 2) with hx
  set y := (N : ℝ) ^ (8 * p + 1) with hy
  have hx0 : 0 < x := pow_pos hN0 _
  have hy0 : 0 < y := pow_pos hN0 _
  have hZ0 : 0 < (N : ℝ) ^ (24 * p + 1) := pow_pos hN0 _
  have t1 : (x * y)⁻¹ * T ≤ x⁻¹ := by
    calc (x * y)⁻¹ * T ≤ (x * y)⁻¹ * y := mul_le_mul_of_nonneg_left hT (by positivity)
      _ = x⁻¹ := by field_simp
  have hxyx : x * y * x ≤ (N : ℝ) ^ (24 * p + 1) := by
    rw [hx, hy, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hNr (by omega)
  have h1 : PΞ * (x * y * x) ≤ 1 := by
    calc PΞ * (x * y * x) ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹ * (N : ℝ) ^ (24 * p + 1) :=
          mul_le_mul hPΞ hxyx (by positivity) (by positivity)
      _ = 1 := inv_mul_cancel₀ hZ0.ne'
  have t2 : PΞ * (4 * (x * y)⁻¹)⁻¹ ≤ x⁻¹ := by
    have e : PΞ * (4 * (x * y)⁻¹)⁻¹ = PΞ * (x * y * x) / (4 * x) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : x⁻¹ * (4 * x) = 4 := by field_simp
    rw [this]
    linarith
  have t3 : K * 2 ^ p * PΞ ≤ x⁻¹ := by
    have h2 : K * 2 ^ p * PΞ ≤ N * ((N : ℝ) ^ (24 * p + 1))⁻¹ :=
      mul_le_mul hK hPΞ hPΞ0 (by positivity)
    have e : (N : ℝ) * ((N : ℝ) ^ (24 * p + 1))⁻¹ = ((N : ℝ) ^ (24 * p))⁻¹ := by
      rw [pow_succ]; field_simp
    have h3 : ((N : ℝ) ^ (24 * p))⁻¹ ≤ x⁻¹ :=
      inv_anti₀ hx0 (by rw [hx]; exact pow_le_pow_right₀ hNr (by omega))
    linarith
  linarith

/-- The rough constant of the leading part. -/
private def hatAvg_RL (p : ℕ) (Cm KP : ℝ) : ℝ :=
  4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) * (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p

/-- The moment constant of the complement of the a priori event. -/
private def hatAvg_Cf (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (Cm KP : ℝ) : ℝ :=
  8 * (4 ^ p * (8 * ((1 + 10 * τ⁻¹) * τ⁻¹ + KP + 1) ^ 4) ^ p) ^ 2 +
    2 * hatAvg_RL p Cm KP ^ 2 * (1 + τ⁻¹) ^ (4 * p) * hatAvg_KS τ C (4 * p)

/-- The constant of (avg_pf_claim), removal of `ν = μ`, at one `(i, μ)`. -/
private def hatAvg_K3 (p : ℕ) (L Cm KP c₂ KL : ℝ) : ℝ :=
  2 ^ p * (hatAvg_K0 p L Cm KP c₂ + KL * (1 + Cm) ^ (p + 2) * (KP + 1) * c₂ ^ 2 * (1 + L) ^ 2 *
    (1 + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) + (1 + L) ^ 2) ^ p)

/-- `f_3(a)` and `f_3(â)` are integrable: deterministic bounds from `|G_{st}| ≤ R`. -/
private theorem hatAvg_f_int {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) (p : ℕ) {R KP : ℝ} (hR0 : 0 ≤ R) (hKP : 0 ≤ KP)
    (hR : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t, ‖G Sig A z s t‖ ≤ R)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    Integrable (fun ω => fCoeff p (avgCoeff Sig (X ω) z i μ) 3) ∧
      Integrable (fun ω => fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3) := by
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  have hB1 : 1 ≤ R + KP + 1 := by linarith
  have hres : ∀ (A : Matrix (Fin M) (Fin N) ℝ) (ν : Fin N) (k : ℕ),
      ‖resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤ 2 ^ k * (R + KP + 1) ^ (k + 1) := by
    intro A ν k
    have h0 : Fv Sig A z (eI (Sum.inr ν)) ≤ R + KP + 1 := by
      unfold Fv
      rw [hatAvg_vbar_inr, ent_eI_eI, Matrix.sub_apply]
      have := norm_sub_le (G Sig A z (Sum.inr ν) (Sum.inr ν)) (PiZ N Sig z (Sum.inr ν) (Sum.inr ν))
      linarith [hR A (Sum.inr ν) (Sum.inr ν), hPi (Sum.inr ν) (Sum.inr ν)]
    have h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig (eI (Sum.inr ν))) (eI (letterT i μ b))‖ ≤
        R + KP + 1 := fun b => by
      rw [hatAvg_vbar_inr, ent_eI_eI]; linarith [hR A (Sum.inr ν) (letterT i μ b)]
    have h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig (eI (Sum.inr ν)))‖ ≤
        R + KP + 1 := fun b => by
      rw [hatAvg_vbar_inr, ent_eI_eI]; linarith [hR A (letterS i μ b) (Sum.inr ν)]
    have h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ R + KP + 1 :=
      fun b b' => by linarith [hR A (letterS i μ b) (letterT i μ b')]
    exact norm_resCoeff_le hSig A hz _ i μ h0 h1 h2 h3 k
  have havg : ∀ (A : Matrix (Fin M) (Fin N) ℝ) (s : Finset (Fin N)) (k : ℕ),
      ‖(N : ℂ)⁻¹ * ∑ ν ∈ s, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤
        2 ^ k * (R + KP + 1) ^ (k + 1) := by
    intro A s k
    have hN : 0 < N := Fin.pos μ
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ ν ∈ s, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖
        ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, 2 ^ k * (R + KP + 1) ^ (k + 1) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
          exact (Finset.sum_le_sum fun ν _ => hres A ν k).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun _ _ _ => by positivity)
      _ = 2 ^ k * (R + KP + 1) ^ (k + 1) := by simp; field_simp
  have hY : ∀ k ≤ 3, (2 : ℝ) ^ k * (R + KP + 1) ^ (k + 1) ≤ 8 * (R + KP + 1) ^ 4 := by
    intro k hk
    exact mul_le_mul (by calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
      _ = 8 := by norm_num) (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by norm_num)
  have hf1 : ∀ A : Matrix (Fin M) (Fin N) ℝ, ‖fCoeff p (avgCoeff Sig A z i μ) 3‖ ≤
      ((3 : ℕ) + 1 : ℝ) ^ p * (8 * (R + KP + 1) ^ 4) ^ p := fun A =>
    hatAvg_fCoeff_le p (by positivity) 3 fun k hk => (havg A Finset.univ k).trans (hY k hk)
  have hf2 : ∀ A : Matrix (Fin M) (Fin N) ℝ, ‖fCoeff p (avgCoeffHat Sig A z i μ) 3‖ ≤
      ((3 : ℕ) + 1 : ℝ) ^ p * (8 * (R + KP + 1) ^ 4) ^ p := fun A =>
    hatAvg_fCoeff_le p (by positivity) 3 fun k hk => (havg A _ k).trans (hY k hk)
  have hc : ∀ (a : Matrix (Fin M) (Fin N) ℝ → ℕ → ℂ), (∀ k, Continuous fun A => a A k) →
      Continuous fun A => fCoeff p (a A) 3 := by
    intro a ha
    unfold fCoeff
    refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
    split_ifs
    · exact ha _
    · exact Complex.continuous_conj.comp (ha _)
  have hc1 : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => fCoeff p (avgCoeff Sig A z i μ) 3 :=
    hc _ fun k => continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      hatAvg_cont_resCoeff hSig hz _ i μ k)
  have hc2 : Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      fCoeff p (avgCoeffHat Sig A z i μ) 3 :=
    hc _ fun k => continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      hatAvg_cont_resCoeff hSig hz _ i μ k)
  exact ⟨(integrable_const _).mono' (hc1.measurable.comp hXm).aestronglyMeasurable
      (ae_of_all _ fun ω => hf1 _),
    (integrable_const _).mono' (hc2.measurable.comp hXm).aestronglyMeasurable
      (ae_of_all _ fun ω => hf2 _)⟩

/-- The sum over `(i, μ)` and the final normalization: from
`∑_{i, μ} |E(f_3(a) − f_3(â))| ≤ M N (N^{−1/2} K₃ (E F̃^p + b^{2p}) + 3 N^{−(2p+2)})`,
`b = τ⁻² N^{ε_a} Ψ`, `Ψ ≥ τ/N`, `2ε_a ≤ δ` and `M/N ≤ τ⁻¹`:
`N^{−3/2} ∑ ≤ (τ⁻¹ K₃ (1 + τ^{−4p}) + 3 τ^{−2p−1}) ((N^δ Ψ²)^p + E F̃^p)`. -/
private theorem hatAvg_sumfinal {M N p : ℕ} (hN : 0 < N) {τ K₃ EF Ψ δ εa S : ℝ}
    (hτ : 0 < τ) (hK₃ : 0 ≤ K₃) (hEF : 0 ≤ EF) (hΨge : τ / N ≤ Ψ) (hεa : 0 < εa)
    (h2εa : 2 * εa ≤ δ) (hMN : (M : ℝ) / N ≤ τ⁻¹)
    (hS : S ≤ (M : ℝ) * N * ((Real.sqrt N)⁻¹ *
      (K₃ * (EF + ((τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) ^ 2) ^ p)) +
      3 * ((N : ℝ) ^ (2 * p + 2))⁻¹)) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * S ≤ (τ⁻¹ * K₃ * (1 + τ⁻¹ ^ (4 * p)) + 3 * τ⁻¹ ^ (2 * p + 1)) *
      (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + EF) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ε := (Real.sqrt N)⁻¹ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact hNr)
  have hεsq : ε ^ 2 = (N : ℝ)⁻¹ := by rw [hε, inv_pow, Real.sq_sqrt hN0.le]
  set b₀ := τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ with hb₀
  set Y := ((N : ℝ) ^ δ * Ψ ^ 2) ^ p with hY
  have hNδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hNr (by linarith)
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨge
  have hY0 : 0 ≤ Y := by positivity
  have hb2 : (b₀ ^ 2) ^ p ≤ τ⁻¹ ^ (4 * p) * Y := by
    have h2ε : (N : ℝ) ^ εa * (N : ℝ) ^ εa ≤ (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have : b₀ ^ 2 ≤ τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2) := by
      calc b₀ ^ 2 = τ⁻¹ ^ 4 * ((N : ℝ) ^ εa * (N : ℝ) ^ εa) * Ψ ^ 2 := by rw [hb₀]; ring
        _ ≤ τ⁻¹ ^ 4 * (N : ℝ) ^ δ * Ψ ^ 2 := by gcongr
        _ = τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2) := by ring
    calc (b₀ ^ 2) ^ p ≤ (τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2)) ^ p :=
          pow_le_pow_left₀ (by positivity) this p
      _ = τ⁻¹ ^ (4 * p) * Y := by rw [mul_pow, ← pow_mul]
  have hNp : ((N : ℝ) ^ (2 * p + 2))⁻¹ * N ≤ τ⁻¹ ^ (2 * p) * Y := by
    have e : ((N : ℝ) ^ (2 * p + 2))⁻¹ * N ≤ ((N : ℝ) ^ (2 * p))⁻¹ := by
      have e2 : ((N : ℝ) ^ (2 * p + 2))⁻¹ * N = ((N : ℝ) ^ (2 * p))⁻¹ * (N : ℝ)⁻¹ := by
        rw [show 2 * p + 2 = 2 * p + 1 + 1 by ring, pow_succ, pow_succ]
        field_simp
      rw [e2]
      calc ((N : ℝ) ^ (2 * p))⁻¹ * (N : ℝ)⁻¹ ≤ ((N : ℝ) ^ (2 * p))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hNr) (by positivity)
        _ = ((N : ℝ) ^ (2 * p))⁻¹ := mul_one _
    have h1 : (τ / N) ^ (2 * p) ≤ Ψ ^ (2 * p) := pow_le_pow_left₀ (by positivity) hΨge _
    have h2 : Ψ ^ (2 * p) ≤ Y := by
      rw [hY, mul_pow, ← pow_mul]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hNδ)
    have e1 : ((N : ℝ) ^ (2 * p))⁻¹ = τ⁻¹ ^ (2 * p) * (τ / N) ^ (2 * p) := by
      rw [div_pow, inv_pow]; field_simp
    rw [e1] at e
    exact e.trans (mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity))
  have hMN' : (M : ℝ) * (N : ℝ)⁻¹ ≤ τ⁻¹ := by rw [← div_eq_mul_inv]; exact hMN
  have hMN0 : 0 ≤ (M : ℝ) * (N : ℝ)⁻¹ := by positivity
  rw [hatAvg_rpow_three_half hN]
  have hX0 : 0 ≤ K₃ * (EF + (b₀ ^ 2) ^ p) := by positivity
  have h1 : (N : ℝ)⁻¹ * ε * S ≤ (M : ℝ) * (N : ℝ)⁻¹ * (K₃ * (EF + (b₀ ^ 2) ^ p)) +
      3 * ((M : ℝ) * (N : ℝ)⁻¹) * ε * (((N : ℝ) ^ (2 * p + 2))⁻¹ * N) := by
    calc (N : ℝ)⁻¹ * ε * S ≤ (N : ℝ)⁻¹ * ε * ((M : ℝ) * N * (ε * (K₃ * (EF + (b₀ ^ 2) ^ p)) +
          3 * ((N : ℝ) ^ (2 * p + 2))⁻¹)) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (M : ℝ) * ((N : ℝ)⁻¹ * N) * (ε * ε) * (K₃ * (EF + (b₀ ^ 2) ^ p)) +
          3 * ((M : ℝ) * (N : ℝ)⁻¹) * ε * (((N : ℝ) ^ (2 * p + 2))⁻¹ * N) := by ring
      _ = (M : ℝ) * (N : ℝ)⁻¹ * (K₃ * (EF + (b₀ ^ 2) ^ p)) +
          3 * ((M : ℝ) * (N : ℝ)⁻¹) * ε * (((N : ℝ) ^ (2 * p + 2))⁻¹ * N) := by
          rw [inv_mul_cancel₀ hN0.ne', ← sq, hεsq]; ring
  have h2 : (M : ℝ) * (N : ℝ)⁻¹ * (K₃ * (EF + (b₀ ^ 2) ^ p)) ≤
      τ⁻¹ * (K₃ * (EF + τ⁻¹ ^ (4 * p) * Y)) :=
    mul_le_mul hMN' (mul_le_mul_of_nonneg_left (by linarith) hK₃) hX0 (by positivity)
  have h3 : 3 * ((M : ℝ) * (N : ℝ)⁻¹) * ε * (((N : ℝ) ^ (2 * p + 2))⁻¹ * N) ≤
      3 * τ⁻¹ * 1 * (τ⁻¹ ^ (2 * p) * Y) := by
    gcongr
  have e : (τ⁻¹ * K₃ * (1 + τ⁻¹ ^ (4 * p)) + 3 * τ⁻¹ ^ (2 * p + 1)) * (Y + EF) =
      τ⁻¹ * (K₃ * (EF + τ⁻¹ ^ (4 * p) * Y)) + 3 * τ⁻¹ * 1 * (τ⁻¹ ^ (2 * p) * Y) +
        (τ⁻¹ * K₃ * Y + τ⁻¹ * K₃ * τ⁻¹ ^ (4 * p) * EF + 3 * τ⁻¹ ^ (2 * p + 1) * EF) := by ring
  have h4 : 0 ≤ τ⁻¹ * K₃ * Y + τ⁻¹ * K₃ * τ⁻¹ ^ (4 * p) * EF + 3 * τ⁻¹ ^ (2 * p + 1) * EF := by
    positivity
  rw [e]
  linarith

/-- (avg_pf_claim) for `n = 3`, the removal of `ν = μ`, at one `N ≥ N₀`. -/
private theorem hatAvg_fixed {τ c εa δ Da : ℝ} {C : ℕ → ℝ} {p : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ) (hεaδ : 20 * p * εa ≤ δ)
    (hDa : dPrevTwo τ p ≤ Da) {KL : ℝ} (hKL0 : 0 ≤ KL)
    (hKL : ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
      (i : Fin M) (μ : Fin N) (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)]
      (β Cm Kg : ℝ), 1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 0 < β → 2 * β ^ 2 ≤ 1 → 0 ≤ Cm →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ β ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ β) →
      ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ Kg → ‖mFun N (specOf Sig) z‖ ≤ Cm →
      ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(Measure.pi ρ)‖ ≤
        KL * (1 + Cm) ^ (p + 2) * Kg * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ *
          (β ^ 2 * (‖hatAvg_Sh Sig A z μ‖ + β ^ 2) ^ (p - 2)))))
    {N : ℕ} (hN2 : 2 ≤ N)
    (hNa : 2 * (1 + 2 * mBoundConst τ) * (τ⁻¹ ^ 2 * (Real.sqrt (mBoundConst τ) + 1)) ≤
      (N : ℝ) ^ (τ / 16))
    (hNb : hatAvg_Cf τ C p (mBoundConst τ) (τ⁻¹ * c⁻¹ + mBoundConst τ) ≤ N)
    (hNc : KL * (1 + mBoundConst τ) ^ (p + 2) * (τ⁻¹ * c⁻¹ + mBoundConst τ + 1) * 2 ^ p ≤ N)
    {M : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ} (hcs : CompSetting τ c M N Sig S)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {z : ℂ} (hz : z ∈ S)
    (hev : HighProbAt N (Da - 3) {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤
      τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z}) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
      ‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
        ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
      (τ⁻¹ * hatAvg_K3 p (2 * mBoundConst τ) (mBoundConst τ) (τ⁻¹ * c⁻¹ + mBoundConst τ)
          (Real.sqrt (mBoundConst τ) * τ ^ 2) KL * (1 + τ⁻¹ ^ (4 * p)) + 3 * τ⁻¹ ^ (2 * p + 1)) *
        (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  set Cm := mBoundConst τ with hCmdef
  have hCm0 : 0 < Cm := mBoundConst_pos hτ
  set L := 2 * Cm with hLdef
  have hL : 0 ≤ L := by positivity
  set KP := τ⁻¹ * c⁻¹ + Cm with hKPdef
  have hKP : 0 ≤ KP := by positivity
  set c₂ := Real.sqrt Cm * τ ^ 2 with hc₂def
  have hc₂ : 0 ≤ c₂ := by positivity
  have h2εa : 2 * εa ≤ δ := by
    have hp1 : (2 : ℝ) ≤ 20 * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
      linarith
    have := mul_le_mul_of_nonneg_right hp1 hεa.le
    linarith
  set K₃ := hatAvg_K3 p L Cm KP c₂ KL with hK₃
  have hK₃0 : 0 ≤ K₃ := by
    simp only [hK₃, hatAvg_K3, hatAvg_K0, hatAvg_CB]; positivity
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hSig := hcs.sigma.posDef
  have hzD := hcs.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hN0).1 hcs.ratio_le
  obtain ⟨hm1, hm2, -⟩ := gen_prop_m_specDomain (hatAvg_density hcs hN1) hzD
  have hPi := (hatAvg_Pi hcs hN1 hz).1
  set Ψ := Psi N (specOf Sig) z with hΨ
  have hΨge : τ / N ≤ Ψ := hatAvg_Psi_ge hN1 hτ hzD
  have hΨdec := hatAvg_Psi_decay hcs hN1 hz
  have hΨsq := hatAvg_Psi_sq_ge hcs hN1 hz
  obtain ⟨hb₀0, hKcb, hNb₀⟩ := hatAvg_scal hτ hεa hεaτ hCm0 hN2 hNa hΨge hΨdec hΨsq
  set b₀ := τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ with hb₀
  have hCmb : 0 ≤ Cm * b₀ := mul_nonneg hCm0.le hb₀0.le
  have hb₀1 : b₀ ≤ 1 := by linarith
  have hβ0 : 0 < (1 + L) * b₀ := by positivity
  have hβ2 : 2 * ((1 + L) * b₀) ^ 2 ≤ 1 := by
    have h1 : (1 + L) * b₀ ≤ 1 / 2 := by rw [hLdef]; linarith
    have h2 := mul_le_mul h1 h1 hβ0.le (by norm_num)
    rw [sq]; linarith
  -- the rough bound of `G`
  set R := (1 + 5 * ‖z‖) / z.im * τ⁻¹ with hRdef
  have hR : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t, ‖G Sig A z s t‖ ≤ R :=
    fun A s t => hatAvg_G_rough hcs.sigma hτ hτ1 A hη s t
  have hR0 : 0 ≤ R := by positivity
  have hRN : R ≤ (1 + 10 * τ⁻¹) * τ⁻¹ * N := by
    have hz2 : ‖z‖ ≤ 2 * τ⁻¹ := by
      have h1 := Complex.norm_le_abs_re_add_abs_im z
      have h2 : |z.im| ≤ τ⁻¹ := by rw [abs_of_pos hη]; exact hzD.2.2.2.2
      linarith [hzD.2.2.1]
    have hNη : 1 ≤ (N : ℝ) * z.im := hatAvg_one_le_N_im hN1 hτ hzD
    have hi : 1 / z.im ≤ N := by rw [div_le_iff₀ hη]; linarith
    rw [hRdef]
    calc (1 + 5 * ‖z‖) / z.im * τ⁻¹ = (1 + 5 * ‖z‖) * (1 / z.im) * τ⁻¹ := by ring
      _ ≤ (1 + 5 * (2 * τ⁻¹)) * N * τ⁻¹ := by gcongr
      _ = (1 + 10 * τ⁻¹) * τ⁻¹ * N := by ring
  -- the a priori event
  set Ξ : Set Ω := {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀} with hΞ
  have hPΞ : (ℙ Ξᶜ).toReal ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹ := by
    have hev' : ℙ Ξᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Da - 3))) := hev
    refine (ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hev').trans ?_
    have hD := hatAvg_D_ge (τ := τ) hDa
    calc (N : ℝ) ^ (-(Da - 3)) ≤ (N : ℝ) ^ (-((24 * p + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by push_cast; linarith only [hD])
      _ = ((N : ℝ) ^ (24 * p + 1))⁻¹ := by rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  have h2Cmb : 2 * Cm * b₀ ≤ 1 := by linarith
  have hΞp : ∀ μ : Fin N, ∀ ω ∈ Ξ, (∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀) ∧
      1 ≤ L * ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)‖ := by
    intro μ ω hω
    refine ⟨hω, ?_⟩
    have hgm : ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b₀ := by
      have := hω (Sum.inr μ) (Sum.inr μ); simpa [PiZ, piMat] using this
    have h1 := norm_sub_norm_le (mFun N (specOf Sig) z) (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ))
    rw [norm_sub_rev] at h1
    have h3 : Cm⁻¹ - b₀ ≤ ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)‖ := by linarith
    have h4 : 2 * Cm * (Cm⁻¹ - b₀) = 2 - 2 * Cm * b₀ := by field_simp
    have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Cm)
    rw [hLdef]
    linarith
  -- one `(i, μ)`
  set s := ((N : ℝ) ^ (2 * p + 2) * (N : ℝ) ^ (8 * p + 1))⁻¹ with hs
  have hs0 : 0 < s := by positivity
  set ε := (Real.sqrt N)⁻¹ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact hNr)
  set EF := ∫ ω, Ft Sig (X ω) z ^ p with hEF
  have hEF0 : 0 ≤ EF := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
  have hper : ∀ (i : Fin M) (μ : Fin N),
      ‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
        ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
      ε * (K₃ * (EF + (b₀ ^ 2) ^ p)) + 3 * ((N : ℝ) ^ (2 * p + 2))⁻¹ := by
    intro i μ
    obtain ⟨hI1, hI2⟩ := hatAvg_f_int hX hSig hη i μ p hR0 hKP hR hPi
    rw [← integral_sub hI1 hI2]
    have hKLp : ∀ (A : Matrix (Fin M) (Fin N) ℝ) (ρ : Fin M → Measure ℝ)
        [∀ j, IsProbabilityMeasure (ρ j)], (∀ j, ∫ y, y ∂(ρ j) = 0) →
        (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
          ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
        (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ (1 + L) * b₀ ∧
          ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ (1 + L) * b₀) →
        ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl i)‖ ≤ KP + 1 →
        ‖∫ y, hatAvg_Lead Sig A z i μ p y ∂(Measure.pi ρ)‖ ≤
          KL * (1 + Cm) ^ (p + 2) * (KP + 1) * ((N : ℝ)⁻¹ * ((Real.sqrt N)⁻¹ *
            (((1 + L) * b₀) ^ 2 * (‖hatAvg_Sh Sig A z μ‖ + ((1 + L) * b₀) ^ 2) ^ (p - 2)))) :=
      fun A ρ _ hmean hρ hGν hGii =>
        hKL M N Sig A z i μ ρ ((1 + L) * b₀) Cm (KP + 1) hN1 hM hβ0 hβ2 hCm0.le hmean hρ hGν hGii
          hm2
    have h := hatAvg_per hX hSig hη i μ hp2 (Ξ := Ξ) hτ hM hb₀1 hL hCm0.le hKP hc₂ hβ0 hβ2 hR0
      hKL0 hs0 hKLp hm2 hPi hNb₀ hR (hΞp μ) hPΞ
    refine h.trans ?_
    -- the off-event terms
    have hT : 2 * (2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p)) ^ 2 +
        2 * (4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) * (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p) ^ 2 *
          (1 + (M : ℝ)) ^ (4 * p) * (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p)) ≤
        (N : ℝ) ^ (8 * p + 1) := by
      have hτi : 0 ≤ τ⁻¹ := by positivity
      set cR := (1 + 10 * τ⁻¹) * τ⁻¹ with hcR
      have hcR0 : 0 ≤ cR := by positivity
      have hRK : R + KP + 1 ≤ (cR + KP + 1) * N := by
        have := le_mul_of_one_le_right hKP hNr
        have e : (cR + KP + 1) * (N : ℝ) = cR * N + KP * N + N := by ring
        linarith
      have h1 : (8 * (R + KP + 1) ^ 4) ^ p ≤ (8 * (cR + KP + 1) ^ 4) ^ p * (N : ℝ) ^ (4 * p) := by
        rw [pow_mul, ← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ p
        calc 8 * (R + KP + 1) ^ 4 ≤ 8 * ((cR + KP + 1) * N) ^ 4 := by gcongr
          _ = 8 * (cR + KP + 1) ^ 4 * (N : ℝ) ^ 4 := by ring
      have h2 : (2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p)) ^ 2 ≤
          4 * (4 ^ p * (8 * (cR + KP + 1) ^ 4) ^ p) ^ 2 * (N : ℝ) ^ (8 * p) := by
        calc (2 * (4 ^ p * (8 * (R + KP + 1) ^ 4) ^ p)) ^ 2
            ≤ (2 * (4 ^ p * ((8 * (cR + KP + 1) ^ 4) ^ p * (N : ℝ) ^ (4 * p)))) ^ 2 := by gcongr
          _ = 4 * (4 ^ p * (8 * (cR + KP + 1) ^ 4) ^ p) ^ 2 * (N : ℝ) ^ (8 * p) := by
              rw [show 8 * p = 4 * p + 4 * p by ring, pow_add]; ring
      have hM1 : (1 + (M : ℝ)) ^ (4 * p) ≤ (1 + τ⁻¹) ^ (4 * p) * (N : ℝ) ^ (4 * p) := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ _
        have e : (1 + τ⁻¹) * (N : ℝ) = N + τ⁻¹ * N := by ring
        linarith
      have hKS0 : 0 ≤ hatAvg_KS τ C (4 * p) := by
        unfold hatAvg_KS
        have := le_max_right (C (2 * (4 * p))) 0
        positivity
      have h3 : 2 * (4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) *
          (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p) ^ 2 *
          (1 + (M : ℝ)) ^ (4 * p) * (hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p)) ≤
          2 * hatAvg_RL p Cm KP ^ 2 * (1 + τ⁻¹) ^ (4 * p) * hatAvg_KS τ C (4 * p) *
            (N : ℝ) ^ (8 * p) := by
        rw [hatAvg_RL]
        have h4 := mul_le_mul_of_nonneg_left hM1
          (by positivity : 0 ≤ 2 * (4 ^ p * p * ((1 + Cm) ^ 2 * (KP + 1)) *
            (2 * (1 + Cm) * (KP + 1) ^ 2) ^ p) ^ 2)
        have h5 := mul_le_mul_of_nonneg_right h4
          (by positivity : 0 ≤ hatAvg_KS τ C (4 * p) * (N : ℝ) ^ (4 * p))
        refine h5.trans (le_of_eq ?_)
        rw [show 8 * p = 4 * p + 4 * p by ring, pow_add]; ring
      have hCf : hatAvg_Cf τ C p Cm KP * (N : ℝ) ^ (8 * p) ≤ (N : ℝ) ^ (8 * p + 1) := by
        rw [pow_succ, mul_comm ((N : ℝ) ^ (8 * p))]
        exact mul_le_mul_of_nonneg_right hNb (by positivity)
      have e : hatAvg_Cf τ C p Cm KP * (N : ℝ) ^ (8 * p) =
          2 * (4 * (4 ^ p * (8 * (cR + KP + 1) ^ 4) ^ p) ^ 2 * (N : ℝ) ^ (8 * p)) +
            2 * hatAvg_RL p Cm KP ^ 2 * (1 + τ⁻¹) ^ (4 * p) * hatAvg_KS τ C (4 * p) *
              (N : ℝ) ^ (8 * p) := by
        rw [hatAvg_Cf, hcR]; ring
      linarith
    have hKb0 : 0 ≤ KL * (1 + Cm) ^ (p + 2) * (KP + 1) := by positivity
    have htiny := hatAvg_tiny hN1 (by omega) hT hNc
      (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹) le_rfl
    have hpre : ε * (2 ^ p * (hatAvg_K0 p L Cm KP c₂ + KL * (1 + Cm) ^ (p + 2) * (KP + 1) *
        c₂ ^ 2 * (1 + L) ^ 2 * (1 + (c₂ ^ 2 + L ^ 2 + Cm * L ^ 2) + (1 + L) ^ 2) ^ p) *
        ((∫ ω, Ft Sig (X ω) z ^ p) + (b₀ ^ 2) ^ p)) = ε * (K₃ * (EF + (b₀ ^ 2) ^ p)) := by
      rw [hK₃, hatAvg_K3]
    rw [← hs] at htiny
    rw [hpre]
    linarith
  -- the sum over `(i, μ)`
  have hsum : ∑ i : Fin M, ∑ μ : Fin N, ‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
      ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
      (M : ℝ) * N * (ε * (K₃ * (EF + (b₀ ^ 2) ^ p)) + 3 * ((N : ℝ) ^ (2 * p + 2))⁻¹) := by
    calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N,
          (ε * (K₃ * (EF + (b₀ ^ 2) ^ p)) + 3 * ((N : ℝ) ^ (2 * p + 2))⁻¹) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hper i μ
      _ = _ := by simp; ring
  rw [hε, hb₀] at hsum
  exact hatAvg_sumfinal (by omega) hτ hK₃0 hEF0 hΨge hεa h2εa hcs.ratio_le hsum

/-! ## (avg_pf_claim) for `n = 3` -/

/-- The removal of `ν = μ` at `n = 3` (`Â` of §9), including the word `𝛍𝐢𝐢𝛍` at `ν = μ`. -/
theorem avg_hat_replace (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
            ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
            K * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  have _hp := hp
  have _hδ := hδ
  obtain ⟨KL, hKL0, hKL⟩ := hatAvg_lead_col C τ hτ p hp2
  have hCm0 : 0 < mBoundConst τ := mBoundConst_pos hτ
  refine ⟨τ⁻¹ * hatAvg_K3 p (2 * mBoundConst τ) (mBoundConst τ) (τ⁻¹ * c⁻¹ + mBoundConst τ)
      (Real.sqrt (mBoundConst τ) * τ ^ 2) KL * (1 + τ⁻¹ ^ (4 * p)) + 3 * τ⁻¹ ^ (2 * p + 1),
    by simp only [hatAvg_K3, hatAvg_K0, hatAvg_CB]; positivity, ?_⟩
  obtain ⟨N₁, h₁⟩ := avg_entry_highProb τ c εa Da hτ hτ1 hc
  obtain ⟨N₂, h₂⟩ := hatAvg_large hτ
    (2 * (1 + 2 * mBoundConst τ) * (τ⁻¹ ^ 2 * (Real.sqrt (mBoundConst τ) + 1)))
    (max (hatAvg_Cf τ C p (mBoundConst τ) (τ⁻¹ * c⁻¹ + mBoundConst τ))
      (KL * (1 + mBoundConst τ) ^ (p + 2) * (τ⁻¹ * c⁻¹ + mBoundConst τ + 1) * 2 ^ p))
  refine ⟨max N₁ N₂, fun N hN M Sig S hcs hA Ω _ _ X hX z hz => ?_⟩
  obtain ⟨hNa, hNb, hN2⟩ := h₂ N (le_of_max_le_right hN)
  have hev := h₁ N (le_of_max_le_left hN) M Sig S hcs Ω X (hA Ω X hX) z hz
  exact hatAvg_fixed hτ hτ1 hc hp2 hεa hεaτ hεaδ hDa hKL0 hKL hN2 hNa
    ((le_max_left _ _).trans hNb) ((le_max_right _ _).trans hNb) hcs hX hz hev

/-! ## The sum over tagged tuples -/

/-- The integrand of (avg_step 1) at one tagged tuple. -/
private def hatAvg_T (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) : ℂ :=
  (N : ℂ)⁻¹ ^ p * ∑ νs ∈ Fintype.piFinset (fun _ : Fin p => Finset.univ.erase μ),
    ∏ r, conjIf (cs r) (tagA Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r) (σs r) *
      G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))

/-- (wh_A_identity) at `v = e_ν`, `ν ≠ μ`:
`a_k(e_ν) = (−1)^k ∑_w ∑_{|σ|_v = 0} A(w, σ) G_μμ^{|σ|_μ}`. -/
private theorem hatAvg_resCoeff_tag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) {μ ν : Fin N}
    (hν : ν ≠ μ) (k : ℕ) :
    resCoeff Sig A z (eI (Sum.inr ν)) i μ k = (-1) ^ k * ∑ w : Word k,
      ∑ σ : Fin (k + 1) → Fin 3, if tagV σ = 0 then tagA Sig A z (eI (Sum.inr ν)) i μ k w σ *
        G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu σ else 0 := by
  rw [resCoeff_eq_sum_wordA hSig A hz]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hv0 : ((vbar Sig (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) (Sum.inr μ) : ℝ) : ℂ) = 0 := by
    rw [hatAvg_vbar_inr]; simp [eI, Ne.symm hν]
  have hw : wordA Sig A z (eI (Sum.inr ν)) i μ k w = hatA Sig A z (eI (Sum.inr ν)) i μ k w := by
    cases k with
    | zero => simp only [hatA]; rw [hv0]; ring
    | succ k => rfl
  rw [hw, wh_A_identity hSig A hz, hv0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · rw [h, pow_zero, mul_one]
  · rw [zero_pow h, mul_zero]

/-- `f_3(â)` as the sum over tagged tuples with `|σ_r|_v = 0` of `−(integrand of (avg_step 1))`. -/
private theorem hatAvg_hat_expand {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (p : ℕ) :
    fCoeff p (avgCoeffHat Sig A z i μ) 3 = ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3,
      ∑ ws : (∀ r, Word (κ r)), ∑ σs : (∀ r, Fin (κ r + 1) → Fin 3),
        if (∀ r, tagV (σs r) = 0) then -hatAvg_T Sig A z i μ κ ws σs (hatAvg_cs p) else 0 := by
  rw [hatAvg_fCoeff_eq]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hκ
  set F : ∀ r : Fin p, Word (κ r) → (Fin (κ r + 1) → Fin 3) → ℂ := fun r w σ =>
    if tagV σ = 0 then (-1) ^ κ r * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
      tagA Sig A z (eI (Sum.inr ν)) i μ (κ r) w σ *
        G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu σ) else 0 with hF
  have hâ : ∀ r, avgCoeffHat Sig A z i μ (κ r) = ∑ w, ∑ σ, F r w σ := by
    intro r
    unfold avgCoeffHat
    rw [Finset.sum_congr rfl fun ν hν => hatAvg_resCoeff_tag hSig A hz i
      (Finset.ne_of_mem_erase hν) (κ r)]
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun ν _ => ?_
      ring
    · simp
  simp only [hâ, hatAvg_conjIf_sum]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun ws _ => ?_
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σs _ => ?_
  split_ifs with hv
  · have hF' : ∀ r, F r (ws r) (σs r) = (-1) ^ κ r * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        tagA Sig A z (eI (Sum.inr ν)) i μ (κ r) (ws r) (σs r) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r)) := fun r => by
      simp only [hF, hv r, ↓reduceIte]
    simp only [hF', hatAvg_T]
    have hc : ∀ r, conjIf (hatAvg_cs p r) ((-1) ^ κ r * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        tagA Sig A z (eI (Sum.inr ν)) i μ (κ r) (ws r) (σs r) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))) =
        (-1) ^ κ r * ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, conjIf (hatAvg_cs p r)
          (tagA Sig A z (eI (Sum.inr ν)) i μ (κ r) (ws r) (σs r) *
            G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))) := by
      intro r
      rw [hatAvg_conjIf_mul, hatAvg_conjIf_mul, hatAvg_conjIf_sum]
      congr 1
      · have : ((-1 : ℂ) ^ κ r) = (((-1 : ℝ) ^ κ r : ℝ) : ℂ) := by push_cast; ring
        rw [this, hatAvg_conjIf_ofReal]
      · congr 1
        have : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
        rw [this, hatAvg_conjIf_ofReal]
    simp only [hc]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hκ,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_univ_sum]
    ring
  · obtain ⟨r, hr⟩ := not_forall.1 hv
    rw [Finset.prod_eq_zero (Finset.mem_univ r)]
    simp [hF, hr, hatAvg_conjIf_zero]

/-- The integrand of (avg_step 1) at one tagged tuple with `|σ_r|_v = 0` is integrable: it is
continuous in `X` and at most `W^{4(p+3)}`, `W = (R + K_Π)(1 + R)(1 + ∑_j |X_{jμ}|)`. -/
private theorem hatAvg_T_int {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0) {KP : ℝ} (hKP : 0 ≤ KP)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    Integrable fun ω => hatAvg_T Sig (X ω) z i μ ns ws σs cs := by
  have hSig := hS.posDef
  have hN1 : 1 ≤ N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  set R := (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 with hRdef
  have hR1 : 1 ≤ R := by have : 0 ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by positivity
                         linarith
  have hRmu : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t, ‖Gmu Sig A z μ s t‖ ≤ R := fun A s t =>
    (hatAvg_Gmu_rough hS hτ hτ1 A hz μ s t).trans (by linarith)
  have hRG : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t, ‖G Sig A z s t‖ ≤ R := fun A s t =>
    (hatAvg_G_rough hS hτ hτ1 A hz s t).trans (by linarith)
  set c₀ := (R + KP) * (1 + R) with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    have : 1 ≤ R + KP := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (R + KP) * (1 + R) := by gcongr; linarith
  -- the pointwise bound
  have hpt : ∀ A : Matrix (Fin M) (Fin N) ℝ, ‖hatAvg_T Sig A z i μ ns ws σs cs‖ ≤
      (c₀ * (1 + hatAvg_V A μ)) ^ (4 * (p + 3)) := by
    intro A
    have hV := hatAvg_V_nonneg A μ
    set W := c₀ * (1 + hatAvg_V A μ) with hW
    have hW1 : 1 ≤ W := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ c₀ * (1 + hatAvg_V A μ) := by gcongr; linarith
    have hRW : R ≤ W := by
      have h1 : R ≤ R + KP := by linarith
      have h2 : R + KP ≤ c₀ := le_mul_of_one_le_right (by linarith) (by linarith)
      have h3 : c₀ ≤ W := le_mul_of_one_le_right (by linarith) (by linarith)
      linarith
    have hterm : ∀ (ν : Fin N), ν ≠ μ → ∀ r, ‖conjIf (cs r)
        (tagA Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤ W ^ (4 * (ns r + 1)) := by
      intro ν hν r
      rw [hatAvg_norm_conjIf, norm_mul, norm_pow]
      have h1 := hatAvg_tagA_rough Sig A z hν i hR1 hKP (hRmu A) hPi (ns r) (ws r) (σs r) (hv r)
      have h2 : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ^ tagMu (σs r) ≤ W ^ (ns r + 1) :=
        (pow_le_pow_left₀ (norm_nonneg _) ((hRG A _ _).trans hRW) _).trans
          (pow_le_pow_right₀ hW1 (hatAvg_tagMu_le _))
      calc _ ≤ W ^ (3 * (ns r + 1)) * W ^ (ns r + 1) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = W ^ (4 * (ns r + 1)) := by rw [← pow_add]; ring_nf
    unfold hatAvg_T
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    have hcard : ((Fintype.piFinset fun _ : Fin p => Finset.univ.erase μ).card : ℝ) ≤
        (N : ℝ) ^ p := by
      rw [Fintype.card_piFinset_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N 1) p
    have hprod : ∀ νs ∈ Fintype.piFinset (fun _ : Fin p => Finset.univ.erase μ),
        ‖∏ r, conjIf (cs r) (tagA Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r) (σs r) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤ W ^ (4 * (p + 3)) := by
      intro νs hνs
      rw [Fintype.mem_piFinset] at hνs
      rw [norm_prod]
      calc _ ≤ ∏ r, W ^ (4 * (ns r + 1)) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            fun r _ => hterm _ (Finset.ne_of_mem_erase (hνs r)) r
        _ = W ^ (4 * (p + 3)) := by
            rw [Finset.prod_pow_eq_pow_sum]
            congr 1
            rw [← Finset.mul_sum, Finset.sum_add_distrib, hns]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
            ring
    calc (N : ℝ)⁻¹ ^ p * ‖∑ νs ∈ Fintype.piFinset (fun _ : Fin p => Finset.univ.erase μ),
          ∏ r, conjIf (cs r) (tagA Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r) (σs r) *
            G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖
        ≤ (N : ℝ)⁻¹ ^ p * ((N : ℝ) ^ p * W ^ (4 * (p + 3))) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
          refine (Finset.sum_le_sum hprod).trans ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = W ^ (4 * (p + 3)) := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hNr.ne', one_pow, one_mul]
  -- continuity and the moments
  have hcont : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hatAvg_T Sig A z i μ ns ws σs cs := by
    unfold hatAvg_T
    have hcj : ∀ (c : Bool) {f : Matrix (Fin M) (Fin N) ℝ → ℂ}, Continuous f →
        Continuous fun A => conjIf c (f A) := by
      intro c f hf
      cases c
      · simpa [conjIf] using hf
      · simp only [conjIf, ite_true]; exact Complex.continuous_conj.comp hf
    exact continuous_const.mul (continuous_finsetSum _ fun νs _ => continuous_finsetProd _
      fun r _ => hcj _ ((hatAvg_cont_tagA hSig hz _ i μ _ _ _).mul
        ((hatAvg_cont_Gent hSig hz _ _).pow _)))
  have hmom := hatAvg_moment hτ hX hN1 hM (4 * (p + 3))
  have hbound : ∀ ω, ‖hatAvg_T Sig (X ω) z i μ ns ws σs cs‖ ≤
      (c₀ * (1 + (M : ℝ))) ^ (4 * (p + 3)) * (1 + hatAvg_sq (X ω)) ^ (4 * (p + 3)) := by
    intro ω
    refine (hpt (X ω)).trans ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by have := hatAvg_V_nonneg (X ω) μ; positivity) ?_ _
    have := hatAvg_V_le (X ω) μ
    calc c₀ * (1 + hatAvg_V (X ω) μ) ≤ c₀ * ((1 + M) * (1 + hatAvg_sq (X ω))) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = c₀ * (1 + M) * (1 + hatAvg_sq (X ω)) := by ring
  exact (hmom.1.const_mul _).mono' (hcont.measurable.comp hXm).aestronglyMeasurable
    (ae_of_all _ hbound)

/-- `∑_a ∑_b ∑_{c ∈ u} f = ∑_{c ∈ u} ∑_a ∑_b f`. -/
private theorem hatAvg_swap {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- (avg_pf_claim) for `n = 3` with `ν ≠ μ`: (wh_A_identity) at `v = e_ν` and `avg_lem82`. -/
theorem avg_claim3_hat (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
            K * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  obtain ⟨K₈₂, hK₈₂0, N₀, h82⟩ :=
    avg_lem82 τ c C p δ εa Da hτ hτ1 hc hp hp2 hδ hεa hεaτ hεaδ hDa
  set nT : ℕ := ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3,
    Fintype.card (∀ r, Word (κ r)) * Fintype.card (∀ r, Fin (κ r + 1) → Fin 3) with hnT
  refine ⟨nT * K₈₂, by positivity, N₀, fun N hN M Sig S hcs hA Ω _ _ X hX z hz => ?_⟩
  have hzD := hcs.domain.1 hz
  have hη : 0 < z.im := hzD.1
  set Y := ((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p with hY
  have hY0 : 0 ≤ Y := by
    have h1 : 0 ≤ ∫ ω, Ft Sig (X ω) z ^ p := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
    have h2 : 0 ≤ Psi N (specOf Sig) z := by
      unfold Psi
      have : 0 ≤ (N : ℝ) * z.im := by positivity
      positivity
    positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero]
    positivity
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ (by exact_mod_cast hN1)).1 hcs.ratio_le
  have hPi := (hatAvg_Pi hcs hN1 hz).1
  have hKP : 0 ≤ τ⁻¹ * c⁻¹ + mBoundConst τ := by
    have := mBoundConst_pos hτ; have := hcs.c_pos; positivity
  -- the expansion of `E f_3(â)` at one `(i, μ)`
  have hexp : ∀ (i : Fin M) (μ : Fin N),
      ‖∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
        ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ ws : (∀ r, Word (κ r)),
          ∑ σs : (∀ r, Fin (κ r + 1) → Fin 3), if (∀ r, tagV (σs r) = 0) then
            ‖∫ ω, hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p)‖ else 0 := by
    intro i μ
    have hint : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∀ (ws : ∀ r, Word (κ r))
        (σs : ∀ r, Fin (κ r + 1) → Fin 3), Integrable fun ω =>
          (if (∀ r, tagV (σs r) = 0) then -hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p)
            else 0) := by
      intro κ hκ ws σs
      rw [Finset.Nat.mem_antidiagonalTuple] at hκ
      split_ifs with hv
      · exact (hatAvg_T_int hX hτ hτ1 hcs.sigma hM hη i μ κ ws σs _ hκ hv hKP hPi).neg
      · exact integrable_const _
    have e : (fun ω => fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3) = fun ω =>
        ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ ws : (∀ r, Word (κ r)),
          ∑ σs : (∀ r, Fin (κ r + 1) → Fin 3), (if (∀ r, tagV (σs r) = 0) then
            -hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p) else 0) := by
      funext ω
      exact hatAvg_hat_expand hcs.sigma.posDef (X ω) hη i μ p
    rw [e, integral_finsetSum _ fun κ hκ => integrable_finsetSum _ fun ws _ =>
      integrable_finsetSum _ fun σs _ => hint κ hκ ws σs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ?_)
    rw [integral_finsetSum _ fun ws _ => integrable_finsetSum _ fun σs _ => hint κ hκ ws σs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ws _ => ?_)
    rw [integral_finsetSum _ fun σs _ => hint κ hκ ws σs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σs _ => ?_)
    split_ifs with hv
    · rw [integral_neg, norm_neg]
    · simp
  -- the bound of each tuple
  have htup : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∀ (ws : ∀ r, Word (κ r))
      (σs : ∀ r, Fin (κ r + 1) → Fin 3),
      (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, (if (∀ r, tagV (σs r) = 0) then
        ‖∫ ω, hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p)‖ else 0) ≤ K₈₂ * Y := by
    intro κ hκ ws σs
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    split_ifs with hv
    · exact h82 N hN M Sig S hcs hA Ω X hX z hz κ ws σs (hatAvg_cs p) hκ hv
    · simp only [Finset.sum_const_zero, mul_zero]; positivity
  have hpre : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3,
          ∑ ws : (∀ r, Word (κ r)), ∑ σs : (∀ r, Fin (κ r + 1) → Fin 3),
            (if (∀ r, tagV (σs r) = 0) then
              ‖∫ ω, hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p)‖ else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ =>
          hexp i μ) hpre
    _ = ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ ws : (∀ r, Word (κ r)),
          ∑ σs : (∀ r, Fin (κ r + 1) → Fin 3), (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
            (if (∀ r, tagV (σs r) = 0) then
              ‖∫ ω, hatAvg_T Sig (X ω) z i μ κ ws σs (hatAvg_cs p)‖ else 0) := by
        rw [hatAvg_swap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [hatAvg_swap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ws _ => ?_
        rw [hatAvg_swap, Finset.mul_sum]
    _ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ _ws : (∀ r, Word (κ r)),
          ∑ _σs : (∀ r, Fin (κ r + 1) → Fin 3), K₈₂ * Y :=
        Finset.sum_le_sum fun κ hκ => Finset.sum_le_sum fun ws _ =>
          Finset.sum_le_sum fun σs _ => htup κ hκ ws σs
    _ = nT * K₈₂ * Y := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hnT]
        push_cast
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun κ _ => ?_
        ring

/-- (avg_pf_claim) for `n = 3`. -/
theorem avg_claim3 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3‖ ≤
            K * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  obtain ⟨K₁, hK₁, N₁, h₁⟩ :=
    avg_hat_replace τ c C p δ εa Da hτ hτ1 hc hp hp2 hδ hεa hεaτ hεaδ hDa
  obtain ⟨K₂, hK₂, N₂, h₂⟩ :=
    avg_claim3_hat τ c C p δ εa Da hτ hτ1 hc hp hp2 hδ hεa hεaτ hεaδ hDa
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, max N₁ N₂, fun N hN M Sig S hcs hA Ω _ _ X hX z hz => ?_⟩
  have e₁ := h₁ N (le_of_max_le_left hN) M Sig S hcs hA Ω X hX z hz
  have e₂ := h₂ N (le_of_max_le_right hN) M Sig S hcs hA Ω X hX z hz
  set R := ((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p
  have hpow : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have htri : ∀ a b : ℂ, ‖a‖ ≤ ‖a - b‖ + ‖b‖ := fun a b => by
    have := norm_sub_norm_le a b
    linarith
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3‖
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          (‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
            ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ +
          ‖∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => htri _ _) hpow
    _ = (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖(∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) 3) -
            ∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ +
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖∫ ω, fCoeff p (avgCoeffHat Sig (X ω) z i μ) 3‖ := by
        simp only [Finset.sum_add_distrib, mul_add]
    _ ≤ K₁ * R + K₂ * R := add_le_add e₁ e₂
    _ = (K₁ + K₂) * R := by ring

/-! ### Compiled instances -/

/-- The leading shape of the removal of `ν = μ` at `p = 2`: `κ = (2, 1) ∈ T(2, 3)`, with the word
`𝛍𝐢𝐢𝛍` (`w = (false, true)`) at `κ_1 = 2`. -/
example : (![2, 1] : Fin 2 → ℕ) ∈ Finset.Nat.antidiagonalTuple 2 3 ∧
    (Finset.univ.filter fun r : Fin 2 => (![2, 1] : Fin 2 → ℕ) r = 2) = {0} := by
  decide

/-- `avg_hat_replace` at `τ = 1/20`, `c = 1/100`, `p = 2`, `δ = 1`, `ε_a = 1/400`,
`D_a = dPrevTwo(1/20, 2)`: the parameter hypotheses are discharged. The model hypotheses
(`CompSetting`, `AnisoAllAt`, `EntryAssumption`) remain binders: `AnisoAllAt` holds only for `N`
large (Theorem 3.21 (i) for the Gaussian model), so this instance is conditional. -/
example (C : ℕ → ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), CompSetting (1 / 20) (1 / 100) M N Sig S →
      AnisoAllAt N C Sig S (1 / 400) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → ∀ z ∈ S,
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖(∫ ω, fCoeff 2 (avgCoeff Sig (X ω) z i μ) 3) -
            ∫ ω, fCoeff 2 (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
          K * (((N : ℝ) ^ (1 : ℝ) * Psi N (specOf Sig) z ^ 2) ^ 2 + ∫ ω, Ft Sig (X ω) z ^ 2) :=
  avg_hat_replace (1 / 20) (1 / 100) C 2 1 (1 / 400) (dPrevTwo (1 / 20) 2)
    (by norm_num) (by norm_num) (by norm_num) ⟨1, rfl⟩ le_rfl one_pos (by norm_num)
    (by norm_num) (by norm_num) le_rfl

/-- `avg_claim3_hat` at the same parameters (conditional, as above). -/
example (C : ℕ → ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), CompSetting (1 / 20) (1 / 100) M N Sig S →
      AnisoAllAt N C Sig S (1 / 400) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → ∀ z ∈ S,
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖∫ ω, fCoeff 2 (avgCoeffHat Sig (X ω) z i μ) 3‖ ≤
          K * (((N : ℝ) ^ (1 : ℝ) * Psi N (specOf Sig) z ^ 2) ^ 2 + ∫ ω, Ft Sig (X ω) z ^ 2) :=
  avg_claim3_hat (1 / 20) (1 / 100) C 2 1 (1 / 400) (dPrevTwo (1 / 20) 2)
    (by norm_num) (by norm_num) (by norm_num) ⟨1, rfl⟩ le_rfl one_pos (by norm_num)
    (by norm_num) (by norm_num) le_rfl

/-- `avg_claim3` at the same parameters (conditional, as above). -/
example (C : ℕ → ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ), CompSetting (1 / 20) (1 / 100) M N Sig S →
      AnisoAllAt N C Sig S (1 / 400) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → ∀ z ∈ S,
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          ‖∫ ω, fCoeff 2 (avgCoeff Sig (X ω) z i μ) 3‖ ≤
          K * (((N : ℝ) ^ (1 : ℝ) * Psi N (specOf Sig) z ^ 2) ^ 2 + ∫ ω, Ft Sig (X ω) z ^ 2) :=
  avg_claim3 (1 / 20) (1 / 100) C 2 1 (1 / 400) (dPrevTwo (1 / 20) 2)
    (by norm_num) (by norm_num) (by norm_num) ⟨1, rfl⟩ le_rfl one_pos (by norm_num)
    (by norm_num) (by norm_num) le_rfl

end Anisotropic

#print axioms Anisotropic.avg_hat_replace
#print axioms Anisotropic.avg_claim3_hat
#print axioms Anisotropic.avg_claim3
