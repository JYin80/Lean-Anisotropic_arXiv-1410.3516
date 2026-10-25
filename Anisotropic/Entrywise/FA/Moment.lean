import Anisotropic.Entrywise.FA.Vanish
import Anisotropic.Entrywise.SelfCons

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The counting lemma and the `2p`-th moment bound `fa_moment` for weighted averages of `Z_s` -/

/-- The number of positions `k` whose value `v k` occurs exactly once in `v`. -/
def loneCount {n : ℕ} {ι : Type*} [DecidableEq ι] (v : Fin n → ι) : ℕ :=
  (Finset.univ.filter fun k => ∀ l, v l = v k → l = k).card

/-- `2ℓ ≤ n + s`: `ℓ` distinct values and `s` lone positions among `n`. -/
theorem two_mul_card_image_le {n : ℕ} {ι : Type*} [DecidableEq ι] (v : Fin n → ι) :
    2 * (Finset.univ.image v).card ≤ n + loneCount v := by
  set I := Finset.univ.image v with hI
  set L := Finset.univ.filter fun k => ∀ l, v l = v k → l = k with hL
  have hmaps : Set.MapsTo v ↑(Finset.univ : Finset (Fin n)) ↑I :=
    fun k _ => Finset.mem_coe.2 (Finset.mem_image_of_mem v (Finset.mem_univ k))
  have hmapsL : Set.MapsTo v ↑L ↑I :=
    fun k _ => Finset.mem_coe.2 (Finset.mem_image_of_mem v (Finset.mem_univ k))
  have h1 := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 := Finset.card_eq_sum_card_fiberwise hmapsL
  have h3 : ∀ x ∈ I, 2 ≤ (Finset.univ.filter fun k => v k = x).card
      + (L.filter fun k => v k = x).card := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    by_cases hk : ∀ l, v l = v k → l = k
    · have e1 : 1 ≤ (Finset.univ.filter fun l => v l = v k).card :=
        Finset.card_pos.2 ⟨k, by simp⟩
      have e2 : 1 ≤ (L.filter fun l => v l = v k).card :=
        Finset.card_pos.2
          ⟨k, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩, rfl⟩⟩
      omega
    · push Not at hk
      obtain ⟨l, hl, hlk⟩ := hk
      have hsub : ({k, l} : Finset (Fin n)) ⊆ Finset.univ.filter fun m => v m = v k := by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl <;> simp [hl]
      have e3 := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hlk)] at e3
      omega
  calc 2 * I.card = ∑ _x ∈ I, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ I, ((Finset.univ.filter fun k => v k = x).card
          + (L.filter fun k => v k = x).card) := Finset.sum_le_sum h3
    _ = n + loneCount v := by
        rw [Finset.sum_add_distrib, ← h1, ← h2, Finset.card_univ, Fintype.card_fin]
        rfl

/-- `loneCount v ≤ n`. -/
private theorem loneCount_le {n : ℕ} {ι : Type*} [DecidableEq ι] (v : Fin n → ι) :
    loneCount v ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- `|image v| ≤ n`. -/
private theorem moment_card_image_le {n : ℕ} {ι : Type*} [DecidableEq ι] (v : Fin n → ι) :
    (Finset.univ.image v).card ≤ n :=
  Finset.card_image_le.trans (by simp)

/-- The image of `Fin.cons x v` is `insert x (image v)`. -/
private theorem moment_image_cons {n : ℕ} {ι : Type*} [DecidableEq ι] (x : ι) (v : Fin n → ι) :
    Finset.univ.image (Fin.cons x v : Fin (n + 1) → ι) = insert x (Finset.univ.image v) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

/-- `Σ_x K^{-|insert x I|} ≤ (|I| + 1) K^{-|I|}` over an index set of size `K ≥ 1`. -/
private theorem moment_sum_insert_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (I : Finset ι) :
    ∑ x : ι, ((Fintype.card ι : ℝ)⁻¹) ^ (insert x I).card
      ≤ ((I.card : ℝ) + 1) * ((Fintype.card ι : ℝ)⁻¹) ^ I.card := by
  set K : ℝ := (Fintype.card ι : ℝ)
  have hK : 0 < K := Nat.cast_pos.2 hι
  have hpt : ∀ x : ι, (K⁻¹) ^ (insert x I).card
      ≤ (if x ∈ I then (K⁻¹) ^ I.card else 0) + (K⁻¹) ^ (I.card + 1) := by
    intro x
    by_cases hx : x ∈ I
    · rw [Finset.insert_eq_of_mem hx]
      simp only [hx, ↓reduceIte]
      have : 0 ≤ (K⁻¹) ^ (I.card + 1) := by positivity
      linarith
    · rw [Finset.card_insert_of_notMem hx]
      simp only [hx, ↓reduceIte, zero_add, le_refl]
  calc ∑ x : ι, (K⁻¹) ^ (insert x I).card
      ≤ ∑ x : ι, ((if x ∈ I then (K⁻¹) ^ I.card else 0) + (K⁻¹) ^ (I.card + 1)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = I.card * (K⁻¹) ^ I.card + K * (K⁻¹) ^ (I.card + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    _ = ((I.card : ℝ) + 1) * (K⁻¹) ^ I.card := by
        rw [pow_succ]
        field_simp

/-- `Σ_{v : Fin n → ι} K^{-|image v|} ≤ n^n` for `K = |ι| ≥ 1`. -/
private theorem moment_sum_inv_pow_card_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (n : ℕ) :
    ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ (Finset.univ.image v).card ≤ (n : ℝ) ^ n := by
  set K : ℝ := (Fintype.card ι : ℝ)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    have hin : ∀ v : Fin n → ι, ∑ x : ι, (K⁻¹) ^ (Finset.univ.image
        ((Fin.consEquiv fun _ => ι) (x, v))).card ≤
          ((n : ℝ) + 1) * (K⁻¹) ^ (Finset.univ.image v).card := by
      intro v
      have e : ∀ x : ι, (Finset.univ.image ((Fin.consEquiv fun _ => ι) (x, v))) =
          insert x (Finset.univ.image v) := fun x => moment_image_cons x v
      simp_rw [e]
      refine (moment_sum_insert_le hι _).trans ?_
      gcongr
      exact_mod_cast moment_card_image_le v
    calc ∑ v : Fin n → ι, ∑ x : ι, (K⁻¹) ^ (Finset.univ.image
          ((Fin.consEquiv fun _ => ι) (x, v))).card
        ≤ ∑ v : Fin n → ι, ((n : ℝ) + 1) * (K⁻¹) ^ (Finset.univ.image v).card :=
          Finset.sum_le_sum fun v _ => hin v
      _ = ((n : ℝ) + 1) * ∑ v : Fin n → ι, (K⁻¹) ^ (Finset.univ.image v).card := by
          rw [Finset.mul_sum]
      _ ≤ ((n : ℝ) + 1) * (n : ℝ) ^ n := by gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
          push_cast
          rw [pow_succ, mul_comm]
          gcongr
          linarith

/-- One tuple: `K^{-n} Υ^{n+s} ≤ K^{-ℓ} κ^n Υ^{2n}` when `K^{-1/2} ≤ κΥ`, `κ ≥ 1`. -/
private theorem moment_tuple_le {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) {Υ κ : ℝ} (hΥ : 0 ≤ Υ) (hκ : 1 ≤ κ)
    (h : (Fintype.card ι : ℝ) ^ (-(1 / 2 : ℝ)) ≤ κ * Υ) (v : Fin n → ι) :
    ((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v) ≤
      ((Fintype.card ι : ℝ)⁻¹) ^ (Finset.univ.image v).card * (κ ^ n * Υ ^ (2 * n)) := by
  set K : ℝ := (Fintype.card ι : ℝ)
  have hK1 : 1 ≤ K := Nat.one_le_cast.2 hι
  have hK0 : 0 < K := by linarith
  set y : ℝ := (Real.sqrt K)⁻¹ with hy
  have hyK : K ^ (-(1 / 2 : ℝ)) = y := by
    rw [Real.rpow_neg hK0.le, ← Real.sqrt_eq_rpow]
  rw [hyK] at h
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hK1)
  have hy2 : K⁻¹ = y ^ 2 := by rw [hy, inv_pow, Real.sq_sqrt hK0.le]
  set ℓ := (Finset.univ.image v).card
  set s := loneCount v
  have hℓ : ℓ ≤ n := moment_card_image_le v
  have hs : s ≤ n := loneCount_le v
  have h2 : 2 * ℓ ≤ n + s := two_mul_card_image_le v
  have e1 : (K⁻¹) ^ n = (K⁻¹) ^ ℓ * y ^ (2 * (n - ℓ)) := by
    rw [hy2, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have e2 : y ^ (2 * (n - ℓ)) ≤ (κ * Υ) ^ (n - s) :=
    (pow_le_pow_of_le_one hy0 hy1 (by omega)).trans (pow_le_pow_left₀ hy0 h _)
  have e3 : (κ * Υ) ^ (n - s) * Υ ^ (n + s) = κ ^ (n - s) * Υ ^ (2 * n) := by
    rw [mul_pow, mul_assoc, ← pow_add]
    congr 2
    omega
  have e4 : κ ^ (n - s) ≤ κ ^ n := pow_le_pow_right₀ hκ (Nat.sub_le n s)
  calc (K⁻¹) ^ n * Υ ^ (n + s) = (K⁻¹) ^ ℓ * (y ^ (2 * (n - ℓ)) * Υ ^ (n + s)) := by
        rw [e1, mul_assoc]
    _ ≤ (K⁻¹) ^ ℓ * ((κ * Υ) ^ (n - s) * Υ ^ (n + s)) := by gcongr
    _ = (K⁻¹) ^ ℓ * (κ ^ (n - s) * Υ ^ (2 * n)) := by rw [e3]
    _ ≤ (K⁻¹) ^ ℓ * (κ ^ n * Υ ^ (2 * n)) := by gcongr

/-- (d), the counting lemma: if `|ι|^{-1/2} ≤ κΥ` with `κ ≥ 1`, `Υ ≥ 0`, then
`Σ_{v : Fin n → ι} |ι|^{-n} Υ^{n + s(v)} ≤ n^n κ^n Υ^{2n}`. -/
theorem sum_tuples_le {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) {Υ κ : ℝ} (hΥ : 0 ≤ Υ) (hκ : 1 ≤ κ)
    (h : (Fintype.card ι : ℝ) ^ (-(1 / 2 : ℝ)) ≤ κ * Υ) :
    ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v) ≤
      (n : ℝ) ^ n * κ ^ n * Υ ^ (2 * n) := by
  calc ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v)
      ≤ ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ (Finset.univ.image v).card
          * (κ ^ n * Υ ^ (2 * n)) :=
        Finset.sum_le_sum fun v _ => moment_tuple_le hι hΥ hκ h v
    _ = (∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ (Finset.univ.image v).card)
          * (κ ^ n * Υ ^ (2 * n)) := by rw [Finset.sum_mul]
    _ ≤ (n : ℝ) ^ n * (κ ^ n * Υ ^ (2 * n)) := by
        have : 0 ≤ κ := by linarith
        exact mul_le_mul_of_nonneg_right (moment_sum_inv_pow_card_image hι n) (by positivity)
    _ = (n : ℝ) ^ n * κ ^ n * Υ ^ (2 * n) := by ring

/-- `N⁻¹ Σ_μ a_μ Z_μ` with deterministic weights `a`. -/
def ZavgN {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (a : Fin N → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ μ, a μ * Zmu σ Xm z μ

/-- `M⁻¹ Σ_i a_i Z_i` with deterministic weights `a`. -/
def ZavgM {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (a : Fin M → ℂ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ i, a i * Zi σ Xm z i

theorem ZavgN_one {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    ZavgN σ Xm z (fun _ => 1) = ZN σ Xm z := by
  simp [ZavgN, ZN]

/-- `C_p = (2p)^{2p} 2^{2p(2p−1)} τ^{-p} (A (K_Z(p) + K_L(p)))^{2p} + 1`. -/
def faMomConst (p : ℕ) (τ c A : ℝ) : ℝ :=
  (2 * p : ℝ) ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) * τ⁻¹ ^ p *
    (A * (mobConst p τ c + ldeZConst p τ c)) ^ (2 * p) + 1

/-! ## The moment expansion in the proof of Lemma 5.6, for a general family of labels -/

section Core

/-- `x` for `b = false` and `x̄` for `b = true`. -/
private def momCj (b : Bool) : ℂ →+* ℂ := if b then starRingEnd ℂ else RingHom.id ℂ

private theorem momCj_norm (b : Bool) (x : ℂ) : ‖momCj b x‖ = ‖x‖ := by
  cases b <;> simp [momCj]

private theorem momCj_invol (b : Bool) (x : ℂ) : momCj b (momCj b x) = x := by
  cases b <;> simp [momCj]

private theorem momCj_measurable (b : Bool) : Measurable (momCj b) := by
  cases b
  · simpa [momCj] using measurable_id
  · simpa [momCj] using Complex.continuous_conj.measurable

private theorem momCj_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (b : Bool)
    (f : Ω → ℂ) : ∫ ω, momCj b (f ω) ∂μ = momCj b (∫ ω, f ω ∂μ) := by
  cases b
  · simp [momCj]
  · simp [momCj, integral_conj]

/-- The pattern `x, …, x, x̄, …, x̄` (`p` of each) on `Fin (2p)`. -/
private def momPat (p : ℕ) (k : Fin (2 * p)) : Bool := decide ((finProdFinEquiv.symm k).1 = 1)

/-- `Π_k c_k(ξ) = |ξ|^{2p}` for the pattern `momPat`. -/
private theorem prod_momPat (p : ℕ) (ξ : ℂ) :
    ∏ k : Fin (2 * p), momCj (momPat p k) ξ = ((‖ξ‖ ^ (2 * p) : ℝ) : ℂ) := by
  rw [← Fintype.prod_equiv (finProdFinEquiv : Fin 2 × Fin p ≃ Fin (2 * p))
    (fun q => momCj (momPat p (finProdFinEquiv q)) ξ) _ (fun _ => rfl)]
  simp only [momPat, Equiv.symm_apply_apply, Fintype.prod_prod_type, Fin.prod_univ_two]
  simp only [show ∀ x, momCj (decide ((0 : Fin 2) = 1)) x = x from fun x => rfl,
    show ∀ x, momCj (decide True) x = starRingEnd ℂ x from fun x => rfl]
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← mul_pow, Complex.mul_conj, pow_mul, ← Complex.sq_norm]
  push_cast
  ring

/-- The hypotheses of the moment expansion: labels `ι`, the label `π i ν` of the entry `(i, ν)`,
the minor fluctuations `Zs S s` as functions of the matrix, the dependence of their Möbius pieces
on the entries, the vanishing lemma, the pathwise bound `Kd (1 + y_s)`, and the moments of `y_s`. -/
private structure MomHyp {Ω : Type} [MeasureSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (X : Ω → Fin M → Fin N → ℝ) (π : Fin M → Fin N → ι)
    (Zs : Finset ι → ι → (Fin M → Fin N → ℝ) → ℂ) (y : ι → (Fin M → Fin N → ℝ) → ℝ)
    (Kd : ℝ) (n : ℕ) (Cm : ℝ) : Prop where
  meas : Measurable X
  measZ : ∀ S s, Measurable (Zs S s)
  congr : ∀ T U s, s ∉ T → ∀ Xm Xm' : Fin M → Fin N → ℝ,
    (∀ i ν, π i ν ∉ T \ U → Xm i ν = Xm' i ν) →
      mobPart (fun S => Zs S s Xm) T U = mobPart (fun S => Zs S s Xm') T U
  van : ∀ S s (F : (Fin M → Fin N → ℝ) → ℂ), Measurable F →
    (∀ Xm Xm' : Fin M → Fin N → ℝ, (∀ i ν, π i ν ≠ s → Xm i ν = Xm' i ν) → F Xm = F Xm') →
      Integrable (fun ω => F (X ω)) → ∫ ω, Zs S s (X ω) * F (X ω) = 0
  measy : ∀ s, Measurable (y s)
  y0 : ∀ s Xm, 0 ≤ y s Xm
  Kd0 : 0 ≤ Kd
  det : ∀ S s Xm, ‖Zs S s Xm‖ ≤ Kd * (1 + y s Xm)
  Cm0 : 0 ≤ Cm
  mom : ∀ s, Integrable (fun ω => y s (X ω) ^ (2 * n)) ∧ ∫ ω, y s (X ω) ^ (2 * n) ≤ Cm

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
  {X : Ω → Fin M → Fin N → ℝ} {π : Fin M → Fin N → ι}
  {Zs : Finset ι → ι → (Fin M → Fin N → ℝ) → ℂ} {y : ι → (Fin M → Fin N → ℝ) → ℝ}
  {Kd : ℝ} {n : ℕ} {Cm : ℝ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `|F^{[U]}| ≤ 2^{|U|} Kd (1 + y_s)`. -/
private theorem MomHyp.mob_norm_le (H : MomHyp X π Zs y Kd n Cm) (T U : Finset ι) (s : ι)
    (Xm : Fin M → Fin N → ℝ) :
    ‖mobPart (fun S => Zs S s Xm) T U‖ ≤ 2 ^ U.card * (Kd * (1 + y s Xm)) := by
  unfold mobPart
  refine (norm_sum_le _ _).trans ?_
  calc ∑ V ∈ U.powerset, ‖(-1 : ℂ) ^ (U.card - V.card) * Zs (T \ V) s Xm‖
      ≤ ∑ _V ∈ U.powerset, Kd * (1 + y s Xm) := Finset.sum_le_sum fun V _ => by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact H.det _ _ _
    _ = 2 ^ U.card * (Kd * (1 + y s Xm)) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private theorem MomHyp.mob_measurable (H : MomHyp X π Zs y Kd n Cm) (T U : Finset ι) (s : ι) :
    Measurable fun Xm : Fin M → Fin N → ℝ => mobPart (fun S => Zs S s Xm) T U := by
  unfold mobPart
  exact Finset.measurable_sum _ fun V _ => measurable_const.mul (H.measZ _ _)

/-- `Π_k g_k ≤ 1 + Σ_k g_k^n` for `g ≥ 0` on `Fin n`. -/
private theorem moment_prod_le {n : ℕ} (g : Fin n → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∏ k, g k ≤ 1 + ∑ k, g k ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ g ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hsum : 0 ≤ ∑ k, g k ^ n := Finset.sum_nonneg fun k _ => pow_nonneg (hg k) n
    calc ∏ k, g k ≤ ∏ _k : Fin n, g k₀ :=
          Finset.prod_le_prod₀ (fun k _ => hg k) (fun k _ => hk₀ k (Finset.mem_univ _))
      _ = g k₀ ^ n := by simp
      _ ≤ ∑ k, g k ^ n :=
          Finset.single_le_sum (f := fun k => g k ^ n) (fun k _ => pow_nonneg (hg k) n)
            (Finset.mem_univ k₀)
      _ ≤ 1 + ∑ k, g k ^ n := by linarith

/-- `(1 + y)^m ≤ 2^m (1 + y^m)` for `y ≥ 0`. -/
private theorem moment_one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    (1 + t) ^ m ≤ 2 ^ m * (1 + t ^ m) := by
  rcases le_total t 1 with h | h
  · have : (1 + t) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have : 0 ≤ 2 ^ m * t ^ m := by positivity
    nlinarith
  · have : (1 + t) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    rw [mul_pow] at this
    have : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith

/-- `W_v = Π_k (1 + y_{v_k})`: measurable, `W_v ≥ 1`, `W_v` and `W_v²` integrable, and
`E W_v² ≤ 1 + n 2^{2n} (1 + Cm)`. -/
private theorem MomHyp.W_props (H : MomHyp X π Zs y Kd n Cm) (v : Fin n → ι) :
    Measurable (fun ω => ∏ k, (1 + y (v k) (X ω))) ∧
    (∀ ω, 1 ≤ ∏ k, (1 + y (v k) (X ω))) ∧
    Integrable (fun ω => ∏ k, (1 + y (v k) (X ω))) ∧
    Integrable (fun ω => (∏ k, (1 + y (v k) (X ω))) ^ 2) ∧
    ∫ ω, (∏ k, (1 + y (v k) (X ω))) ^ 2 ≤ 1 + n * 2 ^ (2 * n) * (1 + Cm) := by
  set W : Ω → ℝ := fun ω => ∏ k, (1 + y (v k) (X ω)) with hW
  have hWm : Measurable W :=
    Finset.measurable_prod _ fun k _ => measurable_const.add ((H.measy _).comp H.meas)
  have hW1 : ∀ ω, 1 ≤ W ω := fun ω =>
    Finset.one_le_prod₀ fun k _ => le_add_of_nonneg_right (H.y0 _ _)
  set h : Ω → ℝ := fun ω => 1 + ∑ k, 2 ^ (2 * n) * (1 + y (v k) (X ω) ^ (2 * n)) with hh
  have hik : ∀ k, Integrable (fun ω => 2 ^ (2 * n) * (1 + y (v k) (X ω) ^ (2 * n))) :=
    fun k => ((integrable_const _).add (H.mom (v k)).1).const_mul _
  have hS : Integrable (fun ω => ∑ k, 2 ^ (2 * n) * (1 + y (v k) (X ω) ^ (2 * n))) :=
    integrable_finsetSum _ fun k _ => hik k
  have hhi : Integrable h := (integrable_const (1 : ℝ)).add hS
  have hW2 : ∀ ω, W ω ^ 2 ≤ h ω := by
    intro ω
    have e : W ω ^ 2 = ∏ k, (1 + y (v k) (X ω)) ^ 2 := by rw [hW, Finset.prod_pow]
    rw [e]
    refine (moment_prod_le _ fun k => by positivity).trans ?_
    simp only [hh]
    gcongr with k
    rw [← pow_mul]
    exact moment_one_add_pow_le (H.y0 _ _) _
  have hW2i : Integrable (fun ω => W ω ^ 2) :=
    hhi.mono' (hWm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hW2 ω)
  have hWi : Integrable W :=
    hW2i.mono' hWm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hW1 ω])]
      nlinarith [hW1 ω])
  refine ⟨hWm, hW1, hWi, hW2i, ?_⟩
  calc ∫ ω, W ω ^ 2 ≤ ∫ ω, h ω := integral_mono hW2i hhi hW2
    _ = 1 + ∑ k, 2 ^ (2 * n) * (1 + ∫ ω, y (v k) (X ω) ^ (2 * n)) := by
        simp only [hh]
        rw [integral_add (integrable_const (1 : ℝ)) hS, integral_finsetSum _ fun k _ => hik k]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_add (integrable_const (1 : ℝ)) (H.mom (v k)).1, integral_const, probReal_univ,
          smul_eq_mul, one_mul]
    _ ≤ 1 + ∑ _k : Fin n, 2 ^ (2 * n) * (1 + Cm) := by
        gcongr with k
        exact (H.mom (v k)).2
    _ = 1 + n * 2 ^ (2 * n) * (1 + Cm) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The other labels of a tuple: `T_k = image v ∖ {v_k}`. -/
private def momT {ι : Type} [DecidableEq ι] {n : ℕ} (v : Fin n → ι) (k : Fin n) : Finset ι :=
  (Finset.univ.image v).erase (v k)

omit [Fintype ι] in
private theorem momT_card (v : Fin n → ι) (k : Fin n) : (momT v k).card + 1 ≤ n := by
  unfold momT
  have hk : v k ∈ Finset.univ.image v := Finset.mem_image_of_mem v (Finset.mem_univ k)
  rw [Finset.card_erase_of_mem hk]
  have h1 := moment_card_image_le v
  have h2 : 0 < (Finset.univ.image v).card := Finset.card_pos.2 ⟨v k, hk⟩
  omega

omit [Fintype ι] in
private theorem notMem_momT (v : Fin n → ι) (k : Fin n) : v k ∉ momT v k :=
  Finset.notMem_erase _ _

/-- The Möbius piece `Π_k c_k(Z^{[U_k]}_{v_k})` of a tuple `v` with sets `U_k ⊆ T_k`. -/
private def momPiece (X : Ω → Fin M → Fin N → ℝ)
    (Zs : Finset ι → ι → (Fin M → Fin N → ℝ) → ℂ) (b : Fin n → Bool) (v : Fin n → ι)
    (Us : Fin n → Finset ι) (ω : Ω) : ℂ :=
  ∏ k, momCj (b k) (mobPart (fun S => Zs S (v k) (X ω)) (momT v k) (Us k))

/-- A piece is measurable, bounded by `(2^n Kd)^n W_v`, and integrable. -/
private theorem MomHyp.piece_basic (H : MomHyp X π Zs y Kd n Cm) (b : Fin n → Bool)
    (v : Fin n → ι) (Us : Fin n → Finset ι) (hUs : ∀ k, Us k ⊆ momT v k) :
    Measurable (momPiece X Zs b v Us) ∧
    (∀ ω, ‖momPiece X Zs b v Us ω‖ ≤ (2 ^ n * Kd) ^ n * ∏ k, (1 + y (v k) (X ω))) ∧
    Integrable (momPiece X Zs b v Us) := by
  have hm : Measurable (momPiece X Zs b v Us) :=
    Finset.measurable_prod _ fun k _ =>
      (momCj_measurable _).comp ((H.mob_measurable _ _ _).comp H.meas)
  have hb : ∀ ω, ‖momPiece X Zs b v Us ω‖ ≤ (2 ^ n * Kd) ^ n * ∏ k, (1 + y (v k) (X ω)) := by
    intro ω
    unfold momPiece
    rw [norm_prod]
    simp only [momCj_norm]
    calc ∏ k, ‖mobPart (fun S => Zs S (v k) (X ω)) (momT v k) (Us k)‖
        ≤ ∏ k, (2 ^ n * Kd * (1 + y (v k) (X ω))) := by
          refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
          refine (H.mob_norm_le _ _ _ _).trans ?_
          have hc : (Us k).card ≤ n := by
            have := Finset.card_le_card (hUs k)
            have := momT_card v k
            omega
          have : (2 : ℝ) ^ (Us k).card ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hc
          have : 0 ≤ Kd * (1 + y (v k) (X ω)) :=
            mul_nonneg H.Kd0 (by linarith [H.y0 (v k) (X ω)])
          nlinarith
      _ = (2 ^ n * Kd) ^ n * ∏ k, (1 + y (v k) (X ω)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨-, -, hWi, -, -⟩ := H.W_props v
  refine ⟨hm, hb, (hWi.const_mul ((2 ^ n * Kd) ^ n)).mono' hm.aestronglyMeasurable
    (ae_of_all _ hb)⟩

/-- The vanishing of a piece in which a lone label `v_k` lies in no other `U_l`. -/
private theorem MomHyp.piece_vanish (H : MomHyp X π Zs y Kd n Cm) (b : Fin n → Bool)
    (v : Fin n → ι) (Us : Fin n → Finset ι) (hUs : ∀ k, Us k ⊆ momT v k) (k : Fin n)
    (hk : ∀ l, v l = v k → l = k) (hkU : ∀ l, l ≠ k → v k ∉ Us l) :
    ∫ ω, momPiece X Zs b v Us ω = 0 := by
  set F : (Fin M → Fin N → ℝ) → ℂ := fun Xm =>
    ∏ l ∈ Finset.univ.erase k, momCj (b l) (mobPart (fun S => Zs S (v l) Xm) (momT v l) (Us l))
    with hFdef
  have hFm : Measurable F :=
    Finset.measurable_prod _ fun l _ => (momCj_measurable _).comp (H.mob_measurable _ _ _)
  have hFc : ∀ Xm Xm' : Fin M → Fin N → ℝ, (∀ i ν, π i ν ≠ v k → Xm i ν = Xm' i ν) →
      F Xm = F Xm' := by
    intro Xm Xm' h
    refine Finset.prod_congr rfl fun l hl => ?_
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    congr 1
    refine H.congr (momT v l) (Us l) (v l) (notMem_momT v l) Xm Xm' fun i ν hiν => h i ν ?_
    intro hπ
    apply hiν
    rw [hπ, Finset.mem_sdiff]
    exact ⟨Finset.mem_erase.2 ⟨fun e => hlk (hk l e.symm),
      Finset.mem_image_of_mem v (Finset.mem_univ k)⟩, hkU l hlk⟩
  obtain ⟨hWm, hW1, hWi, -, -⟩ := H.W_props v
  set c : ℝ := (2 ^ n * Kd) ^ (Finset.univ.erase k).card with hcdef
  have hc0 : 0 ≤ c := pow_nonneg (mul_nonneg (by positivity) H.Kd0) _
  have hWsplit : ∀ ω, (1 + y (v k) (X ω)) * ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω))
      = ∏ l, (1 + y (v l) (X ω)) := fun ω =>
    Finset.mul_prod_erase Finset.univ (fun l => 1 + y (v l) (X ω)) (Finset.mem_univ k)
  have hPe : ∀ ω, 1 ≤ ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω)) := fun ω =>
    Finset.one_le_prod₀ fun l _ => le_add_of_nonneg_right (H.y0 _ _)
  have hyk : ∀ ω, 0 ≤ y (v k) (X ω) := fun ω => H.y0 _ _
  -- the bound on the other factors
  have hFb : ∀ ω, ‖F (X ω)‖ ≤ c * ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω)) := by
    intro ω
    simp only [hFdef]
    rw [norm_prod]
    simp only [momCj_norm]
    calc ∏ l ∈ Finset.univ.erase k, ‖mobPart (fun S => Zs S (v l) (X ω)) (momT v l) (Us l)‖
        ≤ ∏ l ∈ Finset.univ.erase k, (2 ^ n * Kd * (1 + y (v l) (X ω))) := by
          refine Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) fun l _ => ?_
          refine (H.mob_norm_le _ _ _ _).trans ?_
          have hc : (Us l).card ≤ n := by
            have := Finset.card_le_card (hUs l)
            have := momT_card v l
            omega
          have : (2 : ℝ) ^ (Us l).card ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hc
          have : 0 ≤ Kd * (1 + y (v l) (X ω)) :=
            mul_nonneg H.Kd0 (by linarith [H.y0 (v l) (X ω)])
          nlinarith
      _ = c * ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hFW : ∀ ω, ‖F (X ω)‖ ≤ c * ∏ l, (1 + y (v l) (X ω)) := by
    intro ω
    refine (hFb ω).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    rw [← hWsplit ω]
    nlinarith [hPe ω, hyk ω]
  have hFXm : Measurable fun ω => F (X ω) := hFm.comp H.meas
  set F' : (Fin M → Fin N → ℝ) → ℂ := fun Xm => momCj (b k) (F Xm) with hF'def
  have hF'm : Measurable F' := (momCj_measurable _).comp hFm
  have hF'c : ∀ Xm Xm' : Fin M → Fin N → ℝ, (∀ i ν, π i ν ≠ v k → Xm i ν = Xm' i ν) →
      F' Xm = F' Xm' := fun Xm Xm' h => by simp only [hF'def, hFc Xm Xm' h]
  have hF'i : Integrable fun ω => F' (X ω) :=
    (hWi.const_mul c).mono' (hF'm.comp H.meas).aestronglyMeasurable
      (ae_of_all _ fun ω => by simp only [hF'def, momCj_norm]; exact hFW ω)
  -- each term of the Möbius sum of factor `k` integrates to `0` against `F`
  have hterm : ∀ S : Finset ι, Integrable (fun ω => momCj (b k) (Zs S (v k) (X ω)) * F (X ω)) ∧
      ∫ ω, momCj (b k) (Zs S (v k) (X ω)) * F (X ω) = 0 := by
    intro S
    refine ⟨?_, ?_⟩
    · refine ((hWi.const_mul (Kd * c))).mono'
        (((momCj_measurable _).comp ((H.measZ _ _).comp H.meas)).mul hFXm).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [norm_mul, momCj_norm, ← hWsplit ω]
      have h1 := H.det S (v k) (X ω)
      have h2 := hFb ω
      have h3 : 0 ≤ ‖F (X ω)‖ := norm_nonneg _
      calc ‖Zs S (v k) (X ω)‖ * ‖F (X ω)‖
          ≤ (Kd * (1 + y (v k) (X ω))) * (c * ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω))) :=
            mul_le_mul h1 h2 h3 (mul_nonneg H.Kd0 (by linarith [hyk ω]))
        _ = Kd * c * ((1 + y (v k) (X ω)) * ∏ l ∈ Finset.univ.erase k, (1 + y (v l) (X ω))) := by
            ring
    · have e : ∀ ω, momCj (b k) (Zs S (v k) (X ω)) * F (X ω)
          = momCj (b k) (Zs S (v k) (X ω) * F' (X ω)) := fun ω => by
        simp only [hF'def, map_mul, momCj_invol]
      simp only [e]
      rw [momCj_integral, H.van S (v k) F' hF'm hF'c hF'i, map_zero]
  -- the expansion of the piece
  have hP : ∀ ω, momPiece X Zs b v Us ω = ∑ V ∈ (Us k).powerset,
      momCj (b k) ((-1 : ℂ) ^ ((Us k).card - V.card)) *
        (momCj (b k) (Zs (momT v k \ V) (v k) (X ω)) * F (X ω)) := by
    intro ω
    unfold momPiece
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    simp only [hFdef, mobPart, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun V _ => ?_
    ring
  simp only [hP]
  rw [integral_finsetSum _ fun V _ => (hterm _).1.const_mul _]
  refine Finset.sum_eq_zero fun V _ => ?_
  rw [integral_const_mul, (hterm _).2, mul_zero]

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] [Fintype ι] in
/-- On the good event, a piece in which every lone label lies in some `U_l` is at most
`K^n δ^{n + s(v)}`. -/
private theorem piece_good {G : Set Ω} {K δ : ℝ} (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ ω ∈ G, ∀ (T U : Finset ι) (s : ι), s ∉ T → T.card + 1 ≤ n → U ⊆ T →
      ‖mobPart (fun S => Zs S s (X ω)) T U‖ ≤ K * δ ^ (U.card + 1))
    (b : Fin n → Bool) (v : Fin n → ι) (Us : Fin n → Finset ι) (hUs : ∀ k, Us k ⊆ momT v k)
    (hnv : ∀ k, (∀ l, v l = v k → l = k) → ∃ l, v k ∈ Us l) (ω : Ω) (hω : ω ∈ G) :
    ‖momPiece X Zs b v Us ω‖ ≤ K ^ n * δ ^ (n + loneCount v) := by
  have hs : loneCount v ≤ ∑ k, (Us k).card := by
    set Lo := Finset.univ.filter fun k => ∀ l, v l = v k → l = k with hLo
    have hinj : Set.InjOn v Lo := by
      intro k _ k' hk' e
      exact (Finset.mem_filter.1 hk').2 k e
    have hsub : Lo.image v ⊆ Finset.univ.biUnion Us := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨l, hl⟩ := hnv k (Finset.mem_filter.1 hk).2
      exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hl⟩
    calc loneCount v = Lo.card := rfl
      _ = (Lo.image v).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ.biUnion Us).card := Finset.card_le_card hsub
      _ ≤ ∑ k, (Us k).card := Finset.card_biUnion_le
  unfold momPiece
  rw [norm_prod]
  simp only [momCj_norm]
  calc ∏ k, ‖mobPart (fun S => Zs S (v k) (X ω)) (momT v k) (Us k)‖
      ≤ ∏ k, (K * δ ^ ((Us k).card + 1)) :=
        Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ =>
          hgood ω hω _ _ _ (notMem_momT v k) (momT_card v k) (hUs k)
    _ = K ^ n * δ ^ (∑ k, (Us k).card + n) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
        simp
    _ ≤ K ^ n * δ ^ (n + loneCount v) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ0 hδ1 (by omega)) (by positivity)

/-- A piece integrates to at most `K^n δ^{n+s(v)} + β`, where
`β = (2^n Kd)^{2n} (1 + n 2^{2n} (1 + Cm)) / R + R εb` bounds the part off the good event `G`. -/
private theorem MomHyp.piece_bound (H : MomHyp X π Zs y Kd n Cm) {G : Set Ω} {εb K δ R : ℝ}
    (hεb : 0 ≤ εb) (hG : ℙ Gᶜ ≤ ENNReal.ofReal εb) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ ω ∈ G, ∀ (T U : Finset ι) (s : ι), s ∉ T → T.card + 1 ≤ n → U ⊆ T →
      ‖mobPart (fun S => Zs S s (X ω)) T U‖ ≤ K * δ ^ (U.card + 1))
    (hR : 0 < R) (b : Fin n → Bool) (v : Fin n → ι) (Us : Fin n → Finset ι)
    (hUs : ∀ k, Us k ⊆ momT v k) :
    Integrable (momPiece X Zs b v Us) ∧
    ‖∫ ω, momPiece X Zs b v Us ω‖ ≤ K ^ n * δ ^ (n + loneCount v) +
      ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb) := by
  obtain ⟨-, hPb, hPi⟩ := H.piece_basic b v Us hUs
  obtain ⟨-, -, -, hW2i, hW2⟩ := H.W_props v
  refine ⟨hPi, ?_⟩
  have hKd := H.Kd0
  have hCm := H.Cm0
  have hg0 : 0 ≤ K ^ n * δ ^ (n + loneCount v) := by positivity
  have hβ0 : 0 ≤ (2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb := by
    positivity
  by_cases hv : ∃ k, (∀ l, v l = v k → l = k) ∧ ∀ l, l ≠ k → v k ∉ Us l
  · obtain ⟨k, hk, hkU⟩ := hv
    rw [H.piece_vanish b v Us hUs k hk hkU, norm_zero]
    linarith
  · push Not at hv
    have hnv : ∀ k, (∀ l, v l = v k → l = k) → ∃ l, v k ∈ Us l := fun k hk => by
      obtain ⟨l, -, hl⟩ := hv k hk
      exact ⟨l, hl⟩
    set E := toMeasurable ℙ Gᶜ with hEdef
    have hE : MeasurableSet E := measurableSet_toMeasurable _ _
    set g := K ^ n * δ ^ (n + loneCount v) with hgdef
    set c := (2 ^ n * Kd) ^ n with hcdef
    have hpt : ∀ ω, ‖momPiece X Zs b v Us ω‖ ≤
        g + c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 + R * E.indicator 1 ω := by
      intro ω
      have hW0 : 0 ≤ ∏ k, (1 + y (v k) (X ω)) :=
        Finset.prod_nonneg fun k _ => by linarith [H.y0 (v k) (X ω)]
      have hq : 0 ≤ c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 := by positivity
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        have hB := hPb ω
        have hB0 : 0 ≤ c * ∏ k, (1 + y (v k) (X ω)) := (norm_nonneg _).trans hB
        have : c * ∏ k, (1 + y (v k) (X ω)) ≤
            c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 + R := by
          rw [div_mul_eq_mul_div, div_add' _ _ _ hR.ne', le_div_iff₀ hR]
          nlinarith [sq_nonneg (c * ∏ k, (1 + y (v k) (X ω)) - R)]
        linarith
      · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
        have hωG : ω ∈ G := by
          by_contra h
          exact hω (subset_toMeasurable _ _ h)
        have := piece_good hK hδ0 hδ1 hgood b v Us hUs hnv ω hωG
        linarith
    have hindi : Integrable (E.indicator (1 : Ω → ℝ)) := (integrable_const (1 : ℝ)).indicator hE
    have hA : Integrable fun ω => g + c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 :=
      (integrable_const g).add (hW2i.const_mul _)
    have hbi : Integrable fun ω =>
        g + c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 + R * E.indicator 1 ω :=
      hA.add (hindi.const_mul R)
    calc ‖∫ ω, momPiece X Zs b v Us ω‖ ≤ ∫ ω, ‖momPiece X Zs b v Us ω‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (g + c ^ 2 / R * (∏ k, (1 + y (v k) (X ω))) ^ 2 + R * E.indicator 1 ω) :=
          integral_mono hPi.norm hbi hpt
      _ = g + c ^ 2 / R * (∫ ω, (∏ k, (1 + y (v k) (X ω))) ^ 2) + R * (ℙ E).toReal := by
          rw [integral_add hA (hindi.const_mul R),
            integral_add (integrable_const g) (hW2i.const_mul _), integral_const,
            integral_const_mul, integral_const_mul, integral_indicator_one hE, probReal_univ,
            smul_eq_mul, one_mul, measureReal_def]
      _ ≤ g + c ^ 2 / R * (1 + n * 2 ^ (2 * n) * (1 + Cm)) + R * εb := by
          gcongr
          rw [hEdef, measure_toMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hεb hG
      _ = g + ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb) := by
          rw [show (2 ^ n * Kd) ^ (2 * n) = c ^ 2 by rw [hcdef, mul_comm 2 n, pow_mul]]
          ring

/-- One tuple: `|E Π_k c_k(Z_{v_k})| ≤ 2^{n(n−1)} (K^n δ^{n+s(v)} + β)`. -/
private theorem MomHyp.tuple_bound (H : MomHyp X π Zs y Kd n Cm) {G : Set Ω} {εb K δ R : ℝ}
    (hεb : 0 ≤ εb) (hG : ℙ Gᶜ ≤ ENNReal.ofReal εb) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ ω ∈ G, ∀ (T U : Finset ι) (s : ι), s ∉ T → T.card + 1 ≤ n → U ⊆ T →
      ‖mobPart (fun S => Zs S s (X ω)) T U‖ ≤ K * δ ^ (U.card + 1))
    (hR : 0 < R) (b : Fin n → Bool) (v : Fin n → ι) :
    Integrable (fun ω => ∏ k, momCj (b k) (Zs ∅ (v k) (X ω))) ∧
    ‖∫ ω, ∏ k, momCj (b k) (Zs ∅ (v k) (X ω))‖ ≤ 2 ^ (n * (n - 1)) *
      (K ^ n * δ ^ (n + loneCount v) +
        ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb)) := by
  set P := Fintype.piFinset fun k => (momT v k).powerset with hPdef
  have hexp : ∀ ω, ∏ k, momCj (b k) (Zs ∅ (v k) (X ω)) =
      ∑ Us ∈ P, momPiece X Zs b v Us ω := by
    intro ω
    unfold momPiece
    calc ∏ k, momCj (b k) (Zs ∅ (v k) (X ω))
        = ∏ k, ∑ U ∈ (momT v k).powerset,
            momCj (b k) (mobPart (fun S => Zs S (v k) (X ω)) (momT v k) U) :=
          Finset.prod_congr rfl fun k _ => by rw [← map_sum, sum_mobPart]
      _ = _ := Finset.prod_univ_sum _ _
  have hUs : ∀ Us ∈ P, ∀ k, Us k ⊆ momT v k := fun Us hUs k =>
    Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hUs k)
  have hb := fun Us (hU : Us ∈ P) =>
    H.piece_bound hεb hG hK hδ0 hδ1 hgood hR b v Us (hUs Us hU)
  simp only [hexp]
  refine ⟨integrable_finsetSum _ fun Us hU => (hb Us hU).1, ?_⟩
  rw [integral_finsetSum _ fun Us hU => (hb Us hU).1]
  have hcard : P.card ≤ 2 ^ (n * (n - 1)) := by
    rw [hPdef, Fintype.card_piFinset]
    calc ∏ k, ((momT v k).powerset).card ≤ ∏ _k : Fin n, 2 ^ (n - 1) := by
          refine Finset.prod_le_prod fun k _ => ?_
          rw [Finset.card_powerset]
          exact Nat.pow_le_pow_right two_pos (by have := momT_card v k; omega)
      _ = 2 ^ (n * (n - 1)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hKd := H.Kd0
  have hCm := H.Cm0
  have hβ0 : 0 ≤ K ^ n * δ ^ (n + loneCount v) +
      ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb) := by
    positivity
  calc ‖∑ Us ∈ P, ∫ ω, momPiece X Zs b v Us ω‖ ≤ ∑ Us ∈ P, ‖∫ ω, momPiece X Zs b v Us ω‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _Us ∈ P, (K ^ n * δ ^ (n + loneCount v) +
          ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb)) :=
        Finset.sum_le_sum fun Us hU => (hb Us hU).2
    _ = P.card * (K ^ n * δ ^ (n + loneCount v) +
          ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (n * (n - 1)) * (K ^ n * δ ^ (n + loneCount v) +
          ((2 ^ n * Kd) ^ (2 * n) * (1 + n * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb)) := by
        gcongr
        exact_mod_cast hcard

/-- The `2p`-th moment of `L⁻¹ Σ_s a_s Z_s` (`L = |ι|`, `|a| ≤ A`):
`E|·|^{2p} ≤ A^{2p} 2^{2p(2p−1)} (K^{2p} Σ_v L^{-2p} δ^{2p+s(v)} + β)`. -/
private theorem MomHyp.moment {p : ℕ} (H : MomHyp X π Zs y Kd (2 * p) Cm)
    (hι : 0 < Fintype.card ι) {G : Set Ω} {εb K δ R : ℝ}
    (hεb : 0 ≤ εb) (hG : ℙ Gᶜ ≤ ENNReal.ofReal εb) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ ω ∈ G, ∀ (T U : Finset ι) (s : ι), s ∉ T → T.card + 1 ≤ 2 * p → U ⊆ T →
      ‖mobPart (fun S => Zs S s (X ω)) T U‖ ≤ K * δ ^ (U.card + 1))
    (hR : 0 < R) {A : ℝ} (a : ι → ℂ) (ha : ∀ s, ‖a s‖ ≤ A) :
    Integrable (fun ω => ‖(Fintype.card ι : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ (2 * p)) ∧
    ∫ ω, ‖(Fintype.card ι : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ (2 * p) ≤
      A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
        (K ^ (2 * p) * ∑ v : Fin (2 * p) → ι,
            ((Fintype.card ι : ℝ)⁻¹) ^ (2 * p) * δ ^ (2 * p + loneCount v) +
          ((2 ^ (2 * p) * Kd) ^ (2 * (2 * p)) *
            (1 + ((2 * p : ℕ) : ℝ) * 2 ^ (2 * (2 * p)) * (1 + Cm)) / R + R * εb)) := by
  set n := 2 * p with hn
  set L : ℕ := Fintype.card ι with hL
  set b := momPat p
  set β := (2 ^ n * Kd) ^ (2 * n) * (1 + (n : ℝ) * 2 ^ (2 * n) * (1 + Cm)) / R + R * εb with hβ
  have hne : Nonempty ι := Fintype.card_pos_iff.1 hι
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (ha (Classical.arbitrary ι))
  have ht := fun v => H.tuple_bound hεb hG hK hδ0 hδ1 hgood hR b v
  set c : (Fin n → ι) → ℂ := fun v => ∏ k, momCj (b k) (a (v k)) with hc
  set f : (Fin n → ι) → Ω → ℂ := fun v ω => ∏ k, momCj (b k) (Zs ∅ (v k) (X ω)) with hf
  set Φ : Ω → ℂ := fun ω => ((L : ℂ)⁻¹) ^ n * ∑ v, c v * f v ω with hΦdef
  have hΦ : ∀ ω, ((‖(L : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ n : ℝ) : ℂ) = Φ ω := by
    intro ω
    rw [← prod_momPat p]
    simp only [hΦdef, hc, hf, map_mul, map_sum, map_inv₀, map_natCast, Finset.prod_mul_distrib,
      Fintype.prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hΦi : Integrable Φ :=
    (integrable_finsetSum _ fun v _ => (ht v).1.const_mul (c v)).const_mul _
  have hnorm : ∀ ω, ‖Φ ω‖ = ‖(L : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ n := by
    intro ω
    rw [← hΦ ω, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine ⟨hΦi.norm.congr (ae_of_all _ hnorm), ?_⟩
  have hint : ((∫ ω, ‖(L : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ n : ℝ) : ℂ) = ∫ ω, Φ ω := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ hΦ)
  have hcv : ∀ v, ‖c v‖ ≤ A ^ n := by
    intro v
    simp only [hc]
    rw [norm_prod]
    simp only [momCj_norm]
    calc ∏ k, ‖a (v k)‖ ≤ ∏ _k : Fin n, A :=
          Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ha _
      _ = A ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 hι
  have hsum1 : ∑ _v : Fin n → ι, ((L : ℝ)⁻¹) ^ n = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_pow, mul_inv_cancel₀ hL0.ne', one_pow]
  have hKd := H.Kd0
  have hCm := H.Cm0
  have hβ0 : 0 ≤ β := by positivity
  calc ∫ ω, ‖(L : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ n
      ≤ ‖((∫ ω, ‖(L : ℂ)⁻¹ * ∑ s, a s * Zs ∅ s (X ω)‖ ^ n : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_abs_self _
    _ = ‖((L : ℂ)⁻¹) ^ n * ∑ v, c v * ∫ ω, f v ω‖ := by
        rw [hint, hΦdef, integral_const_mul, integral_finsetSum _ fun v _ => (ht v).1.const_mul _]
        simp only [integral_const_mul]
        rfl
    _ ≤ ((L : ℝ)⁻¹) ^ n * ∑ v, A ^ n * (2 ^ (n * (n - 1)) *
          (K ^ n * δ ^ (n + loneCount v) + β)) := by
        rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hcv v) (ht v).2 (norm_nonneg _) (by positivity)
    _ = A ^ n * 2 ^ (n * (n - 1)) * (K ^ n * ∑ v : Fin n → ι,
          ((L : ℝ)⁻¹) ^ n * δ ^ (n + loneCount v) + (∑ _v : Fin n → ι, ((L : ℝ)⁻¹) ^ n) * β) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ = _ := by rw [hsum1, one_mul]

end Core

/-! ## Column and row labels -/

private theorem moment_measurable_Xhat {N : ℕ} (s t : Fin M ⊕ Fin N) :
    Measurable fun Xm : Fin M → Fin N → ℝ => Xhat (Xm : Matrix (Fin M) (Fin N) ℝ) s t := by
  rcases s with i | μ <;> rcases t with j | ν <;>
    simp only [Xhat, cplx, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply] <;>
    first
    | exact measurable_const
    | exact Complex.measurable_ofReal.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

private theorem moment_measurable_Gm {N : ℕ} (σ : Fin M → ℝ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (s t : Fin M ⊕ Fin N) :
    Measurable fun Xm : Fin M → Fin N → ℝ =>
      Gm (diagonal σ) (Xm : Matrix (Fin M) (Fin N) ℝ) z T s t :=
  measurable_Gm_apply σ (X := fun Xm : Fin M → Fin N → ℝ => (Xm : Matrix (Fin M) (Fin N) ℝ))
    (fun i ν => (measurable_pi_apply ν).comp (measurable_pi_apply i)) z T s t

private theorem moment_measurable_ZmuS {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (S : Finset (Fin N))
    (μ : Fin N) : Measurable fun Xm : Fin M → Fin N → ℝ => ZmuS σ Xm z S μ := by
  unfold ZmuS
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact (Finset.measurable_sum _ fun t _ => (Finset.measurable_sum _ fun s _ =>
    (moment_measurable_Xhat _ _).mul (moment_measurable_Gm _ _ _ _ _)).mul
      (moment_measurable_Xhat _ _)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => moment_measurable_Gm _ _ _ _ _))

private theorem moment_measurable_ZiS {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (S : Finset (Fin M))
    (i : Fin M) : Measurable fun Xm : Fin M → Fin N → ℝ => ZiS σ Xm z S i := by
  unfold ZiS
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact (Finset.measurable_sum _ fun t _ => (Finset.measurable_sum _ fun s _ =>
    (moment_measurable_Xhat _ _).mul (moment_measurable_Gm _ _ _ _ _)).mul
      (moment_measurable_Xhat _ _)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun ν _ => moment_measurable_Gm _ _ _ _ _))

/-- `N ≥ 1`, `M ≥ 1` and `τ ≤ 1` under `DiagModel` with `τ > 0`. -/
private theorem moment_dims {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {Ω : Type*}
    [MeasureSpace Ω] {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hτ : 0 < τ)
    (hX : DiagModel τ C M N σ X) : 1 ≤ N ∧ 1 ≤ M ∧ τ ≤ 1 := by
  have h1 : (0 : ℝ) < M / N := hτ.trans_le hX.ratio_ge
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.2 fun h => ?_
    rw [h, Nat.cast_zero, div_zero] at h1
    exact lt_irrefl 0 h1
  · refine Nat.one_le_iff_ne_zero.2 fun h => ?_
    rw [h, Nat.cast_zero, zero_div] at h1
    exact lt_irrefl 0 h1
  · have h2 : τ ≤ τ⁻¹ := hX.ratio_ge.trans hX.ratio_le
    by_contra h3
    push Not at h3
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h3
    linarith

/-- `0 < c_as` and `0 ≤ C_as`, hence `K_Z(p), K_L(p) ≥ 0`. -/
private theorem moment_consts_nonneg {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (p : ℕ) :
    0 < mAsympLower τ ∧ 0 ≤ mobConst p τ c ∧ 0 ≤ ldeZConst p τ c := by
  have hC : 0 < mBoundConst τ := by
    unfold mBoundConst genPropConst
    exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)
  have hcas : 0 < mAsympLower τ := by
    unfold mAsympLower
    have := mul_pos hC (inv_pos.2 hτ)
    exact inv_pos.2 (by linarith)
  have hCas : 0 ≤ mAsympUpper c τ + 1 := by
    have : 0 ≤ mAsympUpper c τ := (inv_pos.2 hc).le.trans (le_max_left _ _)
    linarith
  have hti : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  refine ⟨hcas, ?_, ?_⟩
  · unfold mobConst
    refine mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (pow_nonneg ?_ _))
      (pow_nonneg hti _)
    exact mul_nonneg (mul_nonneg (by positivity) hCas) (div_nonneg (by norm_num) hcas.le)
  · unfold ldeZConst
    exact mul_nonneg (mul_nonneg (by positivity) hCas) (pow_nonneg hti _)

/-- On `FaGood` and under (G*), the Möbius pieces of a column label `μ ∉ T`, `|T| + 1 ≤ 2p`,
`U ⊆ T`, are at most `(K_Z + K_L) (N^{ε₁+ε_L}Υ)^{|U|+1}`. -/
private theorem moment_good_col {τ c c₀ ε₁ εL Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) {z : ℂ} (hz : z ∈ specDomain τ N)
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 1 ≤ N) (hε₁ : 0 ≤ ε₁)
    (hε₁c₀ : ε₁ ≤ c₀ / 2) (hεL : 0 ≤ εL) (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ)
    (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hgood : FaGood σ Xm z p c₀ ε₁ εL Υ)
    (T U : Finset (Fin N)) (μ : Fin N) (hμ : μ ∉ T) (hT : T.card + 1 ≤ 2 * p) (hU : U ⊆ T) :
    ‖mobPart (fun S => ZmuS σ Xm z S μ) T U‖ ≤
      (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (U.card + 1) := by
  obtain ⟨-, hKZ, hKL⟩ := moment_consts_nonneg h.pos hc p
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hΥ : 0 ≤ Υ := le_trans (by positivity) hΥN
  have hNL : 1 ≤ (N : ℝ) ^ εL := Real.one_le_rpow (Nat.one_le_cast.2 hN) hεL
  have hd0 : 0 ≤ (N : ℝ) ^ ε₁ * Υ := by positivity
  have hδ : (N : ℝ) ^ (ε₁ + εL) * Υ = (N : ℝ) ^ εL * ((N : ℝ) ^ ε₁ * Υ) := by
    rw [Real.rpow_add hN0]
    ring
  have hle : (N : ℝ) ^ ε₁ * Υ ≤ (N : ℝ) ^ (ε₁ + εL) * Υ := by
    rw [hδ]
    nlinarith
  obtain ⟨hΛ, hΛo, hcol, -⟩ := hgood
  rcases U.eq_empty_or_nonempty with rfl | hne
  · rw [mobPart_empty]
    have h1 := hcol T μ hμ hT
    have h2 := ldeZCol_le hc h hσ Xm hz hx hε₁ hε₁c₀ hΥN hΥc₀ hG hΛ hΛo T hT μ hμ
    calc ‖ZmuS σ Xm z T μ‖ ≤ (N : ℝ) ^ εL * ldeZCol σ Xm z T μ := h1
      _ ≤ (N : ℝ) ^ εL * (ldeZConst p τ c * ((N : ℝ) ^ ε₁ * Υ)) := by gcongr
      _ = ldeZConst p τ c * ((N : ℝ) ^ (ε₁ + εL) * Υ) := by rw [hδ]; ring
      _ ≤ (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (0 + 1) := by
          rw [zero_add, pow_one]
          gcongr
          linarith
      _ = _ := by rw [Finset.card_empty]
  · have h1 : ‖ZmuMob σ Xm z T U μ‖ ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) :=
      ZmuMob_bound hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo T U hT hU hne μ hμ
    calc ‖mobPart (fun S => ZmuS σ Xm z S μ) T U‖
        ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) := h1
      _ ≤ (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (U.card + 1) := by
          gcongr
          linarith

/-- The row version of `moment_good_col`. -/
private theorem moment_good_row {τ c c₀ ε₁ εL Υ : ℝ} (hc : 0 < c) {p N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) {z : ℂ} (hz : z ∈ specDomain τ N)
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (hN : 1 ≤ N) (hε₁ : 0 ≤ ε₁)
    (hε₁c₀ : ε₁ ≤ c₀ / 2) (hεL : 0 ≤ εL) (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ)
    (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hgood : FaGood σ Xm z p c₀ ε₁ εL Υ)
    (T U : Finset (Fin M)) (i : Fin M) (hi : i ∉ T) (hT : T.card + 1 ≤ 2 * p) (hU : U ⊆ T) :
    ‖mobPart (fun S => ZiS σ Xm z S i) T U‖ ≤
      (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (U.card + 1) := by
  obtain ⟨-, hKZ, hKL⟩ := moment_consts_nonneg h.pos hc p
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hΥ : 0 ≤ Υ := le_trans (by positivity) hΥN
  have hNL : 1 ≤ (N : ℝ) ^ εL := Real.one_le_rpow (Nat.one_le_cast.2 hN) hεL
  have hd0 : 0 ≤ (N : ℝ) ^ ε₁ * Υ := by positivity
  have hδ : (N : ℝ) ^ (ε₁ + εL) * Υ = (N : ℝ) ^ εL * ((N : ℝ) ^ ε₁ * Υ) := by
    rw [Real.rpow_add hN0]
    ring
  have hle : (N : ℝ) ^ ε₁ * Υ ≤ (N : ℝ) ^ (ε₁ + εL) * Υ := by
    rw [hδ]
    nlinarith
  obtain ⟨hΛ, hΛo, -, hrow⟩ := hgood
  rcases U.eq_empty_or_nonempty with rfl | hne
  · rw [mobPart_empty]
    have h1 := hrow T i hi hT
    have h2 := ldeZRow_le hc h hσ Xm hz hx hε₁ hε₁c₀ hΥN hΥc₀ hG hΛ hΛo T hT i hi
    calc ‖ZiS σ Xm z T i‖ ≤ (N : ℝ) ^ εL * ldeZRow σ Xm z T i := h1
      _ ≤ (N : ℝ) ^ εL * (ldeZConst p τ c * ((N : ℝ) ^ ε₁ * Υ)) := by gcongr
      _ = ldeZConst p τ c * ((N : ℝ) ^ (ε₁ + εL) * Υ) := by rw [hδ]; ring
      _ ≤ (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (0 + 1) := by
          rw [zero_add, pow_one]
          gcongr
          linarith
      _ = _ := by rw [Finset.card_empty]
  · have h1 : ‖ZiMob σ Xm z T U i‖ ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) :=
      ZiMob_bound hc h hσ Xm hz hx hε₁ hε₁c₀ hΥ hΥc₀ hG hΛ hΛo T U hT hU hne i hi
    calc ‖mobPart (fun S => ZiS σ Xm z S i) T U‖
        ≤ mobConst p τ c * ((N : ℝ) ^ ε₁ * Υ) ^ (U.card + 1) := h1
      _ ≤ (mobConst p τ c + ldeZConst p τ c) * ((N : ℝ) ^ (ε₁ + εL) * Υ) ^ (U.card + 1) := by
          gcongr
          linarith

/-! ## The exponent bookkeeping of the moment bound -/

/-- `Σ_v L^{-n} (PΥ)^{n+s(v)} ≤ P^{2n} n^n κ^n Υ^{2n}` for `P ≥ 1` (`sum_tuples_le`). -/
private theorem moment_good_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) {n : ℕ} {P Υ κ : ℝ} (hP : 1 ≤ P) (hΥ : 0 ≤ Υ) (hκ : 1 ≤ κ)
    (h : (Fintype.card ι : ℝ) ^ (-(1 / 2 : ℝ)) ≤ κ * Υ) :
    ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ n * (P * Υ) ^ (n + loneCount v) ≤
      P ^ (2 * n) * ((n : ℝ) ^ n * κ ^ n * Υ ^ (2 * n)) := by
  calc ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ n * (P * Υ) ^ (n + loneCount v)
      ≤ ∑ v : Fin n → ι, P ^ (2 * n) * (((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v)) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [mul_pow, mul_left_comm]
        have : P ^ (n + loneCount v) ≤ P ^ (2 * n) :=
          pow_le_pow_right₀ hP (by have := loneCount_le v; omega)
        have : 0 ≤ ((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v) := by positivity
        nlinarith
    _ = P ^ (2 * n) * ∑ v : Fin n → ι, ((Fintype.card ι : ℝ)⁻¹) ^ n * Υ ^ (n + loneCount v) := by
        rw [Finset.mul_sum]
    _ ≤ P ^ (2 * n) * ((n : ℝ) ^ n * κ ^ n * Υ ^ (2 * n)) := by
        have : 0 ≤ P := by linarith
        gcongr
        exact sum_tuples_le hι hΥ hκ h

/-- The part off the good event: with `R = N^{6p+1/2}`, `ε_b = N^{-(D₁-1)}`, `D₁ ≥ 8p + 2` and
`A^{2p} 2^{2p(2p−1)} ((2^{2p} K)^{4p} Q + 1) ≤ N^{1/2}`, it is at most `Υ^{4p}`. -/
private theorem moment_bad {p N : ℕ} {A Kdet Qw D₁ Υ : ℝ} (hN : 1 ≤ N)
    (hD₁ : 8 * (p : ℝ) + 2 ≤ D₁) (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ)
    (hBc : A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
      ((2 ^ (2 * p) * Kdet) ^ (2 * (2 * p)) * Qw + 1) ≤ (N : ℝ) ^ (1 / 2 : ℝ)) :
    A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
      ((2 ^ (2 * p) * (Kdet * N)) ^ (2 * (2 * p)) * Qw / (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) +
        (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) * (N : ℝ) ^ (-(D₁ - 1))) ≤ Υ ^ (2 * (2 * p)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  set e : ℝ := (N : ℝ) ^ (-(2 * (p : ℝ) + 1 / 2)) with he
  have he0 : 0 ≤ e := by positivity
  have hAT : 0 ≤ A ^ (2 * p) * (2 : ℝ) ^ (2 * p * (2 * p - 1)) := by
    rw [pow_mul]
    positivity
  have h1 : (2 ^ (2 * p) * (Kdet * N)) ^ (2 * (2 * p)) * Qw / (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2)
      = (2 ^ (2 * p) * Kdet) ^ (2 * (2 * p)) * Qw * e := by
    have : (N : ℝ) ^ (2 * (2 * p)) / (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) = e := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hN0, he]
      congr 1
      push_cast
      ring
    rw [← this, ← mul_assoc, mul_pow]
    ring
  have h2 : (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) * (N : ℝ) ^ (-(D₁ - 1)) ≤ e := by
    rw [← Real.rpow_add hN0, he]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3 : (N : ℝ) ^ (1 / 2 : ℝ) * e = ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 * (2 * p)) := by
    rw [he, ← Real.rpow_add hN0, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hΥ0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
        ((2 ^ (2 * p) * (Kdet * N)) ^ (2 * (2 * p)) * Qw / (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) +
          (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) * (N : ℝ) ^ (-(D₁ - 1)))
      ≤ A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
          ((2 ^ (2 * p) * Kdet) ^ (2 * (2 * p)) * Qw * e + e) := by
        rw [h1]
        gcongr
    _ = A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
          ((2 ^ (2 * p) * Kdet) ^ (2 * (2 * p)) * Qw + 1) * e := by ring
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * e := by gcongr
    _ = ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 * (2 * p)) := h3
    _ ≤ Υ ^ (2 * (2 * p)) := pow_le_pow_left₀ hΥ0 hΥN _

/-- The final combination of the good and bad parts. -/
private theorem moment_combine {E A K Sv β P nn κn τp U T : ℝ} {n : ℕ} (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hP : 1 ≤ P) (hnn : 0 ≤ nn) (hU : 0 ≤ U) (hκ : κn ≤ τp)
    (hE : E ≤ A ^ n * T * (K ^ n * Sv + β)) (hS : Sv ≤ P * (nn * κn * U))
    (hβ : A ^ n * T * β ≤ U) :
    E ≤ (nn * T * τp * (A * K) ^ n + 1) * P * U := by
  have hAK : 0 ≤ A ^ n * T * K ^ n := by positivity
  calc E ≤ A ^ n * T * K ^ n * Sv + A ^ n * T * β := by linarith [hE]
    _ ≤ A ^ n * T * K ^ n * (P * (nn * κn * U)) + U := by gcongr
    _ ≤ A ^ n * T * K ^ n * (P * (nn * τp * U)) + P * U := by
        have hP0 : 0 ≤ P := by linarith
        gcongr
        nlinarith
    _ = (nn * T * τp * (A * K) ^ n + 1) * P * U := by rw [mul_pow]; ring

/-! ## The moment bound -/

/-- (e), the moment bound: `E|N⁻¹ Σ_μ a_μ Z_μ|^{2p}`, `E|M⁻¹ Σ_i a_i Z_i|^{2p}
≤ C_p N^{4p(ε₁+ε_L)} Υ^{4p}` for deterministic weights `|a| ≤ A`. -/
theorem fa_moment (τ c c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (ε₁ εL D₁ A : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hc₀ : 0 < c₀) (hε₁ : 0 ≤ ε₁) (hε₁c₀ : ε₁ ≤ c₀ / 2) (hεL : 0 < εL) (hεLc₀ : εL ≤ c₀ / 2)
    (hD₁ : 8 * (p : ℝ) + 2 ≤ D₁) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-c₀) →
      DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-c₀)) →
      DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
      (∀ a : Fin N → ℂ, (∀ μ, ‖a μ‖ ≤ A) →
        Integrable (fun ω => ‖ZavgN σ (X ω) z a‖ ^ (2 * p)) ∧
        ∫ ω, ‖ZavgN σ (X ω) z a‖ ^ (2 * p) ≤
          faMomConst p τ c A * (N : ℝ) ^ (4 * (p : ℝ) * (ε₁ + εL)) * Υ ^ (4 * p)) ∧
      (∀ a : Fin M → ℂ, (∀ i, ‖a i‖ ≤ A) →
        Integrable (fun ω => ‖ZavgM σ (X ω) z a‖ ^ (2 * p)) ∧
        ∫ ω, ‖ZavgM σ (X ω) z a‖ ^ (2 * p) ≤
          faMomConst p τ c A * (N : ℝ) ^ (4 * (p : ℝ) * (ε₁ + εL)) * Υ ^ (4 * p)) := by
  obtain ⟨N₁, hN₁⟩ := faGood_highProb τ c₀ C p ε₁ εL D₁ hτ hεL
  have hti0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  obtain ⟨hcas, hKZ, hKL⟩ := moment_consts_nonneg hτ hc p
  set Cm : ℝ := (τ⁻¹ ^ (2 * (2 * p)) + 1) * |C (2 * (2 * (2 * p)))| with hCm
  have hCm0 : 0 ≤ Cm := mul_nonneg (add_nonneg (pow_nonneg hti0 _) zero_le_one) (abs_nonneg _)
  set Qw : ℝ := 1 + ((2 * p : ℕ) : ℝ) * 2 ^ (2 * (2 * p)) * (1 + Cm) with hQw
  set Bc : ℝ := A ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) *
    ((2 ^ (2 * p) * detZConst τ) ^ (2 * (2 * p)) * Qw + 1) with hBc
  set xG : ℝ := 4 ^ (p + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ with hxG
  have hx0 : 0 ≤ xG := mul_nonneg (by positivity) (inv_nonneg.2 hcas.le)
  refine ⟨max N₁ (max ⌈xG ^ (2 / c₀)⌉₊ ⌈Bc ^ 2⌉₊),
    fun N hN Ω _ _ M σ X hX z hz hx Υ hΥN hΥc₀ hΛ hΛo => ?_⟩
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNG : ⌈xG ^ (2 / c₀)⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNB : ⌈Bc ^ 2⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN1, hM1, hτ1⟩ := moment_dims hτ hX
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN1
  have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN1
  have hDA := hX.densityAssumptions hτ
  have hσ := hX.pos
  have hti1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hKdet : 0 ≤ detZConst τ := by
    unfold detZConst
    exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num)
      (Real.sqrt_nonneg _)) hti0)) (add_nonneg hti0 (pow_nonneg hti0 _))
  -- (G*)
  have hGs : xG ≤ (N : ℝ) ^ (c₀ / 2) := by
    calc xG = (xG ^ (2 / c₀)) ^ (c₀ / 2) := by
          rw [← Real.rpow_mul hx0, show 2 / c₀ * (c₀ / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (c₀ / 2) :=
          Real.rpow_le_rpow (by positivity) ((Nat.le_ceil _).trans (by exact_mod_cast hNG))
            (by positivity)
  -- the threshold of the part off the good event
  have hBcN : Bc ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc Bc ≤ |Bc| := le_abs_self _
      _ = √(Bc ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √N := Real.sqrt_le_sqrt ((Nat.le_ceil _).trans (by exact_mod_cast hNB))
  have hΥ0 : 0 ≤ Υ := le_trans (by positivity) hΥN
  have hGP := hN₁ N hNN₁ M σ X hX z Υ hΛ hΛo
  set δ := (N : ℝ) ^ (ε₁ + εL) * Υ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    calc δ ≤ (N : ℝ) ^ (ε₁ + εL) * (N : ℝ) ^ (-c₀) :=
          mul_le_mul_of_nonneg_left hΥc₀ (by positivity)
      _ = (N : ℝ) ^ (ε₁ + εL - c₀) := by rw [← Real.rpow_add hN0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  set K := mobConst p τ c + ldeZConst p τ c with hKdef
  have hK : 0 ≤ K := add_nonneg hKZ hKL
  set R : ℝ := (N : ℝ) ^ (6 * (p : ℝ) + 1 / 2) with hRdef
  have hR : 0 < R := by positivity
  have hεb : 0 ≤ (N : ℝ) ^ (-(D₁ - 1)) := by positivity
  have hXm : Measurable (fun ω => (X ω : Fin M → Fin N → ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun ν => hX.entries.measurable i ν
  have hP1 : 1 ≤ (N : ℝ) ^ (ε₁ + εL) := Real.one_le_rpow hN1' (by linarith)
  have hPe : ((N : ℝ) ^ (ε₁ + εL)) ^ (2 * (2 * p)) = (N : ℝ) ^ (4 * (p : ℝ) * (ε₁ + εL)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hfin : ∀ {E : ℝ},
      E ≤ (((2 * p : ℕ) : ℝ) ^ (2 * p) * 2 ^ (2 * p * (2 * p - 1)) * τ⁻¹ ^ p * (A * K) ^ (2 * p)
        + 1) * ((N : ℝ) ^ (ε₁ + εL)) ^ (2 * (2 * p)) * Υ ^ (2 * (2 * p)) →
      E ≤ faMomConst p τ c A * (N : ℝ) ^ (4 * (p : ℝ) * (ε₁ + εL)) * Υ ^ (4 * p) := by
    intro E hE
    refine hE.trans (le_of_eq ?_)
    rw [hPe, show 2 * (2 * p) = 4 * p by ring]
    unfold faMomConst
    push_cast
    ring
  have hCabs : |C (2 * (2 * (2 * p)))| ≤ Cm :=
    le_mul_of_one_le_left (abs_nonneg _) (by linarith [pow_nonneg hti0 (2 * (2 * p))])
  have hCmle : ∀ x : ℝ, x ≤ C (2 * (2 * (2 * p))) → x ≤ Cm := fun x hx =>
    hx.trans ((le_abs_self _).trans hCabs)
  have hCmle' : τ⁻¹ ^ (2 * (2 * p)) * C (2 * (2 * (2 * p))) ≤ Cm := by
    rw [hCm]
    have h1 : τ⁻¹ ^ (2 * (2 * p)) * C (2 * (2 * (2 * p)))
        ≤ τ⁻¹ ^ (2 * (2 * p)) * |C (2 * (2 * (2 * p)))| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hti0 _)
    nlinarith [abs_nonneg (C (2 * (2 * (2 * p))))]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- column labels
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (ha ⟨0, hN1⟩)
    have H : MomHyp (fun ω => (X ω : Fin M → Fin N → ℝ)) (fun _ ν => ν)
        (fun S μ Xm => ZmuS σ Xm z S μ) (fun μ Xm => ∑ i, Xm i μ ^ 2) (detZConst τ * N)
        (2 * p) Cm :=
      { meas := hXm
        measZ := fun S μ => moment_measurable_ZmuS σ z S μ
        congr := fun T U μ hμ Xm Xm' h => ZmuMob_congr σ z T U μ hμ h
        van := fun S μ F hFm hF hint => integral_ZmuS_mul_eq_zero hX hz.1 S μ F hFm hF hint
        measy := fun μ => Finset.measurable_sum _ fun i _ =>
          ((measurable_pi_apply μ).comp (measurable_pi_apply i)).pow_const 2
        y0 := fun μ Xm => Finset.sum_nonneg fun i _ => sq_nonneg _
        Kd0 := mul_nonneg hKdet hN0.le
        det := fun S μ Xm => ZmuS_det_bound hDA hσ Xm hz S μ
        Cm0 := hCm0
        mom := fun μ => ⟨((sq_norm_moment hτ hX (2 * (2 * p))).1 μ).1,
          ((sq_norm_moment hτ hX (2 * (2 * p))).1 μ).2.trans hCmle'⟩ }
    have hgood : ∀ ω ∈ {ω | FaGood σ (X ω) z p c₀ ε₁ εL Υ}, ∀ (T U : Finset (Fin N)) (s : Fin N),
        s ∉ T → T.card + 1 ≤ 2 * p → U ⊆ T →
        ‖mobPart (fun S => ZmuS σ (X ω) z S s) T U‖ ≤ K * δ ^ (U.card + 1) :=
      fun ω hω T U s hs hT hU => moment_good_col hc hDA hσ hz hx hN1 hε₁ hε₁c₀ hεL.le hΥN hΥc₀
        hGs (X ω) hω T U s hs hT hU
    have hι : 0 < Fintype.card (Fin N) := by rw [Fintype.card_fin]; omega
    obtain ⟨hi, hE⟩ := H.moment hι hεb hGP hK hδ0 hδ1 hgood hR a ha
    have e : ∀ ω, ZavgN σ (X ω) z a =
        ((Fintype.card (Fin N) : ℕ) : ℂ)⁻¹ * ∑ μ, a μ * ZmuS σ (X ω) z ∅ μ := by
      intro ω
      simp [ZavgN, ZmuS_empty]
    simp only [e]
    refine ⟨hi, ?_⟩
    have hS := moment_good_sum (n := 2 * p) hι hP1 hΥ0 le_rfl
      (by rw [Fintype.card_fin, one_mul]; exact hΥN)
    have hβ := moment_bad (A := A) hN1 hD₁ hΥN hBcN
    refine hfin ?_
    exact moment_combine hA0 hK (by positivity) (one_le_pow₀ hP1) (by positivity)
      (by positivity) (by rw [one_pow]; exact one_le_pow₀ hti1) hE hS hβ
  · -- row labels
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (ha ⟨0, hM1⟩)
    have H : MomHyp (fun ω => (X ω : Fin M → Fin N → ℝ)) (fun i _ => i)
        (fun S i Xm => ZiS σ Xm z S i) (fun i Xm => ∑ ν, Xm i ν ^ 2) (detZConst τ * N)
        (2 * p) Cm :=
      { meas := hXm
        measZ := fun S i => moment_measurable_ZiS σ z S i
        congr := fun T U i hi Xm Xm' h => ZiMob_congr σ z T U i hi h
        van := fun S i F hFm hF hint => integral_ZiS_mul_eq_zero hX hz.1 S i F hFm hF hint
        measy := fun i => Finset.measurable_sum _ fun ν _ =>
          ((measurable_pi_apply ν).comp (measurable_pi_apply i)).pow_const 2
        y0 := fun i Xm => Finset.sum_nonneg fun ν _ => sq_nonneg _
        Kd0 := mul_nonneg hKdet hN0.le
        det := fun S i Xm => ZiS_det_bound hDA hσ Xm hz S i
        Cm0 := hCm0
        mom := fun i => ⟨((sq_norm_moment hτ hX (2 * (2 * p))).2 i).1,
          hCmle _ ((sq_norm_moment hτ hX (2 * (2 * p))).2 i).2⟩ }
    have hgood : ∀ ω ∈ {ω | FaGood σ (X ω) z p c₀ ε₁ εL Υ}, ∀ (T U : Finset (Fin M)) (s : Fin M),
        s ∉ T → T.card + 1 ≤ 2 * p → U ⊆ T →
        ‖mobPart (fun S => ZiS σ (X ω) z S s) T U‖ ≤ K * δ ^ (U.card + 1) :=
      fun ω hω T U s hs hT hU => moment_good_row hc hDA hσ hz hx hN1 hε₁ hε₁c₀ hεL.le hΥN hΥc₀
        hGs (X ω) hω T U s hs hT hU
    have hι : 0 < Fintype.card (Fin M) := by rw [Fintype.card_fin]; omega
    obtain ⟨hi, hE⟩ := H.moment hι hεb hGP hK hδ0 hδ1 hgood hR a ha
    have e : ∀ ω, ZavgM σ (X ω) z a =
        ((Fintype.card (Fin M) : ℕ) : ℂ)⁻¹ * ∑ i, a i * ZiS σ (X ω) z ∅ i := by
      intro ω
      simp [ZavgM, ZiS_empty]
    simp only [e]
    refine ⟨hi, ?_⟩
    -- `M^{-1/2} ≤ τ^{-1/2} N^{-1/2} ≤ √τ⁻¹ Υ`
    have hκ1 : 1 ≤ √τ⁻¹ := Real.one_le_sqrt.2 hti1
    have hκM : (Fintype.card (Fin M) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ √τ⁻¹ * Υ := by
      rw [Fintype.card_fin]
      have hτN : τ * N ≤ M := by
        have := hX.ratio_ge
        rwa [le_div_iff₀ hN0] at this
      calc (M : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (τ * N) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hτN (by norm_num)
        _ = √τ⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [Real.mul_rpow hτ.le hN0.le, Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow,
              Real.sqrt_inv]
        _ ≤ √τ⁻¹ * Υ := mul_le_mul_of_nonneg_left hΥN (Real.sqrt_nonneg _)
    have hκp : (√τ⁻¹) ^ (2 * p) = τ⁻¹ ^ p := by rw [pow_mul, Real.sq_sqrt hti0]
    have hS := moment_good_sum (n := 2 * p) hι hP1 hΥ0 hκ1 hκM
    have hβ := moment_bad (A := A) hN1 hD₁ hΥN hBcN
    refine hfin ?_
    exact moment_combine hA0 hK (by positivity) (one_le_pow₀ hP1) (by positivity)
      (by positivity) hκp.le hE hS hβ

/-! ## Checks -/

section Checks

example : loneCount (![0, 0, 1] : Fin 3 → Fin 2) = 1 := by decide

example : 2 * (Finset.univ.image (![0, 0, 1] : Fin 3 → Fin 2)).card ≤
    3 + loneCount (![0, 0, 1] : Fin 3 → Fin 2) := by decide

/-- `two_mul_card_image_le` at the tuple `(0, 0, 1)`: the equality case `4 ≤ 4`. -/
example : 2 * (Finset.univ.image (![0, 0, 1] : Fin 3 → Fin 2)).card ≤
    3 + loneCount (![0, 0, 1] : Fin 3 → Fin 2) :=
  two_mul_card_image_le _

/-- `loneCount` of the tuple `(0, 1)` is `2` and of `(0, 0)` is `0`. -/
example : loneCount (![0, 1] : Fin 2 → Fin 2) = 2 ∧ loneCount (![0, 0] : Fin 2 → Fin 2) = 0 := by
  decide

/-- `sum_tuples_le` at `n = 2`, `ι = Fin 2`, with the trivial weight `Υ = κ = 1`. -/
example : ∑ v : Fin 2 → Fin 2, ((Fintype.card (Fin 2) : ℝ)⁻¹) ^ 2 * (1 : ℝ) ^ (2 + loneCount v) ≤
    ((2 : ℕ) : ℝ) ^ 2 * (1 : ℝ) ^ 2 * (1 : ℝ) ^ (2 * 2) :=
  sum_tuples_le (by simp) zero_le_one le_rfl (by
    rw [one_mul, Fintype.card_fin]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))

/-- `sum_tuples_le` at `n = 2`, `ι = Fin 2`, `κ = 1`, `Υ = 2^{-1/2}`, where the hypothesis
`|ι|^{-1/2} ≤ κΥ` holds with equality. -/
example : ∑ v : Fin 2 → Fin 2, ((Fintype.card (Fin 2) : ℝ)⁻¹) ^ 2 *
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 + loneCount v) ≤
    ((2 : ℕ) : ℝ) ^ 2 * (1 : ℝ) ^ 2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 * 2) :=
  sum_tuples_le (by simp) (by positivity) le_rfl (by
    rw [one_mul, Fintype.card_fin]
    norm_num)

/-- `fa_moment` at `τ = 1/2`, `c = 1`, `c₀ = 1/4`, `C ≡ 1`, `p = 1`, `ε₁ = ε_L = 1/64`,
`D₁ = 10`, `A = 1`. This is a conditional check: the models, `z`, `Υ`, the domination
hypotheses and the weights are binders, since the Rademacher model (`M = N = 2`, `σ ≡ 1`,
`z = 2i`) lies below the threshold `N₀`, which includes (G*) `4^{p+2} τ⁻² c_as⁻¹ ≤ N^{c₀/2}`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 1) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, 1 ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) →
    DomAt N (1 / 64) 10 (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 4 : ℝ))) →
    DomAt N (1 / 64) 10 (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
    (∀ a : Fin N → ℂ, (∀ μ, ‖a μ‖ ≤ 1) →
      Integrable (fun ω => ‖ZavgN σ (X ω) z a‖ ^ (2 * 1)) ∧
      ∫ ω, ‖ZavgN σ (X ω) z a‖ ^ (2 * 1) ≤
        faMomConst 1 (1 / 2) 1 1 * (N : ℝ) ^ (4 * ((1 : ℕ) : ℝ) * (1 / 64 + 1 / 64)) *
          Υ ^ (4 * 1)) ∧
    (∀ a : Fin M → ℂ, (∀ i, ‖a i‖ ≤ 1) →
      Integrable (fun ω => ‖ZavgM σ (X ω) z a‖ ^ (2 * 1)) ∧
      ∫ ω, ‖ZavgM σ (X ω) z a‖ ^ (2 * 1) ≤
        faMomConst 1 (1 / 2) 1 1 * (N : ℝ) ^ (4 * ((1 : ℕ) : ℝ) * (1 / 64 + 1 / 64)) *
          Υ ^ (4 * 1)) :=
  fa_moment (1 / 2) 1 (1 / 4) (fun _ => 1) 1 (1 / 64) (1 / 64) 10 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Checks

end Anisotropic

#print axioms Anisotropic.loneCount
#print axioms Anisotropic.two_mul_card_image_le
#print axioms Anisotropic.sum_tuples_le
#print axioms Anisotropic.ZavgN
#print axioms Anisotropic.ZavgM
#print axioms Anisotropic.ZavgN_one
#print axioms Anisotropic.faMomConst
#print axioms Anisotropic.fa_moment
