module

public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.EdgeUniv.Eigen
public import Anisotropic.Framework.Domination

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The model-agnostic reduction: edge regime and comparison of smooth functionals give the comparison of `E h(q)` -/

/-- The comparison hypothesis: for `F ∈ C⁵` with derivatives of order `≤ 5` bounded by `C_b`
and windows `[E_j, E_L]` with `|E_j - a| ≤ N^{-2/3+ε}`, the expectations of
`F((𝒳_{[E_j, E_L]})_j)` for `A₁` and `A₀` differ by at most `C_b N^{-c₁}`. -/
def SmoothComparable (N : ℕ) (a ε c₁ : ℝ) (l : ℕ) {Ω₁ Ω₀ : Type} [MeasureSpace Ω₁]
    [MeasureSpace Ω₀] {n : ℕ} (A₁ : Ω₁ → Matrix (Fin n) (Fin n) ℝ)
    (A₀ : Ω₀ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (F : (Fin l → ℝ) → ℝ) (Cb : ℝ), ContDiff ℝ 5 F →
    (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
    ∀ E : Fin l → ℝ, (∀ j, |E j - a| ≤ (N : ℝ) ^ (-2 / 3 + ε)) →
      |(∫ ω, F (fun j => smCount (A₁ ω) (etaE N ε) (E j) (edgeEL N a ε))) -
          (∫ ω, F (fun j => smCount (A₀ ω) (etaE N ε) (E j) (edgeEL N a ε)))| ≤
        Cb * (N : ℝ) ^ (-c₁)

/-! ### Approximation of `h` by a combination of orthant indicators on a grid

The passage from the comparison of smoothed counts to the comparison of `E h(q)` in the proof of
Theorem 3.18 (§10.2): on a grid of step `δ`, a block average `Ψ` of `h` is a finite combination
`∑_m c(m) 1(q ≥ δ m)` with `|c(m)| ≤ B (2/K)^l`. -/

/-- The orthant indicator `1(x ≥ s)` (coordinatewise). -/
private def redInd {l : ℕ} (s x : Fin l → ℝ) : ℝ := ∏ i, if s i ≤ x i then 1 else 0

/-- The integer box `[-R, R)^l`. -/
private def redBox (l R : ℕ) : Finset (Fin l → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ico (-(R : ℤ)) R

/-- The one-dimensional averaging weight `K⁻¹ 1(δ(p+1-K) ≤ y < δ(p+1))`. -/
private def redW (δ : ℝ) (K : ℕ) (p : ℤ) (y : ℝ) : ℝ :=
  ((if δ * ((p : ℝ) + 1 - K) ≤ y then 1 else 0) - (if δ * ((p : ℝ) + 1) ≤ y then 1 else 0)) / K

/-- The one-dimensional difference kernel `K⁻¹ (1(t = p+1-K) - 1(t = p+1))`. -/
private def redKer (K : ℕ) (t p : ℤ) : ℝ :=
  ((if t = p + 1 - K then 1 else 0) - (if t = p + 1 then 1 else 0)) / K

/-- The coefficients `c(m) = ∑_p h(δ p) ∏_j w(m_j, p_j)`. -/
private def redCoef {l : ℕ} (h : (Fin l → ℝ) → ℝ) (δ : ℝ) (K R : ℕ) (m : Fin l → ℤ) : ℝ :=
  ∑ p ∈ redBox l R, h (fun j => δ * p j) * ∏ j, redKer K (m j) (p j)

/-- The block average `Ψ(x) = ∑_p h(δ p) ∏_j W(p_j, x_j)`. -/
private def redPsi {l : ℕ} (h : (Fin l → ℝ) → ℝ) (δ : ℝ) (K R : ℕ) (x : Fin l → ℝ) : ℝ :=
  ∑ p ∈ redBox l R, h (fun j => δ * p j) * ∏ j, redW δ K (p j) (x j)

private lemma redInd_nonneg {l : ℕ} (s x : Fin l → ℝ) : 0 ≤ redInd s x :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num

private lemma redInd_le_one {l : ℕ} (s x : Fin l → ℝ) : redInd s x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by split_ifs <;> norm_num

private lemma redW_eq {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (p : ℤ) (y : ℝ) :
    redW δ K p y = (if ⌊y / δ⌋ ≤ p ∧ p ≤ ⌊y / δ⌋ + K - 1 then 1 else 0) / K := by
  unfold redW
  congr 1
  have e1 : δ * ((p : ℝ) + 1 - K) ≤ y ↔ p + 1 - K ≤ ⌊y / δ⌋ := by
    rw [Int.le_floor, le_div_iff₀ hδ]; push_cast; constructor <;> intro h <;> linarith
  have e2 : δ * ((p : ℝ) + 1) ≤ y ↔ p + 1 ≤ ⌊y / δ⌋ := by
    rw [Int.le_floor, le_div_iff₀ hδ]; push_cast; constructor <;> intro h <;> linarith
  simp only [e1, e2]
  split_ifs <;> norm_num <;> omega

private lemma redW_nonneg {δ : ℝ} (hδ : 0 < δ) (K : ℕ) (p : ℤ) (y : ℝ) : 0 ≤ redW δ K p y := by
  rw [redW_eq hδ]; apply div_nonneg <;> [split_ifs <;> norm_num; positivity]

private lemma sum_redW_le {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (I : Finset ℤ) (y : ℝ) :
    ∑ t ∈ I, redW δ K t y ≤ 1 := by
  simp_rw [redW_eq hδ]
  rw [← Finset.sum_div, Finset.sum_boole, div_le_one (by exact_mod_cast hK)]
  have hsub : I.filter (fun t => ⌊y / δ⌋ ≤ t ∧ t ≤ ⌊y / δ⌋ + K - 1) ⊆
      Finset.Icc ⌊y / δ⌋ (⌊y / δ⌋ + K - 1) := by
    intro t ht; simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢; exact ht.2
  have := Finset.card_le_card hsub
  rw [Int.card_Icc] at this
  have hK' : ((⌊y / δ⌋ + K - 1 + 1 - ⌊y / δ⌋).toNat) = K := by omega
  rw [hK'] at this
  exact_mod_cast this

private lemma sum_redW_eq {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ) {y : ℝ}
    (hy : |y| ≤ δ * ((R : ℝ) - K - 1)) :
    ∑ t ∈ Finset.Ico (-(R : ℤ)) R, redW δ K t y = 1 := by
  simp_rw [redW_eq hδ]
  rw [← Finset.sum_div, Finset.sum_boole, div_eq_one_iff_eq (by positivity)]
  have hz : |y / δ| ≤ (R : ℝ) - K - 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]; linarith
  have hf1 := Int.floor_le (y / δ)
  have hf2 := Int.lt_floor_add_one (y / δ)
  rw [abs_le] at hz
  have h1 : -(R : ℤ) + K ≤ ⌊y / δ⌋ := by
    have : ((-(R : ℤ) + K : ℤ) : ℝ) < ⌊y / δ⌋ + 1 := by push_cast; linarith
    exact_mod_cast (show ((-(R : ℤ) + K : ℤ) : ℝ) ≤ ⌊y / δ⌋ by
      have : (-(R : ℤ) + K : ℤ) < ⌊y / δ⌋ + 1 := by exact_mod_cast this
      exact_mod_cast (by omega : (-(R : ℤ) + K : ℤ) ≤ ⌊y / δ⌋))
  have h2 : ⌊y / δ⌋ + K + 1 ≤ (R : ℤ) := by
    have : ((⌊y / δ⌋ + K + 1 : ℤ) : ℝ) ≤ R := by push_cast; linarith
    exact_mod_cast this
  have heq : (Finset.Ico (-(R : ℤ)) R).filter (fun t => ⌊y / δ⌋ ≤ t ∧ t ≤ ⌊y / δ⌋ + K - 1) =
      Finset.Icc ⌊y / δ⌋ (⌊y / δ⌋ + K - 1) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [heq, Int.card_Icc]
  have hK' : ((⌊y / δ⌋ + K - 1 + 1 - ⌊y / δ⌋).toNat) = K := by omega
  rw [hK']

private lemma red_sum_prod {l : ℕ} (I : Finset ℤ) (f : Fin l → ℤ → ℝ) :
    ∑ p ∈ Fintype.piFinset (fun _ => I), ∏ j, f j (p j) = ∏ j, ∑ t ∈ I, f j t :=
  (Finset.prod_univ_sum _ _).symm

private lemma sum_redKer_mul {K : ℕ} (hK : 1 ≤ K) {R : ℕ} {p : ℤ}
    (hp : p ∈ Finset.Ico (-(R : ℤ)) R) (g : ℤ → ℝ) :
    ∑ t ∈ Finset.Ico (-((R + K : ℕ) : ℤ)) ((R + K : ℕ) : ℤ), redKer K t p * g t =
      (g (p + 1 - K) - g (p + 1)) / K := by
  rw [Finset.mem_Ico] at hp
  unfold redKer
  simp_rw [div_mul_eq_mul_div, sub_mul, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  rw [ite_eq_left (by rw [Finset.mem_Ico]; push_cast; omega),
    ite_eq_left (by rw [Finset.mem_Ico]; push_cast; omega)]

/-- Summation by parts on the grid: `Ψ(x) = ∑_m c(m) 1(x ≥ δ m)`. -/
private lemma redPsi_eq {l : ℕ} (h : (Fin l → ℝ) → ℝ) (δ : ℝ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ)
    (x : Fin l → ℝ) :
    redPsi h δ K R x =
      ∑ m ∈ redBox l (R + K), redCoef h δ K R m * redInd (fun i => δ * m i) x := by
  unfold redCoef
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold redPsi
  refine Finset.sum_congr rfl fun p hp => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  unfold redInd
  simp_rw [← Finset.prod_mul_distrib]
  rw [redBox, red_sum_prod _ (fun j t => redKer K t (p j) *
    if δ * (t : ℝ) ≤ x j then 1 else 0)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hpj : p j ∈ Finset.Ico (-(R : ℤ)) R := Fintype.mem_piFinset.1 hp j
  rw [sum_redKer_mul hK hpj (fun t => if δ * (t : ℝ) ≤ x j then 1 else 0)]
  unfold redW
  push_cast
  rfl

private lemma sum_abs_redKer_le {K : ℕ} (hK : 1 ≤ K) (I : Finset ℤ) (m : ℤ) :
    ∑ t ∈ I, |redKer K m t| ≤ 2 / K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hb : ∀ t, |redKer K m t| ≤
      ((if t = m + K - 1 then 1 else 0) + (if t = m - 1 then 1 else 0)) / K := by
    intro t
    unfold redKer
    rw [abs_div, abs_of_pos hK0]
    refine div_le_div_of_nonneg_right ?_ hK0.le
    have e1 : (m = t + 1 - K) ↔ (t = m + K - 1) := by omega
    have e2 : (m = t + 1) ↔ (t = m - 1) := by omega
    simp only [e1, e2]
    split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun t _ => hb t).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  refine div_le_div_of_nonneg_right ?_ hK0.le
  split_ifs <;> norm_num

/-- `|c(m)| ≤ B (2/K)^l`. -/
private lemma abs_redCoef_le {l : ℕ} {h : (Fin l → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (δ : ℝ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ) (m : Fin l → ℤ) :
    |redCoef h δ K R m| ≤ B * (2 / K) ^ l := by
  unfold redCoef
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ p ∈ redBox l R, |h (fun j => δ * p j) * ∏ j, redKer K (m j) (p j)| ≤
      B * ∏ j, |redKer K (m j) (p j)| := by
    intro p _
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_right (hB _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  refine (Finset.sum_le_sum this).trans ?_
  rw [← Finset.mul_sum, redBox, red_sum_prod _ (fun j t => |redKer K (m j) t|)]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine mul_le_mul_of_nonneg_left ?_ hB0
  calc ∏ j, ∑ t ∈ Finset.Ico (-(R : ℤ)) R, |redKer K (m j) t| ≤ ∏ _j : Fin l, (2 / (K : ℝ)) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          fun j _ => sum_abs_redKer_le hK _ _
    _ = (2 / K) ^ l := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `|Ψ(x)| ≤ B`. -/
private lemma abs_redPsi_le {l : ℕ} {h : (Fin l → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ) (x : Fin l → ℝ) :
    |redPsi h δ K R x| ≤ B := by
  unfold redPsi
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ p ∈ redBox l R, |h (fun j => δ * p j) * ∏ j, redW δ K (p j) (x j)| ≤
      B * ∏ j, redW δ K (p j) (x j) := by
    intro p _
    rw [abs_mul, Finset.abs_prod]
    simp_rw [abs_of_nonneg (redW_nonneg hδ K _ _)]
    exact mul_le_mul_of_nonneg_right (hB _) (Finset.prod_nonneg fun _ _ => redW_nonneg hδ K _ _)
  refine (Finset.sum_le_sum this).trans ?_
  rw [← Finset.mul_sum, redBox, red_sum_prod _ (fun j t => redW δ K t (x j))]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine mul_le_of_le_one_right hB0 ?_
  exact Finset.prod_le_one₀ (fun j _ => Finset.sum_nonneg fun _ _ => redW_nonneg hδ K _ _)
    fun j _ => sum_redW_le hδ hK _ _

private lemma redW_ne_zero {δ : ℝ} (hδ : 0 < δ) {K : ℕ} {p : ℤ} {y : ℝ} (h : redW δ K p y ≠ 0) :
    |δ * p - y| ≤ δ * K := by
  rw [redW_eq hδ] at h
  have hc : ⌊y / δ⌋ ≤ p ∧ p ≤ ⌊y / δ⌋ + K - 1 := by
    by_contra hc; rw [ite_eq_right hc] at h; simp at h
  have hf1 := Int.floor_le (y / δ)
  have hf2 := Int.lt_floor_add_one (y / δ)
  have a1 : ((⌊y / δ⌋ : ℤ) : ℝ) ≤ p := by exact_mod_cast hc.1
  have a2 : (p : ℝ) ≤ ⌊y / δ⌋ + K - 1 := by exact_mod_cast hc.2
  have hyd : y = δ * (y / δ) := by field_simp
  rw [abs_le]
  constructor <;> nlinarith

/-- Inside the box, `|h(x) - Ψ(x)| ≤ L δ K`. -/
private lemma abs_sub_redPsi_le {l : ℕ} {h : (Fin l → ℝ) → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h)
    {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ) {x : Fin l → ℝ}
    (hx : ∀ j, |x j| ≤ δ * ((R : ℝ) - K - 1)) :
    |h x - redPsi h δ K R x| ≤ L * (δ * K) := by
  have h1 : ∑ p ∈ redBox l R, ∏ j, redW δ K (p j) (x j) = 1 := by
    rw [redBox, red_sum_prod _ (fun j t => redW δ K t (x j))]
    exact Finset.prod_eq_one fun j _ => sum_redW_eq hδ hK R (hx j)
  have hrw : h x - redPsi h δ K R x =
      ∑ p ∈ redBox l R, (h x - h (fun j => δ * p j)) * ∏ j, redW δ K (p j) (x j) := by
    unfold redPsi
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, mul_one]
  rw [hrw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ p ∈ redBox l R, |(h x - h (fun j => δ * p j)) * ∏ j, redW δ K (p j) (x j)| ≤
      L * (δ * K) * ∏ j, redW δ K (p j) (x j) := by
    intro p _
    have hW : 0 ≤ ∏ j, redW δ K (p j) (x j) := Finset.prod_nonneg fun _ _ => redW_nonneg hδ K _ _
    rw [abs_mul, abs_of_nonneg hW]
    by_cases h0 : ∏ j, redW δ K (p j) (x j) = 0
    · rw [h0]; simp
    · refine mul_le_mul_of_nonneg_right ?_ hW
      have hall : ∀ j, redW δ K (p j) (x j) ≠ 0 := fun j hj =>
        h0 (Finset.prod_eq_zero (Finset.mem_univ j) hj)
      have hd : dist x (fun j => δ * p j) ≤ δ * K := by
        refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
        rw [Real.dist_eq, abs_sub_comm]
        exact redW_ne_zero hδ (hall j)
      rw [← Real.dist_eq]
      exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.2)
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum, h1, mul_one]

private lemma red_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (h0 : ∀ i, 0 ≤ b i)
    (hba : ∀ i, b i ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    ∏ i ∈ s, a i - ∏ i ∈ s, b i ≤ ∑ i ∈ s, (a i - b i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    have hQ0 : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i _ => h0 i
    have hQP : ∏ i ∈ s, b i ≤ ∏ i ∈ s, a i :=
      Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => hba i
    have hQ1 : ∏ i ∈ s, b i ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => h0 i) fun i _ => (hba i).trans (ha1 i)
    have hak := ha1 k
    have hbk := hba k
    have hb0 := h0 k
    nlinarith

private lemma red_sum_coord {l : ℕ} (I : Finset ℤ) (i : Fin l) (g : ℤ → ℝ) :
    ∑ m ∈ Fintype.piFinset (fun _ => I), g (m i) = (I.card : ℝ) ^ (l - 1) * ∑ t ∈ I, g t := by
  have h1 : ∀ m : Fin l → ℤ, g (m i) = ∏ j, (if j = i then g (m j) else 1) := by
    intro m; rw [Finset.prod_ite_eq']; simp
  simp_rw [h1]
  rw [red_sum_prod I (fun j t => if j = i then g t else 1)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [ite_true]
  have h2 : ∀ j ∈ Finset.univ \ {i}, (∑ t ∈ I, if j = i then g t else 1) = (I.card : ℝ) := by
    intro j hj
    have : j ≠ i := by simpa using hj
    simp [this]
  rw [Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_sdiff_of_subset (by simp),
    Finset.card_univ, Fintype.card_fin, Finset.card_singleton, mul_comm]

private lemma red_shell_one {δ : ℝ} (hδ : 0 < δ) (R : ℕ) (y : ℝ) :
    ∑ t ∈ Finset.Ico (-(R : ℤ)) R,
      ((if δ * t - δ ≤ y then (1 : ℝ) else 0) - (if δ * t + δ ≤ y then 1 else 0)) ≤ 2 := by
  have e : ∀ t : ℤ, ((if δ * t - δ ≤ y then (1 : ℝ) else 0) - (if δ * t + δ ≤ y then 1 else 0)) =
      if (δ * t - δ ≤ y ∧ ¬ δ * t + δ ≤ y) then 1 else 0 := by
    intro t
    by_cases h1 : δ * t - δ ≤ y <;> by_cases h2 : δ * t + δ ≤ y <;> simp [h1, h2]
    linarith
  simp_rw [e]
  rw [Finset.sum_boole]
  have hsub : (Finset.Ico (-(R : ℤ)) R).filter (fun t : ℤ => δ * t - δ ≤ y ∧ ¬ δ * t + δ ≤ y) ⊆
      Finset.Icc ⌊y / δ⌋ (⌊y / δ⌋ + 1) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    obtain ⟨_, h1, h2⟩ := ht
    have a1 : ((t - 1 : ℤ) : ℝ) ≤ y / δ := by
      rw [le_div_iff₀ hδ]; push_cast; linarith
    have a2 : y / δ < ((t + 1 : ℤ) : ℝ) := by
      rw [div_lt_iff₀ hδ]; push_cast; linarith
    have b1 := Int.le_floor.2 a1
    have b2 := Int.floor_lt.2 a2
    omega
  have := Finset.card_le_card hsub
  rw [Int.card_Icc] at this
  have h2 : (⌊y / δ⌋ + 1 + 1 - ⌊y / δ⌋).toNat = 2 := by omega
  rw [h2] at this
  exact_mod_cast this

/-- The shell sum: `∑_m (1(x ≥ δ m - δ) - 1(x ≥ δ m + δ)) ≤ 2 l (2R)^{l-1}`. -/
private lemma red_shell {l : ℕ} {δ : ℝ} (hδ : 0 < δ) (R : ℕ) (x : Fin l → ℝ) :
    ∑ m ∈ redBox l R, (redInd (fun i => δ * m i - δ) x - redInd (fun i => δ * m i + δ) x) ≤
      2 * l * (2 * R : ℝ) ^ (l - 1) := by
  set a : ℤ → Fin l → ℝ := fun t i => if δ * t - δ ≤ x i then 1 else 0 with ha
  set b : ℤ → Fin l → ℝ := fun t i => if δ * t + δ ≤ x i then 1 else 0 with hb
  have hpt : ∀ m : Fin l → ℤ, redInd (fun i => δ * m i - δ) x - redInd (fun i => δ * m i + δ) x ≤
      ∑ i, (a (m i) i - b (m i) i) := by
    intro m
    refine red_prod_sub_prod_le Finset.univ (fun i => a (m i) i) (fun i => b (m i) i) ?_ ?_ ?_
    · intro i; simp only [hb]; split_ifs <;> norm_num
    · intro i; simp only [ha, hb]
      by_cases h2 : δ * (m i) + δ ≤ x i
      · rw [ite_eq_left h2, ite_eq_left (by linarith)]
      · rw [ite_eq_right h2]; split_ifs <;> norm_num
    · intro i; simp only [ha]; split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun m _ => hpt m).trans ?_
  rw [Finset.sum_comm]
  have hcard : ((Finset.Ico (-(R : ℤ)) R).card : ℝ) = 2 * R := by
    rw [Int.card_Ico]
    have : ((R : ℤ) - -(R : ℤ)).toNat = 2 * R := by omega
    rw [this]; push_cast; ring
  have hi : ∀ i : Fin l, ∑ m ∈ redBox l R, (a (m i) i - b (m i) i) ≤ (2 * R : ℝ) ^ (l - 1) * 2 := by
    intro i
    rw [redBox, red_sum_coord _ i (fun t => a t i - b t i), hcard]
    exact mul_le_mul_of_nonneg_left (red_shell_one hδ R (x i)) (by positivity)
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

private lemma measurable_redInd {l : ℕ} (s : Fin l → ℝ) : Measurable (redInd s) := by
  unfold redInd
  exact Finset.measurable_prod _ fun i _ =>
    Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i)) measurable_const
      measurable_const

private lemma measurable_redPsi {l : ℕ} (h : (Fin l → ℝ) → ℝ) (δ : ℝ) {K : ℕ} (hK : 1 ≤ K)
    (R : ℕ) : Measurable (redPsi h δ K R) := by
  have : redPsi h δ K R = fun x =>
      ∑ m ∈ redBox l (R + K), redCoef h δ K R m * redInd (fun i => δ * m i) x := by
    funext x; exact redPsi_eq h δ hK R x
  rw [this]
  exact Finset.measurable_sum _ fun m _ => measurable_const.mul (measurable_redInd _)

section RedProb

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

private lemma red_integrable {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable f :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- One ensemble: `|E h(Q) - E Ψ(Q)| ≤ L δ K + 2 B P(T)` if `Q` lies in the inner box off `T`. -/
private lemma red_approx {l : ℕ} {h : (Fin l → ℝ) → ℝ} {B : ℝ} {L : ℝ≥0} (hB : ∀ x, |h x| ≤ B)
    (hL : LipschitzWith L h) {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ)
    {Q : Ω → Fin l → ℝ} (hQ : Measurable Q) {T : Set Ω} (hT : MeasurableSet T)
    (hin : ∀ ω ∉ T, ∀ j, |Q ω j| ≤ δ * ((R : ℝ) - K - 1)) :
    |(∫ ω, h (Q ω)) - ∫ ω, redPsi h δ K R (Q ω)| ≤
      L * (δ * K) + 2 * B * (ℙ T).toReal := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmh : Measurable fun ω => h (Q ω) := hL.continuous.measurable.comp hQ
  have hmP : Measurable fun ω => redPsi h δ K R (Q ω) := (measurable_redPsi h δ hK R).comp hQ
  have i1 : Integrable fun ω => h (Q ω) := red_integrable hmh fun ω => hB _
  have i2 : Integrable fun ω => redPsi h δ K R (Q ω) :=
    red_integrable hmP fun ω => abs_redPsi_le hB hδ hK R _
  rw [← integral_sub i1 i2]
  have hInd : Integrable (T.indicator (1 : Ω → ℝ)) := (integrable_const (1 : ℝ)).indicator hT
  have hg : Integrable fun ω => L * (δ * K) + 2 * B * T.indicator 1 ω :=
    (integrable_const _).add (hInd.const_mul _)
  have hpt : ∀ ω, ‖h (Q ω) - redPsi h δ K R (Q ω)‖ ≤ L * (δ * K) + 2 * B * T.indicator 1 ω := by
    intro ω
    rw [Real.norm_eq_abs]
    have hLδ : 0 ≤ (L : ℝ) * (δ * K) := by positivity
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have := abs_sub (h (Q ω)) (redPsi h δ K R (Q ω))
      have := hB (Q ω)
      have := abs_redPsi_le hB hδ hK R (Q ω)
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact abs_sub_redPsi_le hL hδ hK R (hin ω hω)
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add (integrable_const _) (hInd.const_mul _),
    integral_const, integral_const_mul, integral_indicator_one hT]
  simp [measureReal_def]

end RedProb

/-- The comparison of `E h(Q)` from the comparison of the orthant probabilities on the grid. -/
private lemma red_compare {l : ℕ} {h : (Fin l → ℝ) → ℝ} {B : ℝ} {L : ℝ≥0} (hB : ∀ x, |h x| ≤ B)
    (hL : LipschitzWith L h) {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (R : ℕ) {p e : ℝ}
    {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₀ : Type} [MeasureSpace Ω₀] [IsProbabilityMeasure (ℙ : Measure Ω₀)]
    {Q₁ : Ω₁ → Fin l → ℝ} {Q₀ : Ω₀ → Fin l → ℝ} (hQ₁ : Measurable Q₁) (hQ₀ : Measurable Q₀)
    {T₁ : Set Ω₁} {T₀ : Set Ω₀} (hT₁ : MeasurableSet T₁) (hT₀ : MeasurableSet T₀)
    (hp₁ : (ℙ T₁).toReal ≤ p) (hp₀ : (ℙ T₀).toReal ≤ p)
    (hin₁ : ∀ ω ∉ T₁, ∀ j, |Q₁ ω j| ≤ δ * ((R : ℝ) - K - 1))
    (hin₀ : ∀ ω ∉ T₀, ∀ j, |Q₀ ω j| ≤ δ * ((R : ℝ) - K - 1))
    (hcmp : ∀ m ∈ redBox l (R + K),
      |(∫ ω, redInd (fun i => δ * m i) (Q₁ ω)) - ∫ ω, redInd (fun i => δ * m i) (Q₀ ω)| ≤
        ((∫ ω, redInd (fun i => δ * m i - δ) (Q₀ ω)) -
          ∫ ω, redInd (fun i => δ * m i + δ) (Q₀ ω)) + e) :
    |(∫ ω, h (Q₁ ω)) - ∫ ω, h (Q₀ ω)| ≤
      2 * (L * (δ * K) + 2 * B * p) +
        B * (2 / K) ^ l * (2 * l * (2 * ((R + K : ℕ) : ℝ)) ^ (l - 1) +
          (2 * ((R + K : ℕ) : ℝ)) ^ l * e) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have a1 := red_approx hB hL hδ hK R hQ₁ hT₁ hin₁
  have a0 := red_approx hB hL hδ hK R hQ₀ hT₀ hin₀
  have hI : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {Q : Ω → Fin l → ℝ}, Measurable Q → ∀ s : Fin l → ℝ, Integrable fun ω => redInd s (Q ω) :=
    fun hQ s => red_integrable ((measurable_redInd s).comp hQ) fun ω => by
      rw [abs_of_nonneg (redInd_nonneg _ _)]; exact redInd_le_one _ _
  have hPsi : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {Q : Ω → Fin l → ℝ}, Measurable Q → (∫ ω, redPsi h δ K R (Q ω)) =
        ∑ m ∈ redBox l (R + K), redCoef h δ K R m * ∫ ω, redInd (fun i => δ * m i) (Q ω) := by
    intro Ω _ _ Q hQ
    simp_rw [redPsi_eq h δ hK R]
    rw [integral_finsetSum _ fun m _ => (hI hQ _).const_mul _]
    simp_rw [integral_const_mul]
  set c := B * (2 / (K : ℝ)) ^ l with hc
  have hmid : |(∫ ω, redPsi h δ K R (Q₁ ω)) - ∫ ω, redPsi h δ K R (Q₀ ω)| ≤
      c * (2 * l * (2 * ((R + K : ℕ) : ℝ)) ^ (l - 1) + (2 * ((R + K : ℕ) : ℝ)) ^ l * e) := by
    rw [hPsi hQ₁, hPsi hQ₀, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ m ∈ redBox l (R + K),
        |redCoef h δ K R m * ((∫ ω, redInd (fun i => δ * m i) (Q₁ ω)) -
          ∫ ω, redInd (fun i => δ * m i) (Q₀ ω))| ≤
        c * (((∫ ω, redInd (fun i => δ * m i - δ) (Q₀ ω)) -
          ∫ ω, redInd (fun i => δ * m i + δ) (Q₀ ω)) + e) := by
      intro m hm
      rw [abs_mul]
      exact mul_le_mul (abs_redCoef_le hB δ hK R m) (hcmp m hm) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_add_distrib, Finset.sum_const]
    have hcard : ((redBox l (R + K)).card : ℝ) = (2 * ((R + K : ℕ) : ℝ)) ^ l := by
      rw [redBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Int.card_Ico]
      push_cast
      have : ((R : ℤ) + K - -((R : ℤ) + K)).toNat = 2 * (R + K) := by omega
      rw [this]; push_cast; ring
    rw [nsmul_eq_mul, hcard]
    refine add_le_add ?_ le_rfl
    have hs : ∑ m ∈ redBox l (R + K), ((∫ ω, redInd (fun i => δ * m i - δ) (Q₀ ω)) -
        ∫ ω, redInd (fun i => δ * m i + δ) (Q₀ ω)) =
        ∫ ω, ∑ m ∈ redBox l (R + K), (redInd (fun i => δ * m i - δ) (Q₀ ω) -
          redInd (fun i => δ * m i + δ) (Q₀ ω)) := by
      rw [integral_finsetSum (redBox l (R + K)) (f := fun m ω =>
        redInd (fun i => δ * m i - δ) (Q₀ ω) - redInd (fun i => δ * m i + δ) (Q₀ ω))
        fun m _ => (hI hQ₀ _).sub (hI hQ₀ _)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_sub (hI hQ₀ _) (hI hQ₀ _)]
    rw [hs]
    have hint : Integrable fun ω => ∑ m ∈ redBox l (R + K),
        (redInd (fun i => δ * m i - δ) (Q₀ ω) - redInd (fun i => δ * m i + δ) (Q₀ ω)) :=
      integrable_finsetSum (redBox l (R + K)) (f := fun m ω =>
        redInd (fun i => δ * m i - δ) (Q₀ ω) - redInd (fun i => δ * m i + δ) (Q₀ ω))
        fun m _ => (hI hQ₀ _).sub (hI hQ₀ _)
    calc (∫ ω, ∑ m ∈ redBox l (R + K),
          (redInd (fun i => δ * m i - δ) (Q₀ ω) - redInd (fun i => δ * m i + δ) (Q₀ ω)))
        ≤ ∫ _ω : Ω₀, 2 * l * (2 * ((R + K : ℕ) : ℝ)) ^ (l - 1) :=
          integral_mono hint (integrable_const _) fun ω => red_shell hδ (R + K) (Q₀ ω)
      _ = 2 * l * (2 * ((R + K : ℕ) : ℝ)) ^ (l - 1) := by simp
  have t1 := abs_sub_le (∫ ω, h (Q₁ ω)) (∫ ω, redPsi h δ K R (Q₁ ω)) (∫ ω, h (Q₀ ω))
  have t2 := abs_sub_le (∫ ω, redPsi h δ K R (Q₁ ω)) (∫ ω, redPsi h δ K R (Q₀ ω))
    (∫ ω, h (Q₀ ω))
  rw [abs_sub_comm (∫ ω, redPsi h δ K R (Q₀ ω))] at t2
  have hp1 : 2 * B * (ℙ T₁).toReal ≤ 2 * B * p := by gcongr
  have hp0 : 2 * B * (ℙ T₀).toReal ≤ 2 * B * p := by gcongr
  linarith

/-! ### Measurability of the spectral functionals -/

/-- `A ↦ λ_i(A)` is measurable. -/
private lemma red_measurable_sortedEig (n i : ℕ) :
    Measurable fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i := by
  set H : Set (Matrix (Fin n) (Fin n) ℝ) := {A | A.IsHermitian} with hH
  have hHc : IsClosed H := by
    have : H = {A | Aᴴ = A} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have hpw : (fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i) =
      H.piecewise (fun A => sortedEig A i) (fun _ => 0) := by
    funext A
    by_cases hA : A ∈ H
    · rw [Set.piecewise_eq_of_mem _ _ _ hA]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hA]
      unfold sortedEig
      rw [dite_eq_right_iff]
      exact fun h => absurd h.1 hA
  rw [hpw]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hHc.measurableSet
  have hl : LipschitzOnWith 1 (fun A : Matrix (Fin n) (Fin n) ℝ => sortedEig A i) H := by
    refine LipschitzOnWith.of_dist_le_mul fun A hA B hB => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact sortedEig_lipschitz hA hB i
  exact hl.continuousOn

/-- For symmetric `A`, a sum over the spectrum is a sum over the ordered eigenvalues. -/
private lemma red_sum_specOf {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (φ : ℝ → ℝ) :
    ∑ j, φ (specOf A j) = ∑ k : Fin (Fintype.card (Fin n)), φ (sortedEig A (k + 1)) := by
  rw [specOf_eq hA]
  unfold Matrix.IsHermitian.eigenvalues
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => φ (hA.eigenvalues₀ k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hk := k.2
  unfold sortedEig
  rw [dite_eq_left ⟨hA, by omega, by omega⟩]
  congr 1

private lemma red_measurable_smCount {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    {A : Ω → Matrix (Fin n) (Fin n) ℝ} (hA : Measurable A) (hH : ∀ ω, (A ω).IsHermitian)
    (η E₁ E₂ : ℝ) : Measurable fun ω => smCount (A ω) η E₁ E₂ := by
  have : (fun ω => smCount (A ω) η E₁ E₂) = fun ω =>
      ∑ k : Fin (Fintype.card (Fin n)),
        (fun x => (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi)
          (sortedEig (A ω) (k + 1)) := by
    funext ω
    unfold smCount
    exact red_sum_specOf (hH ω)
      (fun x => (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi)
  rw [this]
  refine Finset.measurable_sum _ fun k _ => ?_
  have hc : Continuous fun x : ℝ =>
      (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi := by fun_prop
  exact hc.measurable.comp ((red_measurable_sortedEig n _).comp hA)

private lemma red_measurable_edgeQ {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    {A : Ω → Matrix (Fin n) (Fin n) ℝ} (hA : Measurable A) (N : ℕ) (a ϖ : ℝ) (d l : ℕ) :
    Measurable fun ω => edgeQ N a ϖ d l (A ω) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold edgeQ
  exact measurable_const.mul (((red_measurable_sortedEig n _).comp hA).sub measurable_const)

/-! ### The smooth cut-off functional `F(x) = ∏_i K_i(x_i)` -/

/-- The cut-off `K_i(x) = S(3(x - i - 1) + 2)`: `0` for `x ≤ i + 1/3`, `1` for `x ≥ i + 2/3`. -/
private def redCut (i : ℕ) (x : ℝ) : ℝ := Real.smoothTransition (3 * x - 3 * (i + 1) + 2)

/-- `F(x) = ∏_i K_i(x_i)`. -/
private def redF (l : ℕ) (x : Fin l → ℝ) : ℝ := ∏ i : Fin l, redCut i (x i)

private lemma redCut_nonneg (i : ℕ) (x : ℝ) : 0 ≤ redCut i x := Real.smoothTransition.nonneg _

private lemma redCut_le_one (i : ℕ) (x : ℝ) : redCut i x ≤ 1 := Real.smoothTransition.le_one _

private lemma redCut_eq_zero {i : ℕ} {x : ℝ} (hx : x ≤ i + 1 / 3) : redCut i x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private lemma redCut_eq_one {i : ℕ} {x : ℝ} (hx : i + 2 / 3 ≤ x) : redCut i x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private lemma redF_nonneg (l : ℕ) (x : Fin l → ℝ) : 0 ≤ redF l x :=
  Finset.prod_nonneg fun _ _ => redCut_nonneg _ _

private lemma redF_le_one (l : ℕ) (x : Fin l → ℝ) : redF l x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => redCut_nonneg _ _) fun _ _ => redCut_le_one _ _

private lemma smoothTransition_deriv_bound :
    ∃ D : ℝ, ∀ k ≤ 5, ∀ y, ‖iteratedFDeriv ℝ k Real.smoothTransition y‖ ≤ D := by
  have hk : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k Real.smoothTransition y‖ ≤ C := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨1, fun y => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · have hc : Continuous fun y => iteratedFDeriv ℝ k Real.smoothTransition y :=
        (Real.smoothTransition.contDiff (n := ⊤)).continuous_iteratedFDeriv (by simp)
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hc.continuousOn (s := Set.Icc (0 : ℝ) 1))
      refine ⟨max C 0, fun y => ?_⟩
      by_cases h0 : y < 0
      · have he : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 :=
          Filter.eventuallyEq_of_mem (Iio_mem_nhds h0) fun z hz =>
            Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
        rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
        simp
      by_cases h1 : 1 < y
      · have he : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 1 :=
          Filter.eventuallyEq_of_mem (Ioi_mem_nhds h1) fun z hz =>
            Real.smoothTransition.one_of_one_le (le_of_lt hz)
        rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
        simp
      exact (hC y ⟨not_lt.1 h0, not_lt.1 h1⟩).trans (le_max_left _ _)
  choose C hC using hk
  refine ⟨∑ k ∈ Finset.range 6, |C k|, fun k hk5 y => ?_⟩
  refine (hC k y).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

private lemma redCut_comp_eq (l : ℕ) (i : Fin l) :
    (fun x : Fin l → ℝ => redCut i (x i)) =
      (fun y => Real.smoothTransition (y + (-3 * ((i : ℝ) + 1) + 2))) ∘
        ((3 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin l => ℝ) i) := by
  funext x
  simp only [redCut, Function.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  ring

private lemma redCut_contDiff (l : ℕ) (i : Fin l) :
    ContDiff ℝ 5 fun x : Fin l → ℝ => redCut i (x i) := by
  rw [redCut_comp_eq]
  exact ((Real.smoothTransition.contDiff (n := 5)).comp (contDiff_id.add contDiff_const)).comp
    (ContinuousLinearMap.contDiff _)

/-- `F ∈ C⁵` with bounded derivatives of order `≤ 5`. -/
private lemma redF_smooth (l : ℕ) :
    ContDiff ℝ 5 (redF l) ∧ ∃ Cb : ℝ, ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m (redF l) x‖ ≤ Cb := by
  have hfd : ∀ i : Fin l, ContDiff ℝ 5 fun x : Fin l → ℝ => redCut i (x i) :=
    fun i => redCut_contDiff l i
  have hF : redF l = fun x => ∏ j ∈ (Finset.univ : Finset (Fin l)),
      (fun x : Fin l → ℝ => redCut j (x j)) x := rfl
  refine ⟨?_, ?_⟩
  · rw [hF]; exact contDiff_prod fun i _ => hfd i
  obtain ⟨D, hD⟩ := smoothTransition_deriv_bound
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (by norm_num) 0)
  have hfac : ∀ (i : Fin l) (k : ℕ), k ≤ 5 → ∀ x,
      ‖iteratedFDeriv ℝ k (fun x : Fin l → ℝ => redCut i (x i)) x‖ ≤ D * 3 ^ 5 := by
    intro i k hk x
    set g : (Fin l → ℝ) →L[ℝ] ℝ :=
      (3 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin l => ℝ) i with hg
    have hg3 : ‖g‖ ≤ 3 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
      simp only [hg, _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (by norm_num)
    have hs : ContDiff ℝ 5 fun y => Real.smoothTransition (y + (-3 * ((i : ℝ) + 1) + 2)) :=
      (Real.smoothTransition.contDiff (n := 5)).comp (contDiff_id.add contDiff_const)
    rw [redCut_comp_eq, g.iteratedFDeriv_comp_right hs x (by exact_mod_cast hk)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h1 := hD k hk (g x + (-3 * ((i : ℝ) + 1) + 2))
    have h2 : ‖g‖ ^ k ≤ 3 ^ 5 :=
      (pow_le_pow_left₀ (norm_nonneg _) hg3 k).trans
        (pow_le_pow_right₀ (by norm_num) hk)
    exact mul_le_mul h1 h2 (by positivity) hD0
  set C : ℕ → ℝ := fun n => ∑ p ∈ (Finset.univ : Finset (Fin l)).sym n,
    ((p : Multiset (Fin l)).countPerms : ℝ) * (D * 3 ^ 5) ^ l with hC
  refine ⟨∑ n ∈ Finset.range 6, C n, fun m hm x => ?_⟩
  have hb := norm_iteratedFDeriv_prod_le (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin l)))
    (f := fun (j : Fin l) (x : Fin l → ℝ) => redCut j (x j)) (N := 5) (fun i _ => hfd i)
    (x := x) (n := m)
    (by exact_mod_cast hm)
  rw [hF]
  refine hb.trans ?_
  have hCm : C m ≤ ∑ n ∈ Finset.range 6, C n := by
    refine Finset.single_le_sum (f := C) (fun n _ => ?_) (Finset.mem_range.2 (by omega))
    exact Finset.sum_nonneg fun p _ => by positivity
  refine le_trans ?_ hCm
  refine Finset.sum_le_sum fun p hp => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∏ j ∈ Finset.univ,
        ‖iteratedFDeriv ℝ ((p : Multiset (Fin l)).count j) (fun x : Fin l → ℝ => redCut j (x j)) x‖
      ≤ ∏ _j ∈ (Finset.univ : Finset (Fin l)), D * 3 ^ 5 := by
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => hfac j _ ?_ x
        have := Multiset.count_le_card j (p : Multiset (Fin l))
        rw [Sym.card_coe] at this
        omega
    _ = (D * 3 ^ 5) ^ l := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Bracketing of `1(q ≥ s)` by `F(𝒳)` on the edge regime -/

private lemma red_eigCount_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E : ℝ) :
    eigCount A E ≤ n := by
  unfold eigCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- `s ≤ q_i` iff at least `d + i + 1` eigenvalues are `≥ a + s ϖ N^{-2/3}`. -/
private lemma red_q_ge_iff {N n d l : ℕ} {a ϖ : ℝ} (hϖ : 0 < ϖ) (hw : 0 < (N : ℝ) ^ (2 / 3 : ℝ))
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hdl : d + l ≤ n) (i : Fin l) (s₀ : ℝ) :
    s₀ ≤ edgeQ N a ϖ d l A i ↔
      d + ((i : ℕ) + 1) ≤ eigCount A (a + s₀ * ϖ / (N : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [← sortedEig_ge_iff hA (by omega) (by omega)]
  unfold edgeQ
  set w := (N : ℝ) ^ (2 / 3 : ℝ)
  set lam := sortedEig A (d + ((i : ℕ) + 1))
  rw [div_mul_eq_mul_div, le_div_iff₀ hϖ]
  have : a + s₀ * ϖ / w ≤ lam ↔ s₀ * ϖ / w ≤ lam - a := by
    constructor <;> intro h <;> linarith
  rw [this, div_le_iff₀ hw, mul_comm (lam - a) w]

/-- On the edge regime, the cut-off functional of `𝒳` brackets the orthant indicator of `q`. -/
private lemma red_point {N n d l : ℕ} {a ϖ ε δr r₀ C₀ δ : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hreg : EdgeRegime N a d l δr r₀ C₀ A) (hϖ : 0 < ϖ)
    (hw : 0 < (N : ℝ) ^ (2 / 3 : ℝ))
    (hbr : ∀ E, |E - a| ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2 →
      smCount A (etaE N ε) (E + ellE N ε) (edgeEL N a ε) - (N : ℝ) ^ (-5 * ε) ≤
          (eigCount A E : ℝ) - d ∧
        (eigCount A E : ℝ) - d ≤
          smCount A (etaE N ε) (E - ellE N ε) (edgeEL N a ε) + (N : ℝ) ^ (-5 * ε))
    (h5 : (N : ℝ) ^ (-5 * ε) ≤ 1 / 3) (hshift : 2 * ellE N ε ≤ δ * ϖ / (N : ℝ) ^ (2 / 3 : ℝ))
    (s : Fin l → ℝ)
    (hs : ∀ i, |s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ)| + 2 * ellE N ε ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2) :
    redInd s (edgeQ N a ϖ d l A) ≤ redF l (fun i => smCount A (etaE N ε)
        (a + s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) - ellE N ε) (edgeEL N a ε)) ∧
      redF l (fun i => smCount A (etaE N ε)
        (a + s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) - ellE N ε) (edgeEL N a ε)) ≤
        redInd (fun i => s i - δ) (edgeQ N a ϖ d l A) ∧
      redInd (fun i => s i + δ) (edgeQ N a ϖ d l A) ≤ redF l (fun i => smCount A (etaE N ε)
        (a + s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) + ellE N ε) (edgeEL N a ε)) ∧
      redF l (fun i => smCount A (etaE N ε)
        (a + s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) + ellE N ε) (edgeEL N a ε)) ≤
        redInd s (edgeQ N a ϖ d l A) := by
  set w := (N : ℝ) ^ (2 / 3 : ℝ) with hw_def
  set ℓ := ellE N ε with hℓ
  set X := fun E => smCount A (etaE N ε) E (edgeEL N a ε) with hX
  have hdl : d + l ≤ n := hreg.2.2.1.trans (red_eigCount_le A _)
  have hq := fun i s₀ => red_q_ge_iff (N := N) (a := a) hϖ hw hA hdl i s₀
  -- the bracket at `E_i`, `E_i ± 2ℓ`
  have hE : ∀ i : Fin l, ∀ t : ℝ, |t| ≤ 2 * ℓ →
      |a + s i * ϖ / w + t - a| ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2 := by
    intro i t ht
    have := hs i
    calc |a + s i * ϖ / w + t - a| = |s i * ϖ / w + t| := by ring_nf
      _ ≤ |s i * ϖ / w| + |t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; unfold ellE; positivity
  have hb0 := fun i => hbr (a + s i * ϖ / w) (by
    have h0 := hE i 0 (by rw [abs_zero]; linarith)
    rwa [add_zero] at h0)
  have hbm := fun i => hbr _ (hE i (-(2 * ℓ)) (by rw [abs_neg, abs_of_nonneg (by linarith)]))
  have hbp := fun i => hbr _ (hE i (2 * ℓ) (by rw [abs_of_nonneg (by linarith)]))
  have em : ∀ i : Fin l, a + s i * ϖ / w + -(2 * ℓ) + ℓ = a + s i * ϖ / w - ℓ := fun i => by ring
  have ep : ∀ i : Fin l, a + s i * ϖ / w + 2 * ℓ - ℓ = a + s i * ϖ / w + ℓ := fun i => by ring
  have hshm : ∀ i : Fin l, a + (s i - δ) * ϖ / w ≤ a + s i * ϖ / w + -(2 * ℓ) := by
    intro i; have : (s i - δ) * ϖ / w = s i * ϖ / w - δ * ϖ / w := by ring
    rw [this]; linarith
  have hshp : ∀ i : Fin l, a + s i * ϖ / w + 2 * ℓ ≤ a + (s i + δ) * ϖ / w := by
    intro i; have : (s i + δ) * ϖ / w = s i * ϖ / w + δ * ϖ / w := by ring
    rw [this]; linarith
  have cnt_ge : ∀ (i : Fin l) (E : ℝ), d + ((i : ℕ) + 1) ≤ eigCount A E →
      (i : ℝ) + 1 ≤ (eigCount A E : ℝ) - d := by
    intro i E h
    have : ((d + ((i : ℕ) + 1) : ℕ) : ℝ) ≤ eigCount A E := by exact_mod_cast h
    push_cast at this; linarith
  have cnt_le : ∀ (i : Fin l) (E : ℝ), ¬ d + ((i : ℕ) + 1) ≤ eigCount A E →
      (eigCount A E : ℝ) - d ≤ i := by
    intro i E h
    have : eigCount A E ≤ d + i := by omega
    have : (eigCount A E : ℝ) ≤ ((d + i : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  unfold redInd redF
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num) fun i _ => ?_
    split_ifs with h
    · rw [redCut_eq_one]
      have := cnt_ge i _ ((hq i _).1 h)
      have := (hb0 i).2
      linarith
    · exact redCut_nonneg _ _
  · refine Finset.prod_le_prod₀ (fun _ _ => redCut_nonneg _ _) fun i _ => ?_
    split_ifs with h
    · exact redCut_le_one _ _
    · rw [redCut_eq_zero]
      have h1 : ¬ d + ((i : ℕ) + 1) ≤ eigCount A (a + s i * ϖ / w + -(2 * ℓ)) := by
        intro h'
        exact h ((hq i _).2 (h'.trans (eigCount_antitone A (hshm i))))
      have := cnt_le i _ h1
      have := (hbm i).1
      rw [em i] at this
      linarith
  · refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num) fun i _ => ?_
    split_ifs with h
    · rw [redCut_eq_one]
      have h1 : d + ((i : ℕ) + 1) ≤ eigCount A (a + s i * ϖ / w + 2 * ℓ) :=
        ((hq i _).1 h).trans (eigCount_antitone A (hshp i))
      have := cnt_ge i _ h1
      have := (hbp i).2
      rw [ep i] at this
      linarith
    · exact redCut_nonneg _ _
  · refine Finset.prod_le_prod₀ (fun _ _ => redCut_nonneg _ _) fun i _ => ?_
    split_ifs with h
    · exact redCut_le_one _ _
    · rw [redCut_eq_zero]
      have h1 : ¬ d + ((i : ℕ) + 1) ≤ eigCount A (a + s i * ϖ / w) := fun h' => h ((hq i _).2 h')
      have := cnt_le i _ h1
      have := (hb0 i).1
      linarith

private lemma redInd_anti {l : ℕ} {s t : Fin l → ℝ} (hst : ∀ i, s i ≤ t i) (x : Fin l → ℝ) :
    redInd t x ≤ redInd s x := by
  unfold redInd
  refine Finset.prod_le_prod₀ (fun _ _ => by split_ifs <;> norm_num) fun i _ => ?_
  by_cases h : t i ≤ x i
  · rw [ite_eq_left h, ite_eq_left ((hst i).trans h)]
  · rw [ite_eq_right h]; split_ifs <;> norm_num

private lemma red_integral_le_add {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {f g : Ω → ℝ} (hf : Integrable f) (hg : Integrable g) {T : Set Ω} (hT : MeasurableSet T)
    (hfg : ∀ ω, f ω ≤ g ω + T.indicator 1 ω) : (∫ ω, f ω) ≤ (∫ ω, g ω) + (ℙ T).toReal := by
  have hInd : Integrable (T.indicator (1 : Ω → ℝ)) := (integrable_const (1 : ℝ)).indicator hT
  calc (∫ ω, f ω) ≤ ∫ ω, (g ω + T.indicator 1 ω) := integral_mono hf (hg.add hInd) hfg
    _ = (∫ ω, g ω) + (ℙ T).toReal := by
      rw [integral_add hg hInd, integral_indicator_one hT, measureReal_def]

/-- The comparison of the orthant probabilities `P(q ≥ s)` at one point `s`. -/
private lemma red_point_compare {N n d l : ℕ} {a ϖ ε δr r₀ C₀ δ c₁ Cb p : ℝ}
    {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₀ : Type} [MeasureSpace Ω₀] [IsProbabilityMeasure (ℙ : Measure Ω₀)]
    {A₁ : Ω₁ → Matrix (Fin n) (Fin n) ℝ} {A₀ : Ω₀ → Matrix (Fin n) (Fin n) ℝ}
    (hA₁ : Measurable A₁) (hA₀ : Measurable A₀) (hH₁ : ∀ ω, (A₁ ω).IsHermitian)
    (hH₀ : ∀ ω, (A₀ ω).IsHermitian) {T₁ : Set Ω₁} {T₀ : Set Ω₀} (hT₁ : MeasurableSet T₁)
    (hT₀ : MeasurableSet T₀) (hp₁ : (ℙ T₁).toReal ≤ p) (hp₀ : (ℙ T₀).toReal ≤ p)
    (hG₁ : ∀ ω ∉ T₁, EdgeRegime N a d l δr r₀ C₀ (A₁ ω))
    (hG₀ : ∀ ω ∉ T₀, EdgeRegime N a d l δr r₀ C₀ (A₀ ω))
    (hbr : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian → EdgeRegime N a d l δr r₀ C₀ A →
      ∀ E, |E - a| ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2 →
        smCount A (etaE N ε) (E + ellE N ε) (edgeEL N a ε) - (N : ℝ) ^ (-5 * ε) ≤
            (eigCount A E : ℝ) - d ∧
          (eigCount A E : ℝ) - d ≤
            smCount A (etaE N ε) (E - ellE N ε) (edgeEL N a ε) + (N : ℝ) ^ (-5 * ε))
    (hϖ : 0 < ϖ) (hw : 0 < (N : ℝ) ^ (2 / 3 : ℝ)) (h5 : (N : ℝ) ^ (-5 * ε) ≤ 1 / 3)
    (hshift : 2 * ellE N ε ≤ δ * ϖ / (N : ℝ) ^ (2 / 3 : ℝ))
    (hSC : SmoothComparable N a ε c₁ l A₁ A₀)
    (hCb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m (redF l) x‖ ≤ Cb)
    (s : Fin l → ℝ)
    (hs : ∀ i, |s i * ϖ / (N : ℝ) ^ (2 / 3 : ℝ)| + 2 * ellE N ε ≤ (N : ℝ) ^ (-2 / 3 + ε) / 2) :
    |(∫ ω, redInd s (edgeQ N a ϖ d l (A₁ ω))) - ∫ ω, redInd s (edgeQ N a ϖ d l (A₀ ω))| ≤
      ((∫ ω, redInd (fun i => s i - δ) (edgeQ N a ϖ d l (A₀ ω))) -
        ∫ ω, redInd (fun i => s i + δ) (edgeQ N a ϖ d l (A₀ ω))) +
        (Cb * (N : ℝ) ^ (-c₁) + 2 * p) := by
  set w := (N : ℝ) ^ (2 / 3 : ℝ) with hw_def
  set ℓ := ellE N ε with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; unfold ellE; positivity
  have hF := (redF_smooth l).1
  -- integrability
  have hIi : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {A : Ω → Matrix (Fin n) (Fin n) ℝ}, Measurable A → ∀ s' : Fin l → ℝ,
      Integrable fun ω => redInd s' (edgeQ N a ϖ d l (A ω)) :=
    fun hA s' => red_integrable ((measurable_redInd s').comp (red_measurable_edgeQ hA N a ϖ d l))
      fun ω => by rw [abs_of_nonneg (redInd_nonneg _ _)]; exact redInd_le_one _ _
  have hFi : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {A : Ω → Matrix (Fin n) (Fin n) ℝ}, Measurable A → (∀ ω, (A ω).IsHermitian) →
      ∀ E : Fin l → ℝ, Integrable fun ω =>
        redF l (fun j => smCount (A ω) (etaE N ε) (E j) (edgeEL N a ε)) := by
    intro Ω _ _ A hA hH E
    refine red_integrable (C := 1) (hF.continuous.measurable.comp
      (measurable_pi_iff.2 fun j => red_measurable_smCount hA hH _ _ _)) fun ω => ?_
    rw [abs_of_nonneg (redF_nonneg _ _)]; exact redF_le_one _ _
  -- the comparison hypothesis at the windows `E_j ∓ ℓ`
  have hwin : ∀ t : ℝ, |t| ≤ ℓ → ∀ j, |a + s j * ϖ / w + t - a| ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
    intro t ht j
    have h1 := hs j
    have h2 : 0 ≤ (N : ℝ) ^ (-2 / 3 + ε) := by positivity
    calc |a + s j * ϖ / w + t - a| = |s j * ϖ / w + t| := by ring_nf
      _ ≤ |s j * ϖ / w| + |t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hCm := hSC (redF l) Cb hF hCb (fun j => a + s j * ϖ / w + -ℓ)
    (hwin (-ℓ) (by rw [abs_neg, abs_of_nonneg hℓ0]))
  have hCp := hSC (redF l) Cb hF hCb (fun j => a + s j * ϖ / w + ℓ)
    (hwin ℓ (by rw [abs_of_nonneg hℓ0]))
  simp only [← sub_eq_add_neg] at hCm
  rw [abs_le] at hCm hCp
  -- pointwise brackets
  have hpt : ∀ {Ω : Type} [MeasureSpace Ω] {A : Ω → Matrix (Fin n) (Fin n) ℝ} {T : Set Ω},
      (∀ ω, (A ω).IsHermitian) → (∀ ω ∉ T, EdgeRegime N a d l δr r₀ C₀ (A ω)) → ∀ ω,
      redInd s (edgeQ N a ϖ d l (A ω)) ≤ redF l (fun i => smCount (A ω) (etaE N ε)
          (a + s i * ϖ / w - ℓ) (edgeEL N a ε)) + T.indicator 1 ω ∧
      redF l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w - ℓ) (edgeEL N a ε)) ≤
          redInd (fun i => s i - δ) (edgeQ N a ϖ d l (A ω)) + T.indicator 1 ω ∧
      redInd (fun i => s i + δ) (edgeQ N a ϖ d l (A ω)) ≤ redF l (fun i => smCount (A ω)
          (etaE N ε) (a + s i * ϖ / w + ℓ) (edgeEL N a ε)) + T.indicator 1 ω ∧
      redF l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w + ℓ) (edgeEL N a ε)) ≤
          redInd s (edgeQ N a ϖ d l (A ω)) + T.indicator 1 ω := by
    intro Ω _ A T hH hG ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [redInd_le_one s (edgeQ N a ϖ d l (A ω)),
        redInd_le_one (fun i => s i + δ) (edgeQ N a ϖ d l (A ω)),
        redInd_nonneg s (edgeQ N a ϖ d l (A ω)),
        redInd_nonneg (fun i => s i - δ) (edgeQ N a ϖ d l (A ω)),
        redF_le_one l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w - ℓ) (edgeEL N a ε)),
        redF_le_one l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w + ℓ) (edgeEL N a ε)),
        redF_nonneg l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w - ℓ) (edgeEL N a ε)),
        redF_nonneg l (fun i => smCount (A ω) (etaE N ε) (a + s i * ϖ / w + ℓ) (edgeEL N a ε))]
    · rw [Set.indicator_of_notMem hω, add_zero, add_zero, add_zero, add_zero]
      exact red_point (hH ω) (hG ω hω) hϖ hw (hbr _ (hH ω) (hG ω hω)) h5 hshift s hs
  have q1 := red_integral_le_add (hIi hA₁ s) (hFi hA₁ hH₁ _) hT₁ fun ω => (hpt hH₁ hG₁ ω).1
  have q2 := red_integral_le_add (hFi hA₀ hH₀ _) (hIi hA₀ _) hT₀ fun ω => (hpt hH₀ hG₀ ω).2.1
  have q3 := red_integral_le_add (hIi hA₀ _) (hFi hA₀ hH₀ _) hT₀ fun ω => (hpt hH₀ hG₀ ω).2.2.1
  have q4 := red_integral_le_add (hFi hA₁ hH₁ _) (hIi hA₁ s) hT₁ fun ω => (hpt hH₁ hG₁ ω).2.2.2
  have m1 : (∫ ω, redInd (fun i => s i + δ) (edgeQ N a ϖ d l (A₀ ω))) ≤
      ∫ ω, redInd s (edgeQ N a ϖ d l (A₀ ω)) := by
    refine integral_mono (hIi hA₀ _) (hIi hA₀ _) fun ω => redInd_anti (fun i => ?_) _
    have : 0 ≤ δ := by
      have := hshift
      have : 0 ≤ δ * ϖ / w := by linarith
      by_contra hδ
      have : δ * ϖ / w < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hϖ) hw
      linarith
    linarith
  have m2 : (∫ ω, redInd s (edgeQ N a ϖ d l (A₀ ω))) ≤
      ∫ ω, redInd (fun i => s i - δ) (edgeQ N a ϖ d l (A₀ ω)) := by
    refine integral_mono (hIi hA₀ _) (hIi hA₀ _) fun ω => redInd_anti (fun i => ?_) _
    have : 0 ≤ δ := by
      have := hshift
      have : 0 ≤ δ * ϖ / w := by linarith
      by_contra hδ
      have : δ * ϖ / w < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hϖ) hw
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith [hCm.1, hCm.2, hCp.1, hCp.2]

/-- On the edge regime, `|q_i| ≤ N^{2/3} ϖ⁻¹ N^{-2/3+δ}`. -/
private lemma red_q_abs_le {N n d l : ℕ} {a ϖ δr r₀ C₀ : ℝ} (hϖ : 0 < ϖ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hreg : EdgeRegime N a d l δr r₀ C₀ A)
    (i : Fin l) :
    |edgeQ N a ϖ d l A i| ≤ (N : ℝ) ^ (2 / 3 : ℝ) / ϖ * (N : ℝ) ^ (-2 / 3 + δr) := by
  have hdl : d + l ≤ n := hreg.2.2.1.trans (red_eigCount_le A _)
  set t := (N : ℝ) ^ (-2 / 3 + δr)
  set lam := sortedEig A (d + ((i : ℕ) + 1))
  have h1 : a - t ≤ lam :=
    (sortedEig_ge_iff hA (by omega) (by omega) _).2 (le_trans (by omega) hreg.2.2.1)
  have h2 : lam < a + t := by
    by_contra hc
    have := (sortedEig_ge_iff hA (i := d + ((i : ℕ) + 1)) (by omega) (by omega) _).1 (not_lt.1 hc)
    rw [hreg.1] at this
    omega
  unfold edgeQ
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_le]; constructor <;> linarith

private lemma red_rpow_split {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x ^ (-2 / 3 + y) = x ^ y / x ^ (2 / 3 : ℝ) := by
  rw [Real.rpow_add hx, show (-2 / 3 : ℝ) = -(2 / 3) by norm_num, Real.rpow_neg hx.le]
  ring


/-! ### The parameters of the reduction -/

section RedParam

variable {l : ℕ} {u ϖm : ℝ}

/-- The averaging length `K = ⌊u^{8l+6}⌋`. -/
private def redK (l : ℕ) (u : ℝ) : ℕ := ⌊u ^ (8 * l + 6)⌋₊

/-- The box half-width `R = ⌈u^{8l+9}⌉ + K + 1`. -/
private def redR (l : ℕ) (u : ℝ) : ℕ := ⌈u ^ (8 * l + 9)⌉₊ + redK l u + 1

/-- The grid step `δ = 2/(ϖ₋ u^{8l+8})`. -/
private def redδ (l : ℕ) (u ϖm : ℝ) : ℝ := 2 / (ϖm * u ^ (8 * l + 8))

private lemma redK_le (hu : 1 ≤ u) : (redK l u : ℝ) ≤ u ^ (8 * l + 6) :=
  Nat.floor_le (by positivity)

private lemma redK_ge (hu : 4 ≤ u) : u ^ (8 * l + 6) / 2 ≤ redK l u := by
  have h4 : 4 ≤ u ^ (8 * l + 6) := le_trans hu (le_self_pow₀ (by linarith) (by omega))
  have := Nat.lt_floor_add_one (u ^ (8 * l + 6))
  unfold redK
  linarith

private lemma one_le_redK (hu : 4 ≤ u) : 1 ≤ redK l u := by
  have h4 : 4 ≤ u ^ (8 * l + 6) := le_trans hu (le_self_pow₀ (by linarith) (by omega))
  have := redK_ge (l := l) hu
  have : (1 : ℝ) ≤ redK l u := by linarith
  exact_mod_cast this

private lemma redRK_le (hu : 1 ≤ u) : ((redR l u + redK l u : ℕ) : ℝ) ≤ 5 * u ^ (8 * l + 9) := by
  have h69 : u ^ (8 * l + 6) ≤ u ^ (8 * l + 9) := pow_le_pow_right₀ hu (by omega)
  have h1 : 1 ≤ u ^ (8 * l + 9) := one_le_pow₀ hu
  have := Nat.ceil_lt_add_one (show 0 ≤ u ^ (8 * l + 9) by positivity)
  have hK := redK_le (l := l) hu
  unfold redR; push_cast; linarith

private lemma redR_inner (hu : 1 ≤ u) (hϖm : 0 < ϖm) :
    u / ϖm ≤ redδ l u ϖm * ((redR l u : ℝ) - redK l u - 1) := by
  have e : (redR l u : ℝ) - redK l u - 1 = ⌈u ^ (8 * l + 9)⌉₊ := by unfold redR; push_cast; ring
  rw [e]
  have hc := Nat.le_ceil (u ^ (8 * l + 9))
  have hu0 : 0 < u := by linarith
  calc u / ϖm ≤ 2 * u / ϖm := by rw [div_le_div_iff_of_pos_right hϖm]; linarith
    _ = redδ l u ϖm * u ^ (8 * l + 9) := by
        unfold redδ; rw [show u ^ (8 * l + 9) = u ^ (8 * l + 8) * u from pow_succ _ _]
        field_simp
    _ ≤ redδ l u ϖm * ⌈u ^ (8 * l + 9)⌉₊ :=
        mul_le_mul_of_nonneg_left hc (by unfold redδ; positivity)

/-- The windows stay inside the bracket range: `|δ t ϖ / w| + 2ℓ ≤ N^{-2/3+ε}/2`. -/
private lemma red_window {ϖp ϖ w t : ℝ} (hϖm : 0 < ϖm) (hϖ1 : ϖm ≤ ϖ) (hϖ2 : ϖ ≤ ϖp)
    (hu : 40 * ϖp / ϖm + 4 ≤ u) (hw : 0 < w) (ht : |t| ≤ ((redR l u + redK l u : ℕ) : ℝ)) :
    |redδ l u ϖm * t * ϖ / w| + 2 * (1 / (u ^ (8 * l + 8) * w)) ≤ u ^ (8 * l + 8) / w / 2 := by
  have hϖp0 : 0 < ϖp := lt_of_lt_of_le hϖm (hϖ1.trans hϖ2)
  have hϖ0 : 0 < ϖ := lt_of_lt_of_le hϖm hϖ1
  have hc0 : 0 ≤ ϖp / ϖm := by positivity
  have : 0 ≤ 40 * ϖp / ϖm := by positivity
  have hu4 : 4 ≤ u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  set a₈ := u ^ (8 * l + 8) with ha₈
  have ha₈1 : 1 ≤ a₈ := one_le_pow₀ hu1
  have hδ0 : 0 < redδ l u ϖm := by unfold redδ; positivity
  have e1 : |redδ l u ϖm * t * ϖ / w| ≤ 10 * u * ϖp / ϖm / w := by
    rw [abs_div, abs_of_pos hw, abs_mul, abs_mul, abs_of_pos hδ0, abs_of_pos hϖ0]
    refine div_le_div_of_nonneg_right ?_ hw.le
    calc redδ l u ϖm * |t| * ϖ ≤ redδ l u ϖm * (5 * u ^ (8 * l + 9)) * ϖp :=
          mul_le_mul (mul_le_mul_of_nonneg_left (ht.trans (redRK_le hu1)) hδ0.le) hϖ2
            hϖ0.le (by positivity)
      _ = 10 * u * ϖp / ϖm := by
          unfold redδ; rw [show u ^ (8 * l + 9) = u ^ (8 * l + 8) * u from pow_succ _ _]
          field_simp; ring
  have e2 : 2 * (1 / (a₈ * w)) ≤ 2 / w := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hw (le_mul_of_one_le_left hw.le ha₈1)
  have e3 : 10 * u * ϖp / ϖm + 2 ≤ a₈ / 2 := by
    have hu2 : u ^ 2 ≤ a₈ := by rw [ha₈]; exact pow_le_pow_right₀ hu1 (by omega)
    set c := ϖp / ϖm with hc
    have h40 : 40 * c + 4 ≤ u := by
      have : 40 * ϖp / ϖm = 40 * c := by rw [hc]; ring
      linarith
    have h1 : u * (40 * c + 4) ≤ u * u := mul_le_mul_of_nonneg_left h40 hu0.le
    have h2 : 10 * u * ϖp / ϖm = 10 * (u * c) := by rw [hc]; ring
    have h3 : 0 ≤ u * c := mul_nonneg hu0.le hc0
    have h4 : u * u = u ^ 2 := by ring
    rw [h2]
    nlinarith
  calc |redδ l u ϖm * t * ϖ / w| + 2 * (1 / (a₈ * w))
      ≤ 10 * u * ϖp / ϖm / w + 2 / w := add_le_add e1 e2
    _ = (10 * u * ϖp / ϖm + 2) / w := by ring
    _ ≤ (a₈ / 2) / w := div_le_div_of_nonneg_right e3 hw.le
    _ = a₈ / w / 2 := by ring

/-- The shell term: `(2/K)^l 2l (2(R+K))^{l-1} ≤ 2 l 40^l u^{-2}`. -/
private lemma red_shell_arith (hu : 4 ≤ u) :
    (2 / (redK l u : ℝ)) ^ l * (2 * l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ (l - 1)) ≤
      2 * l * 40 ^ l / u ^ 2 := by
  have hu1 : 1 ≤ u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  set a₆ := u ^ (8 * l + 6) with ha₆
  have ha₆4 : 4 ≤ a₆ := le_trans hu (le_self_pow₀ hu1 (by omega))
  have hK0 : (0 : ℝ) < redK l u := by have := redK_ge (l := l) hu; linarith
  have h2K : 2 / (redK l u : ℝ) ≤ 4 / a₆ := by
    rw [div_le_div_iff₀ hK0 (by linarith)]; have := redK_ge (l := l) hu; linarith
  have hR0 : 0 ≤ 2 * ((redR l u + redK l u : ℕ) : ℝ) := by positivity
  have hRK2 : 2 * ((redR l u + redK l u : ℕ) : ℝ) ≤ 10 * (a₆ * u ^ 3) := by
    have := redRK_le (l := l) hu1
    rw [show u ^ (8 * l + 9) = a₆ * u ^ 3 by rw [ha₆, ← pow_add]] at this
    linarith
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · subst hl0; simp
  obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hlk : l - 1 = k := by omega
  rw [hlk]
  have s1 : (2 / (redK l u : ℝ)) ^ l ≤ (4 / a₆) ^ l := pow_le_pow_left₀ (by positivity) h2K _
  have s2 : (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ k ≤ (10 * (a₆ * u ^ 3)) ^ k :=
    pow_le_pow_left₀ hR0 hRK2 _
  have ha₆0 : a₆ ≠ 0 := ne_of_gt (by linarith)
  have s3 : (4 / a₆) ^ l * (10 * (a₆ * u ^ 3)) ^ k = 4 ^ l * 10 ^ k * u ^ (3 * k) / a₆ := by
    rw [hk, pow_mul, div_pow, mul_pow, mul_pow, pow_succ a₆]
    field_simp
  have s4 : u ^ (3 * k) * u ^ 2 ≤ a₆ := by
    rw [ha₆, ← pow_add]; exact pow_le_pow_right₀ hu1 (by omega)
  have s5 : (4 : ℝ) ^ l * 10 ^ k ≤ 40 ^ l := by
    rw [show (40 : ℝ) ^ l = 4 ^ l * 10 ^ l by rw [← mul_pow]; norm_num]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  calc (2 / (redK l u : ℝ)) ^ l * (2 * l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ k)
      = 2 * l * ((2 / (redK l u : ℝ)) ^ l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ k) := by
        ring
    _ ≤ 2 * l * ((4 / a₆) ^ l * (10 * (a₆ * u ^ 3)) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul s1 s2 (by positivity) (by positivity)
    _ = 2 * l * (4 ^ l * 10 ^ k * u ^ (3 * k) / a₆) := by rw [s3]
    _ ≤ 2 * l * (40 ^ l / u ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by linarith) hu2]
        calc 4 ^ l * 10 ^ k * u ^ (3 * k) * u ^ 2 = 4 ^ l * 10 ^ k * (u ^ (3 * k) * u ^ 2) := by
              ring
          _ ≤ 40 ^ l * a₆ := mul_le_mul s5 s4 (by positivity) (by positivity)
    _ = 2 * l * 40 ^ l / u ^ 2 := by ring

/-- The comparison term: `(2/K)^l (2(R+K))^l e ≤ 40^l (C_b + 2) u^{-2}` for
`e ≤ (C_b + 2) u^{-(8l+8)}`. -/
private lemma red_comp_arith {e Cb : ℝ} (hu : 4 ≤ u) (he0 : 0 ≤ e) (hCb : 0 ≤ Cb)
    (he : e ≤ (Cb + 2) / u ^ (8 * l + 8)) :
    (2 / (redK l u : ℝ)) ^ l * ((2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l * e) ≤
      40 ^ l * (Cb + 2) / u ^ 2 := by
  have hu1 : 1 ≤ u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  set a₆ := u ^ (8 * l + 6) with ha₆
  have ha₆4 : 4 ≤ a₆ := le_trans hu (le_self_pow₀ hu1 (by omega))
  have ha₈0 : 0 < u ^ (8 * l + 8) := by positivity
  have hK0 : (0 : ℝ) < redK l u := by have := redK_ge (l := l) hu; linarith
  have h2K : 2 / (redK l u : ℝ) ≤ 4 / a₆ := by
    rw [div_le_div_iff₀ hK0 (by linarith)]; have := redK_ge (l := l) hu; linarith
  have hR0 : 0 ≤ 2 * ((redR l u + redK l u : ℕ) : ℝ) := by positivity
  have hRK2 : 2 * ((redR l u + redK l u : ℕ) : ℝ) ≤ 10 * (a₆ * u ^ 3) := by
    have := redRK_le (l := l) hu1
    rw [show u ^ (8 * l + 9) = a₆ * u ^ 3 by rw [ha₆, ← pow_add]] at this
    linarith
  have s1 : (2 / (redK l u : ℝ)) ^ l ≤ (4 / a₆) ^ l := pow_le_pow_left₀ (by positivity) h2K _
  have s2 : (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l ≤ (10 * (a₆ * u ^ 3)) ^ l :=
    pow_le_pow_left₀ hR0 hRK2 _
  have s3 : (4 / a₆) ^ l * (10 * (a₆ * u ^ 3)) ^ l = 40 ^ l * u ^ (3 * l) := by
    have ha₆0 : a₆ ≠ 0 := ne_of_gt (by linarith)
    rw [← mul_pow, pow_mul]
    field_simp
    ring
  have s4 : u ^ (3 * l) * u ^ 2 ≤ u ^ (8 * l + 8) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hu1 (by omega)
  calc (2 / (redK l u : ℝ)) ^ l * ((2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l * e)
      = ((2 / (redK l u : ℝ)) ^ l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l) * e := by ring
    _ ≤ ((4 / a₆) ^ l * (10 * (a₆ * u ^ 3)) ^ l) * ((Cb + 2) / u ^ (8 * l + 8)) :=
        mul_le_mul (mul_le_mul s1 s2 (by positivity) (by positivity)) he he0 (by positivity)
    _ = 40 ^ l * (Cb + 2) * (u ^ (3 * l) / u ^ (8 * l + 8)) := by rw [s3]; ring
    _ ≤ 40 ^ l * (Cb + 2) * (1 / u ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ ha₈0 hu2]; linarith
    _ = 40 ^ l * (Cb + 2) / u ^ 2 := by ring

/-- The final bookkeeping of the reduction. -/
private lemma red_final {B Cb q p : ℝ} {L : ℝ≥0} (hu : 4 ≤ u) (hϖm : 0 < ϖm) (hB0 : 0 ≤ B)
    (hCb0 : 0 ≤ Cb) (hq0 : 0 ≤ q) (hq : q ≤ 1 / u ^ (8 * l + 8)) (hp0 : 0 ≤ p)
    (hp : p ≤ 1 / u ^ (8 * l + 8)) (hpu : p ≤ 1 / u ^ 2) :
    2 * ((L : ℝ) * (redδ l u ϖm * redK l u) + 2 * B * p) +
        B * (2 / (redK l u : ℝ)) ^ l * (2 * l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ (l - 1) +
          (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l * (Cb * q + 2 * p)) ≤
      (4 / ϖm + 4 + 2 * l * 40 ^ l + 40 ^ l * (Cb + 2)) * (B + L) * (1 / u ^ 2) := by
  have hu1 : 1 ≤ u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  have hδK : redδ l u ϖm * redK l u ≤ 2 / ϖm / u ^ 2 := by
    calc redδ l u ϖm * redK l u ≤ redδ l u ϖm * u ^ (8 * l + 6) :=
          mul_le_mul_of_nonneg_left (redK_le hu1) (by unfold redδ; positivity)
      _ = 2 / ϖm / u ^ 2 := by
          unfold redδ; rw [show 8 * l + 8 = (8 * l + 6) + 2 by ring, pow_add]; field_simp
  have he : Cb * q + 2 * p ≤ (Cb + 2) / u ^ (8 * l + 8) := by
    calc Cb * q + 2 * p ≤ Cb * (1 / u ^ (8 * l + 8)) + 2 * (1 / u ^ (8 * l + 8)) :=
          add_le_add (mul_le_mul_of_nonneg_left hq hCb0) (by linarith)
      _ = (Cb + 2) / u ^ (8 * l + 8) := by ring
  have hsh := red_shell_arith (l := l) hu
  have hco := red_comp_arith (l := l) hu (by positivity) hCb0 he
  have hL0 : (0 : ℝ) ≤ L := L.2
  have t1 : 2 * ((L : ℝ) * (redδ l u ϖm * redK l u) + 2 * B * p) ≤
      (4 / ϖm) * L / u ^ 2 + 4 * B / u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hδK hL0
    have := mul_le_mul_of_nonneg_left hpu (by positivity : (0 : ℝ) ≤ 2 * B)
    have e : (4 / ϖm) * L / u ^ 2 + 4 * B / u ^ 2 =
        2 * ((L : ℝ) * (2 / ϖm / u ^ 2) + 2 * B * (1 / u ^ 2)) := by ring
    rw [e]; linarith
  have t2 : B * (2 / (redK l u : ℝ)) ^ l *
      (2 * l * (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ (l - 1) +
        (2 * ((redR l u + redK l u : ℕ) : ℝ)) ^ l * (Cb * q + 2 * p)) ≤
      B * (2 * l * 40 ^ l / u ^ 2 + 40 ^ l * (Cb + 2) / u ^ 2) := by
    rw [mul_assoc, mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_add hsh hco) hB0
  have fin : (4 / ϖm) * L / u ^ 2 + 4 * B / u ^ 2 +
      B * (2 * l * 40 ^ l / u ^ 2 + 40 ^ l * (Cb + 2) / u ^ 2) ≤
      (4 / ϖm + 4 + 2 * l * 40 ^ l + 40 ^ l * (Cb + 2)) * (B + L) * (1 / u ^ 2) := by
    rw [show (4 / ϖm) * L / u ^ 2 + 4 * B / u ^ 2 +
        B * (2 * l * 40 ^ l / u ^ 2 + 40 ^ l * (Cb + 2) / u ^ 2) =
        ((4 / ϖm) * L + B * (4 + 2 * l * 40 ^ l + 40 ^ l * (Cb + 2))) * (1 / u ^ 2) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h4 : 0 ≤ 4 / ϖm := by positivity
    have h40 : (0 : ℝ) ≤ 2 * l * 40 ^ l + 40 ^ l * (Cb + 2) := by positivity
    nlinarith
  linarith

end RedParam

/-- The powers of `N` that enter the reduction, in terms of `u = N^β`, `β = ε/(8(l+1))`. -/
private lemma red_rpow_facts {l : ℕ} {ε c₁ x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    (hc₁ : ε ≤ c₁) (hx1 : 1 ≤ x) :
    x ^ (-2 / 3 + ε) = (x ^ (ε / (8 * (l + 1)))) ^ (8 * l + 8) / x ^ (2 / 3 : ℝ) ∧
    x ^ (-2 / 3 - ε) = 1 / ((x ^ (ε / (8 * (l + 1)))) ^ (8 * l + 8) * x ^ (2 / 3 : ℝ)) ∧
    x ^ (-(ε / (4 * (l + 1)))) = 1 / (x ^ (ε / (8 * (l + 1)))) ^ 2 ∧
    x ^ (-5 * ε) ≤ 1 / (x ^ (ε / (8 * (l + 1)))) ^ (8 * l + 8) ∧
    x ^ (-c₁) ≤ 1 / (x ^ (ε / (8 * (l + 1)))) ^ (8 * l + 8) ∧
    x ^ (-(1 : ℝ)) ≤ 1 / (x ^ (ε / (8 * (l + 1)))) ^ (8 * l + 8) ∧
    x ^ (-(1 : ℝ)) ≤ 1 / (x ^ (ε / (8 * (l + 1)))) ^ 2 ∧
    x ^ (2 / 3 : ℝ) * x ^ (-2 / 3 + ε / (8 * (l + 1))) = x ^ (ε / (8 * (l + 1))) := by
  have hx0 : 0 < x := by linarith
  set β : ℝ := ε / (8 * (l + 1)) with hβ_def
  have hl1 : (0 : ℝ) < l + 1 := by positivity
  have hβ : 0 < β := by positivity
  have hεβ : ε = β * ((8 * l + 8 : ℕ) : ℝ) := by rw [hβ_def]; push_cast; field_simp
  have hrate : ε / (4 * (l + 1)) = β * ((2 : ℕ) : ℝ) := by
    rw [hβ_def]; push_cast; field_simp; ring
  have hβ1 : β * 2 ≤ 1 := by
    rw [hβ_def, div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
  have hpow : ∀ k : ℕ, x ^ (β * (k : ℝ)) = (x ^ β) ^ k := fun k => by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
  have hxε : x ^ ε = (x ^ β) ^ (8 * l + 8) := by rw [hεβ, hpow]
  have hxnε : x ^ (-ε) = 1 / (x ^ β) ^ (8 * l + 8) := by
    rw [Real.rpow_neg hx0.le, hxε, one_div]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [red_rpow_split hx0, hxε]
  · rw [show (-2 / 3 - ε : ℝ) = -2 / 3 + -ε by ring, red_rpow_split hx0, hxnε]
    field_simp
  · rw [Real.rpow_neg hx0.le, hrate, hpow, one_div]
  · rw [← hxnε]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [← hxnε]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [← hxnε]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [← Nat.cast_ofNat, ← hpow, one_div, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  · rw [← Real.rpow_add hx0]; congr 1; ring

/-- The reduction: the edge regime for both ensembles (with probability `≥ 1 - N^{-1}`) and the
comparison of smooth functionals of `𝒳` give the comparison of `E h(q)` for bounded Lipschitz
`h`, at the rate `N^{-ε/(4(l+1))}`. -/
theorem edge_reduction (l : ℕ) (ε c₁ ϖm ϖp C₀ r₀ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    (hc₁ : ε ≤ c₁) (hϖm : 0 < ϖm) (hϖ : ϖm ≤ ϖp) (hC₀ : 0 < C₀) (hr₀ : 0 < r₀) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n d : ℕ) (a ϖ : ℝ), (n : ℝ) ≤ C₀ * N →
      ϖ ∈ Set.Icc ϖm ϖp →
      ∀ {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
        {Ω₀ : Type} [MeasureSpace Ω₀] [IsProbabilityMeasure (ℙ : Measure Ω₀)]
        (A₁ : Ω₁ → Matrix (Fin n) (Fin n) ℝ) (A₀ : Ω₀ → Matrix (Fin n) (Fin n) ℝ),
        Measurable A₁ → Measurable A₀ → (∀ ω, (A₁ ω).IsHermitian) →
        (∀ ω, (A₀ ω).IsHermitian) →
        HighProbAt N 1 {ω | EdgeRegime N a d l (ε / (8 * (l + 1))) r₀ C₀ (A₁ ω)} →
        HighProbAt N 1 {ω | EdgeRegime N a d l (ε / (8 * (l + 1))) r₀ C₀ (A₀ ω)} →
        SmoothComparable N a ε c₁ l A₁ A₀ →
        ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
          |(∫ ω, h (edgeQ N a ϖ d l (A₁ ω))) - (∫ ω, h (edgeQ N a ϖ d l (A₀ ω)))| ≤
            K * (B + L) * (N : ℝ) ^ (-(ε / (4 * (l + 1)))) := by
  have hβ : 0 < ε / (8 * ((l : ℝ) + 1)) := by positivity
  obtain ⟨N₁, hN₁⟩ := smCount_bracket l ε C₀ r₀ hε hε1 hC₀ hr₀
  obtain ⟨_, Cb, hCb⟩ := redF_smooth l
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0 (by norm_num) 0)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (40 * ϖp / ϖm + 4))
  refine ⟨4 / ϖm + 4 + 2 * l * 40 ^ l + 40 ^ l * (Cb + 2), max (max N₁ N₂) 1, ?_⟩
  intro N hN n d a ϖ hn hϖI Ω₁ _ _ Ω₀ _ _ A₁ A₀ hA₁ hA₀ hH₁ hH₀ hG₁ hG₀ hSC h B L hB hL
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨hϖ1, hϖ2⟩ := hϖI
  have hϖ0 : 0 < ϖ := lt_of_lt_of_le hϖm hϖ1
  obtain ⟨hL1, hℓ, hxu2, h5, hc1b, hpa, hpu, hqe⟩ :=
    red_rpow_facts (l := l) (c₁ := c₁) hε hε1 hc₁ hx1
  set u : ℝ := (N : ℝ) ^ (ε / (8 * ((l : ℝ) + 1))) with hu_def
  have hu : 40 * ϖp / ϖm + 4 ≤ u := hN₂ N hNN₂
  have hu4 : 4 ≤ u := by
    have : 0 ≤ 40 * ϖp / ϖm := by
      have : 0 < ϖp := lt_of_lt_of_le hϖm hϖ
      positivity
    linarith
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  set w : ℝ := (N : ℝ) ^ (2 / 3 : ℝ) with hw_def
  have hw : 0 < w := by positivity
  have ha₈1 : 1 ≤ u ^ (8 * l + 8) := one_le_pow₀ hu1
  have h5' : (N : ℝ) ^ (-5 * ε) ≤ 1 / 3 := by
    refine h5.trans ?_
    have : 3 ≤ u ^ (8 * l + 8) := le_trans (by linarith) (le_self_pow₀ hu1 (by omega))
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set δ := redδ l u ϖm with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; unfold redδ; positivity
  set K := redK l u with hK_def
  have hK1 : 1 ≤ K := one_le_redK hu4
  set R := redR l u with hR_def
  set p : ℝ := (N : ℝ) ^ (-(1 : ℝ)) with hp_def
  have hp0 : 0 ≤ p := by positivity
  -- the exceptional sets
  set T₁ := toMeasurable (ℙ : Measure Ω₁)
    {ω | EdgeRegime N a d l (ε / (8 * ((l : ℝ) + 1))) r₀ C₀ (A₁ ω)}ᶜ with hT₁
  set T₀ := toMeasurable (ℙ : Measure Ω₀)
    {ω | EdgeRegime N a d l (ε / (8 * ((l : ℝ) + 1))) r₀ C₀ (A₀ ω)}ᶜ with hT₀
  have hp₁ : (ℙ T₁).toReal ≤ p := by
    rw [hT₁, measure_toMeasurable]; exact ENNReal.toReal_le_of_le_ofReal hp0 hG₁
  have hp₀ : (ℙ T₀).toReal ≤ p := by
    rw [hT₀, measure_toMeasurable]; exact ENNReal.toReal_le_of_le_ofReal hp0 hG₀
  have hreg₁ : ∀ ω ∉ T₁, EdgeRegime N a d l (ε / (8 * ((l : ℝ) + 1))) r₀ C₀ (A₁ ω) :=
    fun ω hω => by
      by_contra hc; exact hω (subset_toMeasurable _ _ (show ω ∈ {ω | _}ᶜ from hc))
  have hreg₀ : ∀ ω ∉ T₀, EdgeRegime N a d l (ε / (8 * ((l : ℝ) + 1))) r₀ C₀ (A₀ ω) :=
    fun ω hω => by
      by_contra hc; exact hω (subset_toMeasurable _ _ (show ω ∈ {ω | _}ᶜ from hc))
  have hqb : ∀ {Ω : Type} {A : Ω → Matrix (Fin n) (Fin n) ℝ} {T : Set Ω},
      (∀ ω, (A ω).IsHermitian) →
      (∀ ω ∉ T, EdgeRegime N a d l (ε / (8 * ((l : ℝ) + 1))) r₀ C₀ (A ω)) →
      ∀ ω ∉ T, ∀ j, |edgeQ N a ϖ d l (A ω) j| ≤ δ * ((R : ℝ) - K - 1) := by
    intro Ω A T hH hG ω hω j
    refine (red_q_abs_le hϖ0 (hH ω) (hG ω hω) j).trans ?_
    rw [div_mul_eq_mul_div, hqe]
    exact le_trans (div_le_div_of_nonneg_left hu0.le hϖm hϖ1) (redR_inner hu1 hϖm)
  have hshift : 2 * ellE N ε ≤ δ * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) := by
    have e : δ * ϖ / (N : ℝ) ^ (2 / 3 : ℝ) = 2 / (u ^ (8 * l + 8) * w) * (ϖ / ϖm) := by
      rw [hδ_def, ← hw_def]; unfold redδ; field_simp
    unfold ellE
    rw [hℓ, e]
    have h1 : 1 ≤ ϖ / ϖm := (one_le_div hϖm).2 hϖ1
    have h2 : 0 ≤ 2 / (u ^ (8 * l + 8) * w) := by positivity
    calc 2 * (1 / (u ^ (8 * l + 8) * w)) = 2 / (u ^ (8 * l + 8) * w) * 1 := by ring
      _ ≤ 2 / (u ^ (8 * l + 8) * w) * (ϖ / ϖm) := mul_le_mul_of_nonneg_left h1 h2
  have hcmp : ∀ m ∈ redBox l (R + K),
      |(∫ ω, redInd (fun i => δ * m i) (edgeQ N a ϖ d l (A₁ ω))) -
          ∫ ω, redInd (fun i => δ * m i) (edgeQ N a ϖ d l (A₀ ω))| ≤
        ((∫ ω, redInd (fun i => δ * m i - δ) (edgeQ N a ϖ d l (A₀ ω))) -
          ∫ ω, redInd (fun i => δ * m i + δ) (edgeQ N a ϖ d l (A₀ ω))) +
          (Cb * (N : ℝ) ^ (-c₁) + 2 * p) := by
    intro m hm
    have hmi : ∀ i, |(m i : ℝ)| ≤ ((R + K : ℕ) : ℝ) := by
      intro i
      have := Fintype.mem_piFinset.1 hm i
      rw [Finset.mem_Ico] at this
      rw [abs_le]; constructor
      · have : (-((R + K : ℕ) : ℤ) : ℝ) ≤ (m i : ℝ) := by exact_mod_cast this.1
        push_cast at this ⊢; linarith
      · have : (m i : ℝ) < ((R + K : ℕ) : ℤ) := by exact_mod_cast this.2
        push_cast at this ⊢; linarith
    refine red_point_compare hA₁ hA₀ hH₁ hH₀ (measurableSet_toMeasurable _ _)
      (measurableSet_toMeasurable _ _) hp₁ hp₀ hreg₁ hreg₀
      (fun A hA hreg E hE => hN₁ N hNN₁ n d a A hA hn hreg E hE) hϖ0 hw h5' hshift hSC hCb
      (fun i => δ * m i) fun i => ?_
    unfold ellE
    rw [hℓ, hL1]
    exact red_window hϖm hϖ1 hϖ2 hu hw (hmi i)
  have hmain := red_compare hB hL hδ0 hK1 R (p := p) (e := Cb * (N : ℝ) ^ (-c₁) + 2 * p)
    (red_measurable_edgeQ hA₁ N a ϖ d l) (red_measurable_edgeQ hA₀ N a ϖ d l)
    (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _) hp₁ hp₀
    (hqb hH₁ hreg₁) (hqb hH₀ hreg₀) hcmp
  refine hmain.trans ?_
  rw [hxu2]
  exact red_final hu4 hϖm hB0 hCb0 (by positivity) hc1b hp0 hpa hpu

/-- Bounded uniformly continuous functions are uniform limits of bounded Lipschitz functions
(inf-convolution `h_L(x) = inf_y (h(y) + L |x - y|)`). -/
theorem exists_lipschitz_approx {l : ℕ} {h : (Fin l → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (hu : UniformContinuous h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (g : (Fin l → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L g ∧ (∀ x, |g x| ≤ B) ∧
      ∀ x, |h x - g x| ≤ δ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨r, hr, hr'⟩ := Metric.uniformContinuous_iff.1 hu δ hδ
  set L : ℝ≥0 := ⟨2 * B / r, by positivity⟩ with hL
  have hLr : (L : ℝ) * r = 2 * B := by
    change (2 * B / r) * r = 2 * B; field_simp
  have hbdd : ∀ x, BddBelow (Set.range fun y => h y + L * dist x y) := fun x => by
    refine ⟨-B, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := (abs_le.1 (hB y)).1
    have h2 : 0 ≤ (L : ℝ) * dist x y := mul_nonneg L.2 dist_nonneg
    linarith
  set g : (Fin l → ℝ) → ℝ := fun x => ⨅ y, h y + L * dist x y with hg
  have hle : ∀ x y, g x ≤ h y + L * dist x y := fun x y => ciInf_le (hbdd x) y
  have hge : ∀ x, -B ≤ g x := fun x => le_ciInf fun y => by
    have h1 := (abs_le.1 (hB y)).1
    have h2 : 0 ≤ (L : ℝ) * dist x y := mul_nonneg L.2 dist_nonneg
    linarith
  have hgh : ∀ x, g x ≤ h x := fun x => by simpa using hle x x
  refine ⟨g, L, ?_, ?_, ?_⟩
  · refine LipschitzWith.of_le_add_mul L fun x y => ?_
    have : g x - L * dist x y ≤ g y := le_ciInf fun z => by
      have h1 := hle x z
      have h2 := dist_triangle x y z
      have h3 : (L : ℝ) * dist x z ≤ L * dist x y + L * dist y z := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg L)
      linarith
    linarith
  · intro x
    rw [abs_le]
    exact ⟨hge x, (hgh x).trans (abs_le.1 (hB x)).2⟩
  · intro x
    rw [abs_of_nonneg (by linarith [hgh x])]
    have : h x - δ ≤ g x := le_ciInf fun y => by
      by_cases hxy : dist x y < r
      · have := hr' hxy
        rw [Real.dist_eq, abs_lt] at this
        have h2 : 0 ≤ (L : ℝ) * dist x y := mul_nonneg L.2 dist_nonneg
        linarith
      · have h1 : (L : ℝ) * r ≤ L * dist x y := mul_le_mul_of_nonneg_left (not_lt.1 hxy) L.2
        have h2 := (abs_le.1 (hB x)).2
        have h3 := (abs_le.1 (hB y)).1
        linarith
    linarith

/-! ### Instances -/

/-- The approximation at `h(x) = sin x₀` (bounded by `1`, uniformly continuous), `δ = 1/10`. -/
example : ∃ (g : (Fin 1 → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L g ∧ (∀ x, |g x| ≤ 1) ∧
    ∀ x, |Real.sin (x 0) - g x| ≤ 1 / 10 :=
  exists_lipschitz_approx (h := fun x : Fin 1 → ℝ => Real.sin (x 0))
    (fun x => Real.abs_sin_le_one _)
    ((Real.lipschitzWith_sin.comp
      (LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0)).uniformContinuous)
    (by norm_num)

end Anisotropic
