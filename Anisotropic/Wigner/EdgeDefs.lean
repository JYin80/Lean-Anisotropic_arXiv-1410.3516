import Anisotropic.Framework.Domination
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Exclusion
import Anisotropic.Wigner.SelfConsistent
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The extreme edges `L±` of `ϱ^W` through `g(x) = x − m_A(x)`, Definition 12.3 (rigid extremes), and the partial-fraction identity (tur1) -/

/-- `S(x) = N⁻¹ ∑ᵢ (aᵢ − x)⁻²` on the real axis. -/
def sW {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹

/-- `g(x) = x − m_A(x)` with `m_A(x) = N⁻¹ ∑ᵢ (aᵢ − x)⁻¹`, on the real axis; `z = g(z + m^W(z))`
is the self-consistent equation of §12.1. -/
def gW {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ := x - (N : ℝ)⁻¹ * ∑ i, (a i - x)⁻¹

/-- The critical point `x₊ > maxᵢ aᵢ` of `g`: the least `x > maxᵢ aᵢ` with `S(x) ≤ 1`. -/
def xpW {N : ℕ} (a : Fin N → ℝ) : ℝ := sInf {x | (⨆ i, a i) < x ∧ sW a x ≤ 1}

/-- The critical point `x₋ < minᵢ aᵢ` of `g`: the greatest `x < minᵢ aᵢ` with `S(x) ≤ 1`. -/
def xmW {N : ℕ} (a : Fin N → ℝ) : ℝ := sSup {x | x < (⨅ i, a i) ∧ sW a x ≤ 1}

/-- The right edge `L₊ = g(x₊)` of `ϱ^W` (§12.1, Definition 12.3). -/
def LpW {N : ℕ} (a : Fin N → ℝ) : ℝ := gW a (xpW a)

/-- The left edge `L₋ = g(x₋)` of `ϱ^W` (§12.1, Definition 12.3). -/
def LmW {N : ℕ} (a : Fin N → ℝ) : ℝ := gW a (xmW a)

/-- `κ(E) = dist(E, [L₋, L₊])` (§12.4). -/
def kappaW {N : ℕ} (a : Fin N → ℝ) (E : ℝ) : ℝ := max (max (E - LpW a) (LmW a - E)) 0

/-- The domain `𝐒_τ` of the proof of Theorem 12.4 (§12.4), with `δ = τ_S`:
`N^{−2/3+τ_S} ≤ κ(E) ≤ τ_S⁻¹` and `N^{−τ_S} κ(E) ≤ η ≤ N^{−τ_S/2} κ(E)`. -/
def outDomW {N : ℕ} (τS : ℝ) (a : Fin N → ℝ) : Set ℂ :=
  {z | (N : ℝ) ^ (-2 / 3 + τS) ≤ kappaW a z.re ∧ kappaW a z.re ≤ τS⁻¹ ∧
    (N : ℝ) ^ (-τS) * kappaW a z.re ≤ z.im ∧ z.im ≤ (N : ℝ) ^ (-τS / 2) * kappaW a z.re}

section Rigid

variable {Ω : Type*} [MeasureSpace Ω]

/-- `[λ₁(H) − Lp]₊ ≺ N^{−2/3}` and `[λ_N(H) − Lm]₋ ≺ N^{−2/3}` at fixed `N, ε, D`. -/
def RigidExtremesAt (N : ℕ) (ε D Lm Lp : ℝ) (H : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  DomAt N ε D (fun ω => max (sortedEig (H ω) 1 - Lp) 0) (fun _ => (N : ℝ) ^ (-2 / 3 : ℝ)) ∧
    DomAt N ε D (fun ω => max (Lm - sortedEig (H ω) N) 0) (fun _ => (N : ℝ) ^ (-2 / 3 : ℝ))

/-- Definition 12.3 at fixed `N, ε, D`: the extreme eigenvalues of `H` are rigid with respect to
the edges `L±` of the density `ϱ^W` of the spectrum `a`. -/
def RigidExtremesWAt (N : ℕ) (ε D : ℝ) (a : Fin N → ℝ) (H : Ω → Matrix (Fin N) (Fin N) ℝ) :
    Prop :=
  RigidExtremesAt N ε D (LmW a) (LpW a) H

end Rigid

/-- `S` does not depend on the order of the spectrum. -/
theorem sW_comp_perm {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (x : ℝ) :
    sW (a ∘ e) x = sW a x := by
  unfold sW
  congr 1
  exact Equiv.sum_comp e (fun i => ((a i - x) ^ 2)⁻¹)

/-- `g` does not depend on the order of the spectrum. -/
theorem gW_comp_perm {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (x : ℝ) :
    gW (a ∘ e) x = gW a x := by
  unfold gW
  congr 2
  exact Equiv.sum_comp e (fun i => (a i - x)⁻¹)

private lemma aux_iSup_comp {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    (⨆ i, (a ∘ e) i) = ⨆ i, a i := by
  show sSup (Set.range (a ∘ e)) = sSup (Set.range a)
  rw [EquivLike.range_comp]

private lemma aux_iInf_comp {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    (⨅ i, (a ∘ e) i) = ⨅ i, a i := by
  show sInf (Set.range (a ∘ e)) = sInf (Set.range a)
  rw [EquivLike.range_comp]

/-- `L₊` depends only on the spectrum of `A`. -/
theorem LpW_comp_perm {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    LpW (a ∘ e) = LpW a := by
  unfold LpW xpW
  simp only [sW_comp_perm, gW_comp_perm, aux_iSup_comp]

/-- `L₋` depends only on the spectrum of `A`. -/
theorem LmW_comp_perm {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    LmW (a ∘ e) = LmW a := by
  unfold LmW xmW
  simp only [sW_comp_perm, gW_comp_perm, aux_iInf_comp]

private lemma aux_stieltjesA_neg {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    stieltjesA (-a) (-(starRingEnd ℂ) w) = -(starRingEnd ℂ) (stieltjesA a w) := by
  unfold stieltjesA
  rw [map_mul, map_inv₀, map_sum, Complex.conj_natCast, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 2
  ext i
  rw [map_inv₀, map_sub, Complex.conj_ofReal, ← inv_neg]
  congr 1
  simp only [Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- Reflection: `m^W_{−a}(−z̄) = −conj m^W_a(z)`. -/
theorem mW_neg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    mW (-a) (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (mW a z) := by
  obtain ⟨hpos, heq⟩ := mW_spec hN a hz
  apply mW_eq_of_spec hN (-a)
  · simpa using hz
  · simpa using hpos
  · have h1 : -(starRingEnd ℂ) z + -(starRingEnd ℂ) (mW a z)
        = -(starRingEnd ℂ) (z + mW a z) := by
      rw [map_add]; ring
    rw [h1, aux_stieltjesA_neg, ← heq]

private lemma aux_sW_neg {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : sW (-a) x = sW a (-x) := by
  unfold sW
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Pi.neg_apply]
  ring

private lemma aux_gW_neg {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : gW (-a) x = -gW a (-x) := by
  unfold gW
  have : ∀ i, ((-a) i - x)⁻¹ = -(a i - -x)⁻¹ := fun i => by
    rw [← inv_neg]
    congr 1
    simp only [Pi.neg_apply]
    ring
  simp only [this, Finset.sum_neg_distrib]
  ring

private lemma aux_range_neg {N : ℕ} (a : Fin N → ℝ) : Set.range (-a) = -Set.range a := by
  ext x
  simp only [Set.mem_range, Set.mem_neg, Pi.neg_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by linarith⟩

private lemma aux_iSup_neg {N : ℕ} (a : Fin N → ℝ) : (⨆ i, (-a) i) = -⨅ i, a i := by
  show sSup (Set.range (-a)) = -sInf (Set.range a)
  rw [aux_range_neg, Real.sSup_neg]

private lemma aux_xpW_neg {N : ℕ} (a : Fin N → ℝ) : xpW (-a) = -xmW a := by
  unfold xpW xmW
  have : {x : ℝ | (⨆ i, (-a) i) < x ∧ sW (-a) x ≤ 1} =
      -{y : ℝ | y < (⨅ i, a i) ∧ sW a y ≤ 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_neg, aux_iSup_neg, aux_sW_neg]
    rw [neg_lt]
  rw [this, Real.sInf_neg]

/-- Reflection: `L₋(a) = −L₊(−a)`. -/
theorem LmW_neg {N : ℕ} (a : Fin N → ℝ) : LmW a = -LpW (-a) := by
  unfold LmW LpW
  rw [aux_xpW_neg, aux_gW_neg, neg_neg, neg_neg]

/-- The constants `C_{n,k} = k^{−1/2} (−1)^{k−1} / ((k−1)! (n−k)!)` of (tur1). -/
def turC (n k : ℕ) : ℝ :=
  (k : ℝ) ^ (-(1 / 2 : ℝ)) * (-1) ^ (k - 1) / ((Nat.factorial (k - 1) : ℝ) * Nat.factorial (n - k))

private lemma aux_prod_erase (m r : ℕ) :
    ∏ j ∈ (Finset.Icc 1 (m + 1 + r)).erase (m + 1), ((j : ℝ) - ((m + 1 : ℕ) : ℝ)) =
      (-1) ^ m * (Nat.factorial m : ℝ) * (Nat.factorial r : ℝ) := by
  induction r with
  | zero =>
    have h1 : (Finset.Icc 1 (m + 1 + 0)).erase (m + 1) = Finset.Icc 1 m := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_sub_cancel]
    have h2 : ∀ j ∈ Finset.range m, ((1 + j : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) =
        -1 * (((m - 1 - j : ℕ) : ℝ) + 1) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have : ((m - 1 - j : ℕ) : ℝ) = (m : ℝ) - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [this]
      push_cast
      ring
    rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    rw [Finset.prod_range_reflect (fun j : ℕ => ((j : ℝ) + 1)) m]
    have : ∏ j ∈ Finset.range m, ((j : ℝ) + 1) = (Nat.factorial m : ℝ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rfl
    rw [this]
  | succ r ih =>
    have h1 : (Finset.Icc 1 (m + 1 + (r + 1))).erase (m + 1) =
        insert (m + 1 + (r + 1)) ((Finset.Icc 1 (m + 1 + r)).erase (m + 1)) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h1, Finset.prod_insert (by simp), ih, Nat.factorial_succ]
    push_cast
    ring

private lemma aux_pf {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 ≤ y) :
    ∏ k ∈ Finset.Icc 1 n, (y + k * c)⁻¹ =
      ∑ k ∈ Finset.Icc 1 n,
        (c ^ (n - 1) * ((-1) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) *
          (Nat.factorial (n - k) : ℝ)))⁻¹ * (y + k * c)⁻¹ := by
  have hs : (Finset.Icc 1 n).Nonempty := Finset.nonempty_Icc.2 hn
  have hinj : Set.InjOn (fun k : ℕ => -((k : ℝ) * c)) (Finset.Icc 1 n : Set ℕ) := by
    intro a _ b _ h
    have : (a : ℝ) * c = b * c := by simpa using h
    exact_mod_cast mul_right_cancel₀ hc.ne' this
  have h := congrArg (Polynomial.eval y) (Lagrange.sum_basis hinj hs)
  simp only [Polynomial.eval_finsetSum, Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one] at h
  have hpos : ∀ k ∈ Finset.Icc 1 n, 0 < y + (k : ℝ) * c := by
    intro k hk
    have : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    positivity
  have hP : ∏ k ∈ Finset.Icc 1 n, (y + (k : ℝ) * c) ≠ 0 :=
    (Finset.prod_pos hpos).ne'
  rw [Finset.prod_inv_distrib]
  refine mul_right_cancel₀ hP ?_
  rw [inv_mul_cancel₀ hP, Finset.sum_mul]
  refine Eq.trans h.symm (Finset.sum_congr rfl ?_)
  intro k hk
  have hkn := Finset.mem_Icc.1 hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, n = m + 1 + r := ⟨n - (m + 1), by omega⟩
  have hQ : (y + ((m + 1 : ℕ) : ℝ) * c) * ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y + (j : ℝ) * c)
      = ∏ j ∈ Finset.Icc 1 n, (y + (j : ℝ) * c) :=
    Finset.mul_prod_erase _ (fun j : ℕ => y + (j : ℝ) * c) hk
  have hk0 : y + ((m + 1 : ℕ) : ℝ) * c ≠ 0 := (hpos _ hk).ne'
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hQ]
  have hD : ∏ j ∈ (Finset.Icc 1 n).erase (m + 1),
      (-(((m + 1 : ℕ) : ℝ) * c) - -((j : ℝ) * c)) =
      c ^ (n - 1) * ((-1) ^ m * (Nat.factorial m : ℝ) * (Nat.factorial (n - (m + 1)) : ℝ)) := by
    have : ∀ j ∈ (Finset.Icc 1 n).erase (m + 1),
        (-(((m + 1 : ℕ) : ℝ) * c) - -((j : ℝ) * c)) = ((j : ℝ) - ((m + 1 : ℕ) : ℝ)) * c :=
      fun j _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem hk, Nat.card_Icc, Nat.add_sub_cancel, hr, aux_prod_erase m r]
    have : m + 1 + r - (m + 1) = r := by omega
    rw [this, mul_comm]
  have hY : ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y - -((j : ℝ) * c)) =
      ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y + (j : ℝ) * c) :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [hD, hY]
  simp only [Nat.add_sub_cancel]
  field_simp
  exact Finset.prod_congr rfl fun j _ => by ring

/-- (tur1), §10: `K⁻¹ ∑ⱼ ∏ₖ ((λⱼ − E)² + kη²)⁻¹ = ∑ₖ C_{n,k} η^{−2n+1} Im s(E + i√k η)` for the
Stieltjes transform `s` of the empirical measure of `λ`. -/
theorem tur1 {K : ℕ} (n : ℕ) (hn : 1 ≤ n) (lam : Fin K → ℝ) (E η : ℝ) (hη : 0 < η) :
    (K : ℝ)⁻¹ * ∑ j, ∏ k ∈ Finset.Icc 1 n, ((lam j - E) ^ 2 + k * η ^ 2)⁻¹ =
      ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
        (empStieltjes lam ⟨E, √(k : ℝ) * η⟩).im := by
  have hc : 0 < η ^ 2 := by positivity
  have hη' : η ^ (1 - 2 * (n : ℤ)) * η = ((η ^ 2) ^ (n - 1))⁻¹ := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have : (1 - 2 * ((n' + 1 : ℕ) : ℤ)) = -((2 * n' + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, _root_.zpow_neg, zpow_natCast]
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have him : ∀ (t : ℝ) , (empStieltjes lam ⟨E, t⟩).im =
      (K : ℝ)⁻¹ * ∑ j, t / ((lam j - E) ^ 2 + t ^ 2) := by
    intro t
    unfold empStieltjes
    have : ((K : ℂ)⁻¹) = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [this, Complex.im_ofReal_mul, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [neg_div, ← neg_div]
    simp only [zero_sub, neg_neg]
    congr 1
    ring
  simp_rw [him]
  have hL : ∀ j, ∏ k ∈ Finset.Icc 1 n, ((lam j - E) ^ 2 + k * η ^ 2)⁻¹ =
      ∑ k ∈ Finset.Icc 1 n, (((η ^ 2) ^ (n - 1) * ((-1) ^ (k - 1) *
        (Nat.factorial (k - 1) : ℝ) * (Nat.factorial (n - k) : ℝ)))⁻¹ *
          ((lam j - E) ^ 2 + k * η ^ 2)⁻¹) := fun j =>
    aux_pf hn hc (sq_nonneg _)
  simp_rw [hL]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  have hsq : (√(k : ℝ) * η) ^ 2 = k * η ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk0.le]
  have hcoef : ((η ^ 2) ^ (n - 1) * ((-1) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) *
      (Nat.factorial (n - k) : ℝ)))⁻¹ = turC n k * η ^ (1 - 2 * (n : ℤ)) * (√(k : ℝ) * η) := by
    have h1 : (k : ℝ) ^ (-(1 / 2 : ℝ)) * √(k : ℝ) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk0]
      norm_num
    have h2 := hη'
    have hf1 : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by positivity
    have hf2 : (Nat.factorial (n - k) : ℝ) ≠ 0 := by positivity
    have hs : ((-1 : ℝ) ^ (k - 1)) ≠ 0 := by simp
    have hp : ((η ^ 2) ^ (n - 1)) ≠ 0 := by positivity
    have hs2 : ((-1 : ℝ) ^ (k - 1))⁻¹ = (-1) ^ (k - 1) := by
      rw [← inv_pow, inv_neg, inv_one]
    have e : turC n k * η ^ (1 - 2 * (n : ℤ)) * (√(k : ℝ) * η) =
        ((k : ℝ) ^ (-(1 / 2 : ℝ)) * √(k : ℝ)) * (η ^ (1 - 2 * (n : ℤ)) * η) *
          ((-1) ^ (k - 1) / ((Nat.factorial (k - 1) : ℝ) * (Nat.factorial (n - k) : ℝ))) := by
      unfold turC
      ring
    rw [e, h1, h2, one_mul]
    simp only [mul_inv, hs2, div_eq_mul_inv]
    ring
  rw [← Finset.mul_sum, hsq, hcoef]
  simp only [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

/-- `C_{1,1} = 1`. -/
example : turC 1 1 = 1 := by simp [turC]

/-- (tur1) at `n = 2` for three eigenvalues `(1, −1, 3)`, `E = 5`, `η = 1/2`. -/
example : ((3 : ℕ) : ℝ)⁻¹ * ∑ j, ∏ k ∈ Finset.Icc (1 : ℕ) 2,
      ((![(1 : ℝ), -1, 3] j - 5) ^ 2 + (k : ℝ) * (1 / 2 : ℝ) ^ 2)⁻¹ =
    ∑ k ∈ Finset.Icc (1 : ℕ) 2, turC 2 k * (1 / 2 : ℝ) ^ (1 - 2 * ((2 : ℕ) : ℤ)) *
      (empStieltjes ![(1 : ℝ), -1, 3] ⟨5, √(k : ℝ) * (1 / 2)⟩).im :=
  tur1 2 (by norm_num) _ 5 (1 / 2) (by norm_num)

/-- Reflection of `m^W` at spectrum `(1, −1)`, `z = i`. -/
example : mW (-(![1, -1] : Fin 2 → ℝ)) (-(starRingEnd ℂ) Complex.I) =
    -(starRingEnd ℂ) (mW (![1, -1] : Fin 2 → ℝ) Complex.I) :=
  mW_neg (by norm_num) _ (by simp)

/-- Reflection of the left edge at spectrum `(1, −1)`. -/
example : LmW (![1, -1] : Fin 2 → ℝ) = -LpW (-(![1, -1] : Fin 2 → ℝ)) := LmW_neg _

#print axioms Anisotropic.sW
#print axioms Anisotropic.gW
#print axioms Anisotropic.xpW
#print axioms Anisotropic.xmW
#print axioms Anisotropic.LpW
#print axioms Anisotropic.LmW
#print axioms Anisotropic.kappaW
#print axioms Anisotropic.outDomW
#print axioms Anisotropic.RigidExtremesAt
#print axioms Anisotropic.RigidExtremesWAt
#print axioms Anisotropic.sW_comp_perm
#print axioms Anisotropic.gW_comp_perm
#print axioms Anisotropic.LpW_comp_perm
#print axioms Anisotropic.LmW_comp_perm
#print axioms Anisotropic.mW_neg
#print axioms Anisotropic.LmW_neg
#print axioms Anisotropic.turC
#print axioms Anisotropic.tur1

end Anisotropic
