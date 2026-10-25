import Anisotropic.Gaussian.RotationLaw
import Anisotropic.Gaussian.Invariance
import Anisotropic.Gaussian.Measurable
import Anisotropic.Entrywise.Control

/-!
# The parity argument for the off-diagonal part

Section 6, proof of Lemma 6.2, for `Σ = diag(σ)` and a Gaussian `X`. In the paper's proof the
off-diagonal sum `𝒵` (defined after (UGU_ij), and `𝒵'` of (UG_imu)) is estimated through the
moment `E|𝒵|^p`, `p ∈ 2ℕ`. Contents:
* the off-diagonal part `𝒵 = Σ_{s ≠ t} v_s A_{st} w_t` of `⟨v, A w⟩` over the joint index set;
* labelings of `2n` slots with even fibres, and the matching count
  `Σ_{ℓ even} Π_a c_a(ℓ_a) ≤ (2n − 1)!!` for nonnegative weights with `Σ_u c_a(u)² ≤ 1`;
* the moment bound `E|𝒵|^p ≤ (2p − 1)!! E Λ_o^p` for `B = Σ̲⁻¹(G − Π)Σ̲⁻¹`, even `p` and unit
  `v`, `w`. The expansion of `|𝒵|^p = 𝒵^{p/2} 𝒵̄^{p/2}` runs over labelings of `2p` slots; the
  sign flip of one index `u`, `X ↦ R_M X R_N`, preserves the law of `X` and multiplies a term by
  `(−1)^{n_u}`, so only even labelings contribute, and `|B_{st}| ≤ Λ_o` for `s ≠ t`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The parity argument -/

/-- `𝒵 = Σ_{s ≠ t} v_s A_{st} w_t`. -/
def offPart {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (A : Matrix ι ι ℂ)
    (w : ι → ℝ) : ℂ :=
  ∑ s, ∑ t ∈ Finset.univ.erase s, (v s : ℂ) * A s t * w t

theorem testBilin_eq_diag_add_offPart {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ)
    (A : Matrix ι ι ℂ) (w : ι → ℝ) :
    testBilin v A w = ∑ s, (v s : ℂ) * A s s * w s + offPart v A w := by
  simp only [testBilin, offPart, dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  ring_nf

section Moments

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Labelings `ℓ` of `n` slots in which every value is taken an even number of times. -/
def EvenLabel {ι : Type*} [DecidableEq ι] {n : ℕ} (ℓ : Fin n → ι) : Prop :=
  ∀ u, Even (Finset.univ.filter fun a => ℓ a = u).card

/-- Permuting the slots does not change the fibre sizes of a labeling. -/
private theorem parity_evenLabel_comp {ι : Type*} [DecidableEq ι] {m : ℕ} (ℓ : Fin m → ι)
    (τ : Equiv.Perm (Fin m)) : EvenLabel (ℓ ∘ τ) ↔ EvenLabel ℓ := by
  unfold EvenLabel
  refine forall_congr' fun u => ?_
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp τ (fun a => if ℓ a = u then 1 else 0)]

/-- A labeling of `k + 2` slots whose first two slots carry the same value `x` is even iff its
restriction to the remaining `k` slots is even. -/
private theorem parity_evenLabel_cons_cons {ι : Type*} [DecidableEq ι] {k : ℕ} (x : ι)
    (ℓ : Fin k → ι) :
    EvenLabel (Fin.cons x (Fin.cons x ℓ : Fin (k + 1) → ι) : Fin (k + 2) → ι) ↔
      EvenLabel ℓ := by
  unfold EvenLabel
  refine forall_congr' fun u => ?_
  rw [Fin.card_filter_univ_succ', Fin.card_filter_univ_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]
  split_ifs <;> simp [Nat.even_add]

/-- Sums over labelings of `k + 1` slots split off the value of the first slot. -/
private theorem parity_sum_cons {ι : Type*} [Fintype ι] {k : ℕ} (G : (Fin (k + 1) → ι) → ℝ) :
    ∑ ℓ, G ℓ = ∑ x, ∑ ℓ : Fin k → ι, G (Fin.cons x ℓ) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => ι).symm _ _ fun ℓ => by
    simp [Fin.consEquiv, Fin.cons_self_tail]

/-- The pair step of the matching count: labelings of `k + 2` slots with equal values on the
first two slots. -/
private theorem parity_sum_pair_le {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} {D : ℝ}
    (c : Fin (k + 2) → ι → ℝ) (hc : ∀ a u, 0 ≤ c a u)
    (ih : ∑ ℓ : Fin k → ι, (if EvenLabel ℓ then ∏ a, c a.succ.succ (ℓ a) else 0) ≤ D) :
    ∑ ℓ : Fin (k + 2) → ι, (if EvenLabel ℓ ∧ ℓ 1 = ℓ 0 then ∏ a, c a (ℓ a) else 0) ≤
      (∑ u, c 0 u * c 1 u) * D := by
  rw [parity_sum_cons, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [parity_sum_cons]
  rw [Finset.sum_eq_single x]
  · have h : ∀ ℓ : Fin k → ι,
        (if EvenLabel (Fin.cons x (Fin.cons x ℓ : Fin (k + 1) → ι) : Fin (k + 2) → ι) ∧
            (Fin.cons x (Fin.cons x ℓ : Fin (k + 1) → ι) : Fin (k + 2) → ι) 1 =
              (Fin.cons x (Fin.cons x ℓ : Fin (k + 1) → ι) : Fin (k + 2) → ι) 0
          then ∏ a, c a ((Fin.cons x (Fin.cons x ℓ : Fin (k + 1) → ι) : Fin (k + 2) → ι) a)
          else 0) =
        c 0 x * c 1 x * (if EvenLabel ℓ then ∏ a, c a.succ.succ (ℓ a) else 0) := by
      intro ℓ
      rw [parity_evenLabel_cons_cons]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.cons_one, and_true]
      split_ifs <;> simp [Fin.succ_zero_eq_one, mul_assoc]
    simp only [h, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ih (mul_nonneg (hc 0 x) (hc 1 x))
  · intro y _ hy
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    simp [Fin.cons_one, hy]
  · simp

/-- `Σ_u c_0(u) c_b(u) ≤ 1` for nonnegative weights with `Σ_u c_a(u)² ≤ 1`. -/
private theorem parity_inner_le_one {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∑ u, f u ^ 2 ≤ 1) (hg : ∑ u, g u ^ 2 ≤ 1) : ∑ u, f u * g u ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have h0 : 0 ≤ ∑ u, f u ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
  have h1 : 0 ≤ ∑ u, g u ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
  nlinarith [mul_le_mul hf hg h1 zero_le_one]

/-- The matching count: `Σ_{ℓ even} Π_a c_a(ℓ_a) ≤ (2n − 1)!!` for unit weight vectors. -/
theorem sum_evenLabel_le {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : Fin (2 * n) → ι → ℝ) (hc : ∀ a u, 0 ≤ c a u) (hc1 : ∀ a, ∑ u, c a u ^ 2 ≤ 1) :
    ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * n) → ι => EvenLabel ℓ), ∏ a, c a (ℓ a) ≤
      ((2 * n - 1).doubleFactorial : ℝ) := by
  induction n with
  | zero =>
    have h1 : ∀ ℓ : Fin (2 * 0) → ι, ∏ a, c a (ℓ a) = 1 := fun ℓ => by simp
    simp only [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 := Finset.card_le_univ (Finset.univ.filter fun ℓ : Fin (2 * 0) → ι => EvenLabel ℓ)
    have h3 : Fintype.card (Fin (2 * 0) → ι) = 1 := by simp
    rw [h3] at h2
    norm_num
    exact_mod_cast h2
  | succ k ih =>
    set F : (Fin (2 * (k + 1)) → ι) → ℝ := fun ℓ => ∏ a, c a (ℓ a) with hF
    have hF0 : ∀ ℓ, 0 ≤ F ℓ := fun ℓ => Finset.prod_nonneg fun a _ => hc a _
    -- every even labeling pairs slot `0` with some other slot
    have step1 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * (k + 1)) → ι => EvenLabel ℓ), F ℓ ≤
        ∑ b ∈ Finset.univ.erase (0 : Fin (2 * (k + 1))), ∑ ℓ : Fin (2 * (k + 1)) → ι,
          (if EvenLabel ℓ ∧ ℓ b = ℓ 0 then F ℓ else 0) := by
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      split_ifs with hE
      · have hmem : (0 : Fin (2 * (k + 1))) ∈ Finset.univ.filter (fun a => ℓ a = ℓ 0) := by simp
        have hpos := Finset.card_pos.2 ⟨0, hmem⟩
        have h2 : 2 ≤ (Finset.univ.filter (fun a => ℓ a = ℓ 0)).card := by
          obtain ⟨r, hr⟩ := hE (ℓ 0)
          omega
        have hne : ((Finset.univ.filter (fun a => ℓ a = ℓ 0)).erase 0).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hmem]
          omega
        obtain ⟨b, hb⟩ := hne
        have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
        have hbl : ℓ b = ℓ 0 := by simpa using Finset.mem_of_mem_erase hb
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun b =>
          if EvenLabel ℓ ∧ ℓ b = ℓ 0 then F ℓ else 0) (fun b _ => ?_)
          (Finset.mem_erase.2 ⟨hb0, Finset.mem_univ b⟩))
        · simp [hE, hbl]
        · split_ifs
          · exact hF0 ℓ
          · exact le_rfl
      · exact Finset.sum_nonneg fun b _ => by split_ifs <;> simp [hF0]
    -- each pair `(0, b)` contributes at most `(2k − 1)!!`
    have step2 : ∀ b ∈ Finset.univ.erase (0 : Fin (2 * (k + 1))),
        ∑ ℓ : Fin (2 * (k + 1)) → ι, (if EvenLabel ℓ ∧ ℓ b = ℓ 0 then F ℓ else 0) ≤
          ((2 * k - 1).doubleFactorial : ℝ) := by
      intro b hb
      have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
      set τ : Equiv.Perm (Fin (2 * k + 2)) := Equiv.swap 1 b with hτ
      have hτ0 : τ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by simp) hb0.symm
      have hτ1 : τ 1 = b := Equiv.swap_apply_left 1 b
      have hre : ∑ ℓ : Fin (2 * (k + 1)) → ι, (if EvenLabel ℓ ∧ ℓ b = ℓ 0 then F ℓ else 0) =
          ∑ ℓ : Fin (2 * k + 2) → ι,
            (if EvenLabel ℓ ∧ ℓ 1 = ℓ 0 then ∏ a, c (τ a) (ℓ a) else 0) := by
        refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl ι)) _ _ fun ℓ => ?_
        have e : (Equiv.arrowCongr τ.symm (Equiv.refl ι)) ℓ = ℓ ∘ τ := by
          funext a
          simp
        rw [e, parity_evenLabel_comp]
        simp only [Function.comp_apply, hτ0, hτ1, hF]
        rw [Equiv.prod_comp τ (fun a => c a (ℓ a))]
        split_ifs <;> rfl
      rw [hre]
      have ih' := ih (fun a => c (τ a.succ.succ)) (fun a u => hc _ u) (fun a => hc1 _)
      rw [Finset.sum_filter] at ih'
      refine le_trans (parity_sum_pair_le (fun a => c (τ a)) (fun a u => hc _ u) ih') ?_
      simp only [hτ0, hτ1]
      have hdf : (0 : ℝ) ≤ ((2 * k - 1).doubleFactorial : ℝ) := by positivity
      have := parity_inner_le_one (c 0) (c b) (hc1 0) (hc1 b)
      nlinarith
    refine le_trans step1 (le_trans (Finset.sum_le_sum step2) (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rcases k with _ | j
    · simp
    · rw [show 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 by omega, Nat.doubleFactorial_add_two,
        show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
      push_cast
      ring

/-! ## The expansion of `|𝒵|^p` over labelings -/

/-- The summand `v_s A_{st} w_t` of `𝒵` at `x = (s, t)`, and `0` for `s = t`. -/
private def parity_ent {ι : Type*} [DecidableEq ι] (v w : ι → ℝ) (B : Matrix ι ι ℂ)
    (x : ι × ι) : ℂ :=
  if x.1 = x.2 then 0 else (v x.1 : ℂ) * B x.1 x.2 * w x.2

/-- The `r`-th factor of `𝒵^q 𝒵̄^q`: the summand of `𝒵` for `r < q`, its conjugate otherwise. -/
private def parity_fac {ι : Type*} [DecidableEq ι] (q : ℕ) (v w : ι → ℝ) (B : Matrix ι ι ℂ)
    (r : Fin (q + q)) (x : ι × ι) : ℂ :=
  if (r : ℕ) < q then parity_ent v w B x else (starRingEnd ℂ) (parity_ent v w B x)

/-- The term of a labeling `ℓ` of `2n` slots: the slots `(0, r)` and `(1, r)` carry the index
pair of the `r`-th factor. -/
private def parity_term {ι : Type*} {n : ℕ} (f : Fin n → ι × ι → ℂ) (ℓ : Fin (2 * n) → ι) : ℂ :=
  ∏ r, f r (ℓ (finProdFinEquiv (0, r)), ℓ (finProdFinEquiv (1, r)))

/-- A product over the `2n` slots, grouped by the pairs `(0, r)`, `(1, r)`. -/
private theorem parity_prod_slots {R : Type*} [CommMonoid R] {n : ℕ} (h : Fin (2 * n) → R) :
    ∏ a, h a = ∏ r : Fin n, h (finProdFinEquiv (0, r)) * h (finProdFinEquiv (1, r)) := by
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type_right]
  simp [Fin.prod_univ_two]

/-- Labelings of `2n` slots are the `n`-tuples of index pairs. -/
private def parity_slotEquiv (ι : Type*) (n : ℕ) : (Fin (2 * n) → ι) ≃ (Fin n → ι × ι) where
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
private theorem parity_prod_sum {ι : Type*} [Fintype ι] {n : ℕ} (f : Fin n → ι × ι → ℂ) :
    ∏ r, ∑ x, f r x = ∑ ℓ : Fin (2 * n) → ι, parity_term f ℓ := by
  rw [Fintype.prod_sum]
  exact (Fintype.sum_equiv (parity_slotEquiv ι n) _ _ fun ℓ => rfl).symm

/-- `𝒵 = Σ_{(s,t)} v_s A_{st} w_t 1(s ≠ t)`. -/
private theorem parity_offPart_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (v w : ι → ℝ)
    (B : Matrix ι ι ℂ) : offPart v B w = ∑ x, parity_ent v w B x := by
  rw [offPart, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  simp only [parity_ent, ↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp [(Finset.ne_of_mem_erase ht).symm]

/-- `|𝒵|^{2q} = Σ_ℓ T_ℓ` over labelings `ℓ` of `4q` slots. -/
private theorem parity_norm_pow_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (v w : ι → ℝ) (B : Matrix ι ι ℂ) :
    ((‖offPart v B w‖ ^ (q + q) : ℝ) : ℂ) =
      ∑ ℓ : Fin (2 * (q + q)) → ι, parity_term (parity_fac q v w B) ℓ := by
  rw [← parity_prod_sum, Fin.prod_univ_add]
  have h1 : ∀ i : Fin q, ∑ x, parity_fac q v w B (Fin.castAdd q i) x = offPart v B w := by
    intro i
    rw [parity_offPart_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [parity_fac, i.isLt]
  have h2 : ∀ i : Fin q, ∑ x, parity_fac q v w B (Fin.natAdd q i) x =
      (starRingEnd ℂ) (offPart v B w) := by
    intro i
    rw [parity_offPart_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [parity_fac]
  simp only [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- `|T_ℓ| ≤ Π_a c_a(ℓ_a) L^n` when every factor is bounded by `α_s β_t L`. -/
private theorem parity_norm_term_le {ι : Type*} {n : ℕ} (f : Fin n → ι × ι → ℂ)
    (α β : ι → ℝ) (L : ℝ) (hf : ∀ r x, ‖f r x‖ ≤ α x.1 * β x.2 * L) (ℓ : Fin (2 * n) → ι) :
    ‖parity_term f ℓ‖ ≤
      (∏ a, (if (finProdFinEquiv.symm a).1 = 0 then α else β) (ℓ a)) * L ^ n := by
  rw [parity_prod_slots, parity_term, norm_prod]
  simp only [Equiv.symm_apply_apply, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
  calc ∏ r, ‖f r (ℓ (finProdFinEquiv (0, r)), ℓ (finProdFinEquiv (1, r)))‖
      ≤ ∏ r, (α (ℓ (finProdFinEquiv (0, r))) * β (ℓ (finProdFinEquiv (1, r))) * L) :=
        Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) fun r _ => hf r _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `T_ℓ` for the factors `g_r(x) = ε_s ε_t f_r(x)` is `Π_a ε_{ℓ_a}` times `T_ℓ` for `f`. -/
private theorem parity_term_sign {ι : Type*} {n : ℕ} (f g : Fin n → ι × ι → ℂ) (ε : ι → ℝ)
    (h : ∀ r x, g r x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * f r x) (ℓ : Fin (2 * n) → ι) :
    parity_term g ℓ = ((∏ a, ε (ℓ a) : ℝ) : ℂ) * parity_term f ℓ := by
  rw [parity_prod_slots (fun a => ε (ℓ a)), parity_term, parity_term]
  simp only [h, Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_mul_distrib]

/-- The factors of `B'` with `B'_{st} = ε_s ε_t B_{st}` are `ε_s ε_t` times those of `B`. -/
private theorem parity_fac_sign {ι : Type*} [DecidableEq ι] (q : ℕ) (v w ε : ι → ℝ)
    (B B' : Matrix ι ι ℂ) (hB : ∀ s t, B' s t = (ε s : ℂ) * (ε t : ℂ) * B s t)
    (r : Fin (q + q)) (x : ι × ι) :
    parity_fac q v w B' r x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * parity_fac q v w B r x := by
  have he : parity_ent v w B' x = ((ε x.1 * ε x.2 : ℝ) : ℂ) * parity_ent v w B x := by
    unfold parity_ent
    split_ifs
    · simp
    · rw [hB]
      push_cast
      ring
  unfold parity_fac
  split_ifs
  · exact he
  · rw [he, map_mul, Complex.conj_ofReal]

/-- `|v_s B_{st} w_t| ≤ |v_s| |w_t| L` when `|B_{st}| ≤ L` for `s ≠ t`. -/
private theorem parity_fac_norm_le {ι : Type*} [DecidableEq ι] (q : ℕ) (v w : ι → ℝ)
    (B : Matrix ι ι ℂ) (L : ℝ) (hL : 0 ≤ L) (hB : ∀ s t, s ≠ t → ‖B s t‖ ≤ L)
    (r : Fin (q + q)) (x : ι × ι) :
    ‖parity_fac q v w B r x‖ ≤ |v x.1| * |w x.2| * L := by
  have he : ‖parity_ent v w B x‖ ≤ |v x.1| * |w x.2| * L := by
    unfold parity_ent
    split_ifs with h
    · simp only [norm_zero]
      positivity
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      calc |v x.1| * ‖B x.1 x.2‖ * |w x.2| = |v x.1| * |w x.2| * ‖B x.1 x.2‖ := by ring
        _ ≤ |v x.1| * |w x.2| * L := mul_le_mul_of_nonneg_left (hB _ _ h) (by positivity)
  unfold parity_fac
  split_ifs
  · exact he
  · rwa [Complex.norm_conj]

/-- `Π_a ε_{ℓ_a} = (−1)^{n_u(ℓ)}` for the sign flip at `u`. -/
private theorem parity_prod_sign {ι : Type*} [DecidableEq ι] {m : ℕ} (ℓ : Fin m → ι) (u : ι) :
    ∏ a, (if ℓ a = u then (-1 : ℝ) else 1) =
      (-1) ^ (Finset.univ.filter fun a => ℓ a = u).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ## The Gaussian sign flip -/

/-- `σ̲_s > 0` for `σ > 0`. -/
private theorem parity_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Λ_o ≥ 0`. -/
private theorem parity_LambdaO_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ LambdaO σ A z :=
  Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _)
    (mul_pos (parity_sigS_pos hσ _) (parity_sigS_pos hσ _)).le

/-- `Π = diag(m_1, …, m_M, m, …, m)` vanishes off the diagonal. -/
private theorem parity_PiDiag_offdiag {N : ℕ} (σ : Fin M → ℝ) (z : ℂ)
    {s t : Fin M ⊕ Fin N} (hst : s ≠ t) : PiDiag N σ z s t = 0 := by
  cases s <;> cases t <;> simp_all [PiDiag]

/-- `|B_{st}| ≤ Λ_o` for `s ≠ t`, `B = Σ̲⁻¹(G − Π)Σ̲⁻¹`, `Σ = diag(σ)`. -/
private theorem parity_norm_lawMat_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {z : ℂ}
    (hz : 0 < z.im) (A : Matrix (Fin M) (Fin N) ℝ) {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    ‖lawMat (diagonal σ) A z s t‖ ≤ LambdaO σ A z := by
  have h1 : lawMat (diagonal σ) A z s t =
      G (diagonal σ) A z s t / ((sigS (N := N) σ s : ℂ) * sigS σ t) := by
    have h := wEnt_eq hσ (G (diagonal σ) A z - PiDiag N σ z) s t
    unfold lawMat
    rw [piMat_diagonal (fun i => (hσ i).le) hz, ← h, wEnt, Matrix.sub_apply,
      parity_PiDiag_offdiag σ z hst, sub_zero]
  rw [h1, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (parity_sigS_pos hσ s).le, Real.norm_of_nonneg (parity_sigS_pos hσ t).le]
  unfold LambdaO
  exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
    ‖G (diagonal σ) A z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
    (Set.finite_range _).bddAbove ⟨(s, t), hst⟩

/-- The joint flip `diag(R_M, R_N)` with `−1` exactly at `u`. -/
private theorem parity_signVec_eq {N : ℕ} (u s : Fin M ⊕ Fin N) :
    signVec (Finset.univ.filter fun i => Sum.inl i = u)
        (Finset.univ.filter fun μ : Fin N => Sum.inr μ = u) s = if s = u then -1 else 1 := by
  cases s <;> simp [signVec]

/-- Each factor is a measurable function of the matrix `X`. -/
private theorem parity_measurable_fac {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (q : ℕ)
    (v w : Fin M ⊕ Fin N → ℝ) (r : Fin (q + q)) (x : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ =>
      parity_fac q v w (lawMat (diagonal σ) A z) r x := by
  have he : Measurable fun A : Matrix (Fin M) (Fin N) ℝ =>
      parity_ent v w (lawMat (diagonal σ) A z) x := by
    unfold parity_ent
    by_cases h : x.1 = x.2
    · simp only [h, ↓reduceIte]
      exact measurable_const
    · simp only [h, ↓reduceIte]
      exact ((measurable_lawMat_apply _ _ _ _).const_mul _).mul_const _
  unfold parity_fac
  by_cases hr : (r : ℕ) < q
  · simp only [hr, ↓reduceIte]
    exact he
  · simp only [hr, ↓reduceIte]
    exact Complex.continuous_conj.measurable.comp he

/-- `E|𝒵|^p ≤ (2p − 1)!! E Λ_o^p` for even `p` and unit `v, w`. -/
theorem moment_offPart_le {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {z : ℂ} (hz : 0 < z.im)
    {v w : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (hw : testNorm w = 1) {p : ℕ}
    (hp : Even p) (hint : Integrable fun ω => LambdaO σ (X ω) z ^ p) :
    Integrable (fun ω => ‖offPart v (lawMat (diagonal σ) (X ω) z) w‖ ^ p) ∧
      ∫ ω, ‖offPart v (lawMat (diagonal σ) (X ω) z) w‖ ^ p ≤
        ((2 * p - 1).doubleFactorial : ℝ) * ∫ ω, LambdaO σ (X ω) z ^ p := by
  obtain ⟨q, rfl⟩ := hp
  -- the weights `c_a = |v|` on the slots `(0, r)` and `|w|` on the slots `(1, r)`
  let c : Fin (2 * (q + q)) → Fin M ⊕ Fin N → ℝ := fun a =>
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
  -- the real parts of the terms `T_ℓ`, as functions of the matrix
  let g : (Fin (2 * (q + q)) → Fin M ⊕ Fin N) → Matrix (Fin M) (Fin N) ℝ → ℝ :=
    fun ℓ A => (parity_term (parity_fac q v w (lawMat (diagonal σ) A z)) ℓ).re
  have hgm : ∀ ℓ, Measurable (g ℓ) := fun ℓ =>
    Complex.measurable_re.comp (Finset.measurable_prod _ fun r _ =>
      parity_measurable_fac σ z q v w r _)
  have hgb : ∀ ℓ A, ‖g ℓ A‖ ≤ (∏ a, c a (ℓ a)) * LambdaO σ A z ^ (q + q) := by
    intro ℓ A
    refine le_trans (by simpa [g] using Complex.abs_re_le_norm _) (parity_norm_term_le _
      (fun u => |v u|) (fun u => |w u|) _
      (fun r x => parity_fac_norm_le q v w _ _ (parity_LambdaO_nonneg hσ A z)
        (fun s t hst => parity_norm_lawMat_le hσ hz A hst) r x) ℓ)
  have hgi : ∀ ℓ, Integrable fun ω => g ℓ (X ω) := fun ℓ =>
    Integrable.mono' (hint.const_mul _) ((hgm ℓ).comp hX.measurable_mat).aestronglyMeasurable
      (ae_of_all _ fun ω => hgb ℓ (X ω))
  have hexp : ∀ A : Matrix (Fin M) (Fin N) ℝ,
      ‖offPart v (lawMat (diagonal σ) A z) w‖ ^ (q + q) = ∑ ℓ, g ℓ A := by
    intro A
    have h := congrArg Complex.re (parity_norm_pow_eq q v w (lawMat (diagonal σ) A z))
    rwa [Complex.ofReal_re, Complex.re_sum] at h
  -- odd fibres: the sign flip at `u` changes the sign of `T_ℓ` and preserves the law of `X`
  have hzero : ∀ ℓ, ¬EvenLabel ℓ → ∫ ω, g ℓ (X ω) = 0 := by
    intro ℓ hℓ
    unfold EvenLabel at hℓ
    simp only [not_forall] at hℓ
    obtain ⟨u, hu⟩ := hℓ
    set SM : Finset (Fin M) := Finset.univ.filter fun i => Sum.inl i = u
    set SN : Finset (Fin N) := Finset.univ.filter fun μ => Sum.inr μ = u
    have hflip : ∀ A, g ℓ (signMat SM * A * (signMat SN)ᵀ) = -g ℓ A := by
      intro A
      have hs := parity_term_sign _ _ (signVec SM SN)
        (parity_fac_sign q v w (signVec SM SN) _ _ (lawMat_signFlip σ SM SN A z)) ℓ
      have hp : ∏ a, signVec SM SN (ℓ a) = -1 := by
        simp only [SM, SN, parity_signVec_eq]
        rw [parity_prod_sign]
        exact (Nat.not_even_iff_odd.1 hu).neg_one_pow
      simp only [g]
      rw [hs, hp]
      simp
    have h1 : ∫ ω, g ℓ (signMat SM * X ω * (signMat SN)ᵀ) = ∫ ω, g ℓ (X ω) := by
      rw [← integral_map (measurable_rotate hX.measurable_mat _ _).aemeasurable
          (hgm ℓ).aestronglyMeasurable, hX.map_rotate (signMat_mem SM) (signMat_mem SN),
        integral_map hX.measurable_mat.aemeasurable (hgm ℓ).aestronglyMeasurable]
    simp only [hflip, integral_neg] at h1
    linarith
  have hle : ∀ ℓ, ∫ ω, g ℓ (X ω) ≤ (∏ a, c a (ℓ a)) * ∫ ω, LambdaO σ (X ω) z ^ (q + q) := by
    intro ℓ
    rw [← integral_const_mul]
    exact integral_mono (hgi ℓ) (hint.const_mul _) fun ω =>
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hgb ℓ (X ω))
  have hI : 0 ≤ ∫ ω, LambdaO σ (X ω) z ^ (q + q) :=
    integral_nonneg fun ω => pow_nonneg (parity_LambdaO_nonneg hσ _ _) _
  have hsum : (fun ω => ‖offPart v (lawMat (diagonal σ) (X ω) z) w‖ ^ (q + q)) =
      fun ω => ∑ ℓ, g ℓ (X ω) := funext fun ω => hexp (X ω)
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun ℓ _ => hgi ℓ
  · rw [hsum, integral_finsetSum _ fun ℓ _ => hgi ℓ]
    calc ∑ ℓ, ∫ ω, g ℓ (X ω)
        ≤ ∑ ℓ, if EvenLabel ℓ then (∏ a, c a (ℓ a)) * ∫ ω, LambdaO σ (X ω) z ^ (q + q)
            else 0 := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          split_ifs with h
          · exact hle ℓ
          · exact (hzero ℓ h).le
      _ = (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * (q + q)) → Fin M ⊕ Fin N =>
            EvenLabel ℓ), ∏ a, c a (ℓ a)) * ∫ ω, LambdaO σ (X ω) z ^ (q + q) := by
          rw [Finset.sum_filter, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          split_ifs <;> simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_evenLabel_le (q + q) c hc hc1) hI

end Moments

/-- `sum_evenLabel_le` at `n = 2`, `ι = Fin 2`, `c_a ≡ (1/√2, 1/√2)` for every slot `a`. -/
example :
    ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * 2) → Fin 2 => EvenLabel ℓ),
        ∏ a, (fun (_ : Fin (2 * 2)) (_ : Fin 2) => (√2)⁻¹) a (ℓ a) ≤
      ((2 * 2 - 1).doubleFactorial : ℝ) :=
  sum_evenLabel_le 2 (fun _ _ => (√2)⁻¹) (fun _ _ => by positivity) fun _ => by
    simp [inv_pow, Real.sq_sqrt]

/-- `moment_offPart_le` at `M = N = 2`, `X` the `2 × 2` Gaussian matrix, `σ = (3, 1)` (the
spectrum of `Σ₀ = [[2, 1], [1, 2]]`), `z = 2i`, `v = w = (1/2, 1/2, 1/2, 1/2)`, `p = 2`. The
integrability of `Λ_o²` is kept as a hypothesis: this is a conditional example. -/
example (hint : Integrable fun ω =>
      LambdaO (![3, 1] : Fin 2 → ℝ) (gaussX 2 2 ω) (2 * Complex.I) ^ 2) :
    Integrable (fun ω => ‖offPart (fun _ : Fin 2 ⊕ Fin 2 => (1 / 2 : ℝ))
        (lawMat (diagonal ![3, 1]) (gaussX 2 2 ω) (2 * Complex.I)) fun _ => 1 / 2‖ ^ 2) ∧
      ∫ ω, ‖offPart (fun _ : Fin 2 ⊕ Fin 2 => (1 / 2 : ℝ))
          (lawMat (diagonal ![3, 1]) (gaussX 2 2 ω) (2 * Complex.I)) (fun _ => 1 / 2)‖ ^ 2 ≤
        ((2 * 2 - 1).doubleFactorial : ℝ) *
          ∫ ω, LambdaO (![3, 1] : Fin 2 → ℝ) (gaussX 2 2 ω) (2 * Complex.I) ^ 2 :=
  moment_offPart_le (gaussX_isGaussianEnsemble 2 2)
    (fun i => by fin_cases i <;> norm_num) (by simp)
    (by rw [testNorm, Real.sqrt_eq_one]; norm_num)
    (by rw [testNorm, Real.sqrt_eq_one]; norm_num) even_two hint

end Anisotropic

#print axioms Anisotropic.offPart
#print axioms Anisotropic.testBilin_eq_diag_add_offPart
#print axioms Anisotropic.EvenLabel
#print axioms Anisotropic.sum_evenLabel_le
#print axioms Anisotropic.moment_offPart_le
