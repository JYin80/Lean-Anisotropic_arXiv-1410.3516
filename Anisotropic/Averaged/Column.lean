import Anisotropic.Comparison.Brackets
import Anisotropic.Comparison.ColumnMoment
import Anisotropic.Comparison.DegreeCount
import Anisotropic.Comparison.TaggedWords
import Anisotropic.Comparison.Words
import Anisotropic.LinAlg.Basic

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The `i`-form counts, the case facts, (cond_avg_pf) and (A+_avg) (§9) -/

/-- The number of linear forms of `[G_{xy}]^s` whose coefficient vector is indexed by the
letter `I`. -/
def degTabI (x y : Letter) (s : Fin 3) : ℕ :=
  if s = 0 then 0
  else if s = 1 then (if x = .I then 1 else 0) + (if y = .I then 1 else 0)
  else if x = .V then (if y = .I then 1 else 0)
  else if y = .V then (if x = .I then 1 else 0) else 0

/-- `d_{X,i}` of one tagged word: the number of `i`-forms of `A⁺(w, σ)`. -/
def tagDegI : (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → ℕ
  | 0, _, _ => 0
  | _k + 1, w, σ => ∑ l, degTabI (factorX w l) (factorY w l) (σ l)

/-- `d_{X,i} = ∑_r d_{X,i,r}`. -/
def dXIof {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) :
    ℕ := ∑ r, tagDegI (ns r) (ws r) (σs r)

/-- No identically vanishing bracket and only the tags `0, 1` (`ℤ₂` tags, `|σ|_v = 0`). -/
def tagNZ2 (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) : Bool :=
  tagNZ n w σ && (tagV σ == 0)

/-- The case facts of §9 for `n(w) = 1`, `ℤ₂` tags: `d_{X,r} ≤ 2 ⇒ d_{X,i,r} = 0`; and
`d_{X,i,r} ≤ n(w)`. -/
theorem avgCase_one : ∀ w : Word 1, ∀ σ : Fin 2 → Fin 3, tagNZ2 1 w σ = true →
    (tagDeg 1 w σ ≤ 2 → tagDegI 1 w σ = 0) ∧ tagDegI 1 w σ ≤ 1 := by decide

/-- The case facts for `n(w) = 2`: `d_{X,r} ≤ 2 ⇒ d_{X,i,r} ≤ 1`; and `d_{X,i,r} ≤ n(w)`. -/
theorem avgCase_two : ∀ w : Word 2, ∀ σ : Fin 3 → Fin 3, tagNZ2 2 w σ = true →
    (tagDeg 2 w σ ≤ 2 → tagDegI 2 w σ ≤ 1) ∧ tagDegI 2 w σ ≤ 2 := by decide

/-- The case facts for `n(w) = 3`: `d_{X,r} ≤ 2 ⇒ d_{X,i,r} ≤ 1`; and `d_{X,i,r} ≤ n(w)`. -/
theorem avgCase_three : ∀ w : Word 3, ∀ σ : Fin 4 → Fin 3, tagNZ2 3 w σ = true →
    (tagDeg 3 w σ ≤ 2 → tagDegI 3 w σ ≤ 1) ∧ tagDegI 3 w σ ≤ 3 := by decide

section CondAvg

/-- The case facts for one word with `n(w) ≤ 3`, `ℤ₂` tags and no zero bracket: for
`n(w) = 0`, `d_{X,r} = 2|σ_r|` and `d_{X,i,r} = 0`; `d_{X,r} ≤ 2 ⇒ d_{X,i,r} ≤ [n(w) ≥ 2]`;
`d_{X,i,r} ≤ n(w)`. -/
private theorem column_case (n : ℕ) (hn : n ≤ 3) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hnz : tagNZ n w σ = true) (hv : tagV σ = 0) :
    (n = 0 → tagDeg n w σ = 2 * tagMu σ ∧ tagDegI n w σ = 0) ∧
      (tagDeg n w σ ≤ 2 → tagDegI n w σ ≤ if 2 ≤ n then 1 else 0) ∧ tagDegI n w σ ≤ n := by
  have h2 : tagNZ2 n w σ = true := by simp [tagNZ2, hnz, hv]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl
  · revert hv; revert w σ; decide
  · obtain ⟨h1, h1'⟩ := avgCase_one w σ h2
    exact ⟨fun h => absurd h (by norm_num), fun hd => by simpa using h1 hd, h1'⟩
  · obtain ⟨h1, h1'⟩ := avgCase_two w σ h2
    exact ⟨fun h => absurd h (by norm_num), fun hd => by simpa using h1 hd, h1'⟩
  · obtain ⟨h1, h1'⟩ := avgCase_three w σ h2
    exact ⟨fun h => absurd h (by norm_num), fun hd => by simpa using h1 hd, h1'⟩

/-- `n(w_r) ≤ 3` when `∑_r n(w_r) = 3`. -/
private theorem column_ns_le {p : ℕ} (ns : Fin p → ℕ) (hn : ∑ r, ns r = 3) (r : Fin p) :
    ns r ≤ 3 :=
  hn ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

/-- `d_{X,i} ≤ 3` for `∑_r n(w_r) = 3`, `ℤ₂` tags and no zero bracket. -/
private theorem column_dXI_le {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (hn : ∑ r, ns r = 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (hv : ∀ r, tagV (σs r) = 0) :
    dXIof ns ws σs ≤ 3 := by
  calc dXIof ns ws σs = ∑ r, tagDegI (ns r) (ws r) (σs r) := rfl
    _ ≤ ∑ r, ns r := Finset.sum_le_sum fun r _ =>
        (column_case (ns r) (column_ns_le ns hn r) (ws r) (σs r) (hnz r) (hv r)).2.2
    _ = 3 := hn

end CondAvg

/-- (cond_avg_pf): `2q + 2∑_{r>q}|σ_r| + [d_{X,i} = 3] ≤ d_X + ∑_{r≤q}(2 − d_{X,r})_+` for
`∑_r n(w_r) = 3`, `ℤ₂` tags and no zero bracket. -/
theorem cond_avg_pf {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (hn : ∑ r, ns r = 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (hv : ∀ r, tagV (σs r) = 0) :
    2 * (Finset.univ.filter fun r => 1 ≤ ns r).card +
        2 * (∑ r ∈ Finset.univ.filter (fun r => ns r = 0), tagMu (σs r)) +
        (if dXIof ns ws σs = 3 then 1 else 0) ≤
      dXof ns ws σs +
        ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), (2 - tagDeg (ns r) (ws r) (σs r)) := by
  have hc := fun r => column_case (ns r) (column_ns_le ns hn r) (ws r) (σs r) (hnz r) (hv r)
  set S0 := Finset.univ.filter (fun r => ns r = 0) with hS0def
  set S1 := Finset.univ.filter (fun r => 1 ≤ ns r) with hS1def
  have hcompl : Finset.univ.filter (fun r => ¬ ns r = 0) = S1 := by
    ext r; simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hdX : dXof ns ws σs = ∑ r ∈ S0, tagDeg (ns r) (ws r) (σs r) +
      ∑ r ∈ S1, tagDeg (ns r) (ws r) (σs r) := by
    rw [dXof, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => ns r = 0), hcompl]
  have hS0 : ∑ r ∈ S0, tagDeg (ns r) (ws r) (σs r) = 2 * ∑ r ∈ S0, tagMu (σs r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr => ((hc r).1 (Finset.mem_filter.1 hr).2).1
  have hdXI : dXIof ns ws σs = ∑ r ∈ S1, tagDegI (ns r) (ws r) (σs r) := by
    rw [dXIof, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => ns r = 0), hcompl]
    have : ∑ r ∈ S0, tagDegI (ns r) (ws r) (σs r) = 0 :=
      Finset.sum_eq_zero fun r hr => ((hc r).1 (Finset.mem_filter.1 hr).2).2
    rw [this, zero_add]
  have hkey : 2 * S1.card + (if dXIof ns ws σs = 3 then 1 else 0) ≤
      ∑ r ∈ S1, (tagDeg (ns r) (ws r) (σs r) + (2 - tagDeg (ns r) (ws r) (σs r))) := by
    split_ifs with h3
    · obtain ⟨r0, hr0, hd0⟩ : ∃ r0 ∈ S1, 3 ≤ tagDeg (ns r0) (ws r0) (σs r0) := by
        by_contra hne
        simp only [not_exists, not_and, not_le] at hne
        have hb : ∀ r ∈ S1, tagDegI (ns r) (ws r) (σs r) ≤ if 2 ≤ ns r then 1 else 0 :=
          fun r hr => (hc r).2.1 (by have := hne r hr; omega)
        have h2 : ∑ r, (if 2 ≤ ns r then 1 else 0) ≤ 1 := by
          have : ∑ r, 2 * (if 2 ≤ ns r then 1 else 0) ≤ ∑ r, ns r :=
            Finset.sum_le_sum fun r _ => by split_ifs <;> omega
          rw [← Finset.mul_sum, hn] at this
          omega
        have : dXIof ns ws σs ≤ 1 := by
          rw [hdXI]
          calc ∑ r ∈ S1, tagDegI (ns r) (ws r) (σs r) ≤ ∑ r ∈ S1, (if 2 ≤ ns r then 1 else 0) :=
                Finset.sum_le_sum hb
            _ ≤ ∑ r, (if 2 ≤ ns r then 1 else 0) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  fun _ _ _ => Nat.zero_le _
            _ ≤ 1 := h2
        omega
      calc 2 * S1.card + 1 = ∑ r ∈ S1, (2 + if r = r0 then 1 else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq', smul_eq_mul,
              mul_comm]
            simp [hr0]
        _ ≤ _ := Finset.sum_le_sum fun r _ => by
            split_ifs with h
            · subst h; omega
            · omega
    · calc 2 * S1.card + 0 = ∑ _r ∈ S1, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]; rfl
        _ ≤ _ := Finset.sum_le_sum fun r _ => by omega
  rw [hdX, hS0]
  have hsplit : ∑ r ∈ S1, (tagDeg (ns r) (ws r) (σs r) + (2 - tagDeg (ns r) (ws r) (σs r))) =
      ∑ r ∈ S1, tagDeg (ns r) (ws r) (σs r) + ∑ r ∈ S1, (2 - tagDeg (ns r) (ws r) (σs r)) :=
    Finset.sum_add_distrib
  omega

section ColPoly

/-- `N^{−1/2} = (√N)⁻¹`. -/
private theorem column_rpow_eq (N : ℕ) : (N : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), neg_div]

/-- `|E y^m| ≤ C_m N^{−m/2}` under (moments of X-1). -/
private theorem column_coord {N : ℕ} {C : ℕ → ℝ} {ρ : Measure ℝ} (hN : 1 ≤ N)
    (hρ : ∀ n : ℕ, Integrable (fun y => |y| ^ n) ρ ∧ ∫ y, |Real.sqrt N * y| ^ n ∂ρ ≤ C n)
    (m : ℕ) : |∫ y, y ^ m ∂ρ| ≤ C m * (Real.sqrt N)⁻¹ ^ m := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have h1 : (fun y : ℝ => |y| ^ m) = fun y => (Real.sqrt N)⁻¹ ^ m * |Real.sqrt N * y| ^ m := by
    funext y
    rw [abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow,
      one_mul]
  calc |∫ y, y ^ m ∂ρ| ≤ ∫ y, |y ^ m| ∂ρ := abs_integral_le_integral_abs
    _ = ∫ y, |y| ^ m ∂ρ := by simp_rw [abs_pow]
    _ = (Real.sqrt N)⁻¹ ^ m * ∫ y, |Real.sqrt N * y| ^ m ∂ρ := by rw [h1, integral_const_mul]
    _ ≤ (Real.sqrt N)⁻¹ ^ m * C m := mul_le_mul_of_nonneg_left (hρ m).2 (by positivity)
    _ = _ := mul_comm _ _

/-- A monomial `∏_a y_{J(a)}` of independent centred coordinates: integrable, with
`|E ∏_a y_{J(a)}| ≤ (D N^{−1/2})^{|ι|}`, and `= 0` if some value of `J` is taken exactly once. -/
private theorem column_monomial {ι : Type*} [Fintype ι] {M N : ℕ} {C : ℕ → ℝ}
    (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)] (hN : 1 ≤ N)
    (hmean : ∀ j, ∫ y, y ∂(ρ j) = 0)
    (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
      ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n)
    {D : ℝ} (hD1 : 1 ≤ D) (hD : ∀ m ≤ Fintype.card ι, C m ≤ D) (J : ι → Fin M) :
    Integrable (fun y : Fin M → ℝ => ∏ a, y (J a)) (Measure.pi ρ) ∧
    |∫ y, ∏ a, y (J a) ∂(Measure.pi ρ)| ≤
      if ∀ x, (Finset.univ.filter fun a => J a = x).card ≠ 1 then
        (D * (Real.sqrt N)⁻¹) ^ Fintype.card ι else 0 := by
  set cnt : Fin M → ℕ := fun x => (Finset.univ.filter fun a => J a = x).card with hcnt
  have hprod : ∀ y : Fin M → ℝ, ∏ a, y (J a) = ∏ x, y x ^ cnt x := by
    intro y
    rw [← Finset.prod_fiberwise Finset.univ J (fun a => y (J a))]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => congrArg y (Finset.mem_filter.1 ha).2),
      Finset.prod_const]
  have hfun : (fun y : Fin M → ℝ => ∏ a, y (J a)) =
      fun y => ∏ x, (fun (x : Fin M) (t : ℝ) => t ^ cnt x) x (y x) := funext hprod
  have hintc : ∀ x, Integrable (fun t : ℝ => t ^ cnt x) (ρ x) := fun x =>
    (hρ x (cnt x)).1.mono' (continuous_pow _).aestronglyMeasurable
      (ae_of_all _ fun t => by simp [Real.norm_eq_abs])
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact Integrable.fintype_prod hintc
  · rw [hfun, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun (x : Fin M) (t : ℝ) => t ^ cnt x),
      Finset.abs_prod]
    have hsN : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
    split_ifs with hA
    · have hsum : ∑ x, cnt x = Fintype.card ι := by
        rw [← Finset.card_univ]
        exact (Finset.card_eq_sum_card_fiberwise (f := J) (s := Finset.univ) (t := Finset.univ)
          (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm
      have hle : ∀ x, cnt x ≤ Fintype.card ι := fun x => by
        rw [← Finset.card_univ]; exact Finset.card_filter_le _ _
      calc ∏ x, |∫ t, t ^ cnt x ∂(ρ x)| ≤ ∏ x, (D * (Real.sqrt N)⁻¹) ^ cnt x := by
            refine Finset.prod_le_prod₀ (fun x _ => abs_nonneg _) fun x _ => ?_
            rcases Nat.eq_zero_or_pos (cnt x) with h0 | hpos
            · rw [h0]; simp
            · calc |∫ t, t ^ cnt x ∂(ρ x)| ≤ C (cnt x) * (Real.sqrt N)⁻¹ ^ cnt x :=
                    column_coord hN (hρ x) _
                _ ≤ D ^ cnt x * (Real.sqrt N)⁻¹ ^ cnt x := by
                    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hsN _)
                    calc C (cnt x) ≤ D := hD _ (hle x)
                      _ = D ^ 1 := (pow_one D).symm
                      _ ≤ D ^ cnt x := pow_le_pow_right₀ hD1 hpos
                _ = _ := (mul_pow _ _ _).symm
        _ = (D * (Real.sqrt N)⁻¹) ^ Fintype.card ι := by rw [Finset.prod_pow_eq_pow_sum, hsum]
    · simp only [not_forall, not_not] at hA
      obtain ⟨x, hx⟩ := hA
      rw [Finset.prod_eq_zero (Finset.mem_univ x)]
      have : cnt x = 1 := hx
      rw [this]; simp [hmean x]

/-- A representative of the class of `a` under `a ~ a' ⇔ J a = J a'`. -/
private def column_rep {ι : Type*} {M : ℕ} (J : ι → Fin M) (a : ι) : ι :=
  @Classical.epsilon ι ⟨a⟩ fun a' => J a' = J a

private theorem column_rep_spec {ι : Type*} {M : ℕ} (J : ι → Fin M) (a : ι) :
    J (column_rep J a) = J a :=
  @Classical.epsilon_spec ι (fun a' => J a' = J a) ⟨a, rfl⟩

private theorem column_rep_congr {ι : Type*} {M : ℕ} (J : ι → Fin M) {a b : ι}
    (h : J a = J b) : column_rep J a = column_rep J b := by
  unfold column_rep
  simp only [h]

/-- Summing a product weight over the tuples `J` that are constant on the fibres of an idempotent
`f`: the sum factorises over the representatives `r = f r`. -/
private theorem column_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (w : ι → Fin M → ℝ) (hw : ∀ a x, 0 ≤ w a x) (f : ι → ι) (hf : ∀ a, f (f a) = f a)
    (s : Finset (ι → Fin M))
    (hs : ∀ J ∈ s, ∀ a, J (f a) = J a) :
    ∑ J ∈ s, ∏ a, w a (J a) ≤
      ∏ r ∈ Finset.univ.filter (fun r => f r = r),
        ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x := by
  set H : ι → Fin M → ℝ := fun r x => ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x
    with hHdef
  have hH1 : ∀ r, f r ≠ r → ∀ x, H r x = 1 := by
    intro r hr x
    have : Finset.univ.filter (fun a => f a = r) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro ha; exact hr (by rw [← ha, hf])
    simp [H, this]
  have hJ : ∀ J ∈ s, ∏ a, w a (J a) = ∏ r : {r // f r = r}, H r (J r) := by
    intro J hJs
    calc ∏ a, w a (J a) = ∏ a, w a (J (f a)) :=
          Finset.prod_congr rfl fun a _ => by rw [hs J hJs a]
      _ = ∏ r, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a (J (f a)) :=
          (Finset.prod_fiberwise _ f _).symm
      _ = ∏ r, H r (J r) := Finset.prod_congr rfl fun r _ =>
          Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
      _ = ∏ r ∈ Finset.univ.filter (fun r => f r = r), H r (J r) :=
          (Finset.prod_filter_of_ne fun r _ h => by_contra fun hr => h (hH1 r hr _)).symm
      _ = ∏ r : {r // f r = r}, H r (J r) := Finset.prod_subtype _ (by simp) _
  set restr : (ι → Fin M) → ({r // f r = r} → Fin M) := fun J r => J r with hrestr
  have hinj : Set.InjOn restr s := by
    intro J hJ J' hJ' h
    funext a
    have := congrFun h ⟨f a, hf a⟩
    simp only [restr] at this
    rw [← hs J hJ a, ← hs J' hJ' a, this]
  calc ∑ J ∈ s, ∏ a, w a (J a) = ∑ J ∈ s, ∏ r : {r // f r = r}, H r (restr J r) :=
        Finset.sum_congr rfl hJ
    _ = ∑ g ∈ s.image restr, ∏ r : {r // f r = r}, H r (g r) :=
        (Finset.sum_image (f := fun g : {r // f r = r} → Fin M =>
          ∏ r : {r // f r = r}, H r (g r)) hinj).symm
    _ ≤ ∑ g : {r // f r = r} → Fin M, ∏ r : {r // f r = r}, H r (g r) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun g _ _ =>
          Finset.prod_nonneg fun r _ => Finset.prod_nonneg fun a _ => hw _ _
    _ = ∏ r : {r // f r = r}, ∑ x, H r x := (Fintype.prod_sum _).symm
    _ = _ := (Finset.prod_subtype (Finset.univ.filter fun r => f r = r) (fun r => by simp)
          (fun r => ∑ x, H r x)).symm

/-- `∏_{l ∈ s} a_l ≤ ∑_{l ∈ s} a_l^{|s|}` for `a ≥ 0`, `s ≠ ∅`. -/
private theorem column_prod_le_sum_pow {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (a : α → ℝ) (ha : ∀ l, 0 ≤ a l) : ∏ l ∈ s, a l ≤ ∑ l ∈ s, a l ^ s.card := by
  obtain ⟨l0, hl0, hmax⟩ := s.exists_max_image a hs
  calc ∏ l ∈ s, a l ≤ ∏ l ∈ s, a l0 := Finset.prod_le_prod₀ (fun l _ => ha l) hmax
    _ = a l0 ^ s.card := Finset.prod_const _
    _ ≤ ∑ l ∈ s, a l ^ s.card :=
        Finset.single_le_sum (f := fun l => a l ^ s.card) (fun l _ => pow_nonneg (ha l) _) hl0

/-- One block of (730): `∑_j ∏_{l ∈ s} |c_{lj}| ≤ (|s| + 1) τ'⁻¹ N b^{|s| ∧ 2} K^{|s| − 2}`
with `τ' = min(τ, 1)`, from (bound_sum_hat). -/
private theorem column_block {M N d : ℕ} {τ K b : ℝ} (hτ : 0 < τ) (hK : 1 ≤ K)
    (hb : 0 ≤ b) (hM : (M : ℝ) ≤ τ⁻¹ * N) (c : Fin d → Fin M → ℂ) (hc : ∀ l j, ‖c l j‖ ≤ K)
    (hc2 : ∀ l, ∑ j, ‖c l j‖ ^ 2 ≤ N * b ^ 2) (s : Finset (Fin d)) :
    ∑ j, ∏ l ∈ s, ‖c l j‖ ≤
      (s.card + 1) * ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) := by
  have hτ' : 0 < min τ 1 := lt_min hτ one_pos
  have hM' : (M : ℝ) ≤ (min τ 1)⁻¹ * N :=
    hM.trans (mul_le_mul_of_nonneg_right (inv_anti₀ hτ' (min_le_left _ _)) (Nat.cast_nonneg _))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hB : 0 ≤ (min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2) := by positivity
  rcases s.eq_empty_or_nonempty with h | h
  · subst h
    simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Finset.card_empty, Nat.cast_zero, zero_add, one_mul, Nat.zero_le,
      min_eq_left, pow_zero, Nat.zero_sub]
    exact hM'
  · calc ∑ j, ∏ l ∈ s, ‖c l j‖ ≤ ∑ j, ∑ l ∈ s, ‖c l j‖ ^ s.card :=
          Finset.sum_le_sum fun j _ => column_prod_le_sum_pow s h _ fun _ => norm_nonneg _
      _ = ∑ l ∈ s, ∑ j, ‖c l j‖ ^ s.card := Finset.sum_comm
      _ ≤ ∑ l ∈ s, ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) :=
          Finset.sum_le_sum fun l _ =>
            bound_sum_hat hτ' (min_le_right _ _) hK hb hM' (c l) (hc l) (hc2 l) s.card
      _ = s.card * ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card + 1) * ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hB

/-- The expansion (prod_pA1) of `∏_l L_l ∏_t Q_t` over index tuples
`J : κ ⊕ (Fin k ⊕ Fin k) → Fin M`. -/
private theorem column_expand {κ : Type*} [Fintype κ] [DecidableEq κ] {M k : ℕ}
    (c : κ → Fin M → ℂ) (B : Fin k → Fin M → Fin M → ℂ) (y : Fin M → ℝ) :
    (∏ l, ∑ j, c l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
      ∑ J : κ ⊕ (Fin k ⊕ Fin k) → Fin M,
        ((∏ l, c l (J (Sum.inl l))) *
          ∏ t, B t (J (Sum.inr (Sum.inl t))) (J (Sum.inr (Sum.inr t)))) *
          ((∏ a, y (J a) : ℝ) : ℂ) := by
  have h1 : ∏ l, ∑ j, c l j * (y j : ℂ) = ∑ u : κ → Fin M, ∏ l, (c l (u l) * (y (u l) : ℂ)) :=
    Fintype.prod_sum _
  have h2 : ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
      ∑ v : Fin k ⊕ Fin k → Fin M, ∏ t, ((y (v (Sum.inl t)) : ℂ) *
        B t (v (Sum.inl t)) (v (Sum.inr t)) * y (v (Sum.inr t))) := by
    have e1 : ∀ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
        ∑ q : Fin M × Fin M, (y q.1 : ℂ) * B t q.1 q.2 * y q.2 := fun t =>
      (Fintype.sum_prod_type' (fun j j' => (y j : ℂ) * B t j j' * y j')).symm
    simp_rw [e1]
    rw [Fintype.prod_sum]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin M) (fun _ => Fin M)).symm.sum_comp]
    rw [← (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (Fin M)).symm.sum_comp]
    rfl
  rw [h1, h2, Finset.sum_mul_sum,
    ← (Equiv.sumArrowEquivProdArrow κ (Fin k ⊕ Fin k) (Fin M)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Fintype.prod_sum_type, Complex.ofReal_mul,
    Complex.ofReal_prod, Finset.prod_mul_distrib]
  ring


/-- The power count of the two-class bound: blocks `r` of sizes `s_r ≥ 2` with `p_r` pointwise and
`q_r` summed linear indices, `∑ s_r = d_P + d_S + 2k` with `d_P + d_S` odd and `d_S ≤ 3`:
`∏_r N^{1 − s_r/2} b^{p_r + q_r ∧ 2} ≤ N^{−1/2} b^{d_P + d_S − [d_S = 3]}` (`β = N^{−1/2} ≤ 1`). -/
private theorem column_exp_two {α : Type*} (L : Finset α) (s pp ss : α → ℕ)
    (hs : ∀ r ∈ L, 2 ≤ s r) {dP dS k : ℕ} (hsum_s : ∑ r ∈ L, s r = dP + dS + 2 * k)
    (hsum_p : ∑ r ∈ L, pp r = dP) (hsum_q : ∑ r ∈ L, ss r = dS) (hodd : Odd (dP + dS))
    (hdS : dS ≤ 3) {β b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∏ r ∈ L, (β ^ (s r - 2) * b ^ (pp r + min (ss r) 2)) ≤
      β * b ^ (dP + dS - if dS = 3 then 1 else 0) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_pow_eq_pow_sum]
  have hmin : min (∑ r ∈ L, ss r) 2 ≤ ∑ r ∈ L, min (ss r) 2 := by
    clear hsum_q hsum_s hsum_p hs
    induction L using Finset.induction_on with
    | empty => simp
    | insert a L ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      omega
  have hexp : dP + dS - (if dS = 3 then 1 else 0) ≤ ∑ r ∈ L, (pp r + min (ss r) 2) := by
    rw [Finset.sum_add_distrib, hsum_p]
    rw [hsum_q] at hmin
    split_ifs <;> omega
  obtain ⟨r0, hr0, hodd0⟩ : ∃ r ∈ L, Odd (s r) := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have : Even (∑ r ∈ L, s r) :=
      Finset.even_sum _ fun r hr => Nat.not_odd_iff_even.1 (hne r hr)
    rw [hsum_s] at this
    exact (Nat.not_even_iff_odd.2 (hodd.add_even (even_two_mul k))) this
  have hβexp : 1 ≤ ∑ r ∈ L, (s r - 2) := by
    have h3 : 1 ≤ s r0 - 2 := by
      have := hs r0 hr0; obtain ⟨m, hm⟩ := hodd0; omega
    exact h3.trans (Finset.single_le_sum (f := fun r => s r - 2) (fun _ _ => Nat.zero_le _) hr0)
  calc β ^ (∑ r ∈ L, (s r - 2)) * b ^ (∑ r ∈ L, (pp r + min (ss r) 2))
      ≤ β ^ 1 * b ^ (dP + dS - if dS = 3 then 1 else 0) :=
        mul_le_mul (pow_le_pow_of_le_one hβ0 hβ1 hβexp) (pow_le_pow_of_le_one hb0 hb1 hexp)
          (pow_nonneg hb0 _) (pow_nonneg hβ0 _)
    _ = β * b ^ (dP + dS - if dS = 3 then 1 else 0) := by rw [pow_one]

end ColPoly

/-- (A+_avg), deterministic core: independent centred coordinates with `E|√N y_j|^n ≤ C_n`;
`dP` linear forms with coefficients bounded pointwise by `b`, `dS` linear forms with
`∑_j |c_j| ≤ N b`, `∑_j |c_j|² ≤ N b²`, `|c_j| ≤ K`, and `k` quadratic forms with entries at most
`K`. For `dP + dS` odd and `dS ≤ 3`: `|E ∏∏∏| ≤ K' K^{k + dS} N^{−1/2} b^{dP + dS − [dS = 3]}`. -/
theorem colPoly_bound_two (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (dP dS k : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)]
      (cP : Fin dP → Fin M → ℂ) (cS : Fin dS → Fin M → ℂ) (B : Fin k → Fin M → Fin M → ℂ)
      (K b : ℝ), 1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ K → 0 ≤ b → b ≤ 1 →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ l j, ‖cP l j‖ ≤ b) → (∀ l j, ‖cS l j‖ ≤ K) → (∀ l, ∑ j, ‖cS l j‖ ≤ N * b) →
      (∀ l, ∑ j, ‖cS l j‖ ^ 2 ≤ N * b ^ 2) → (∀ t j j', ‖B t j j'‖ ≤ K) →
      Odd (dP + dS) → dS ≤ 3 →
      ‖∫ y, (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) *
          ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' ∂(Measure.pi ρ)‖ ≤
        K' * K ^ (k + dS) * (N : ℝ) ^ (-(1 : ℝ) / 2) *
          b ^ (dP + dS - if dS = 3 then 1 else 0) := by
  set n : ℕ := dP + dS + 2 * k with hn
  set T : ℝ := (min τ 1)⁻¹ with hTdef
  set D : ℝ := 1 + ∑ m ∈ Finset.range (n + 1), |C m| with hDdef
  have hτ' : 0 < min τ 1 := lt_min hτ one_pos
  have hT1 : 1 ≤ T := (one_le_inv₀ hτ').2 (min_le_right _ _)
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hD1 : 1 ≤ D := by
    have := Finset.sum_nonneg (s := Finset.range (n + 1)) fun m _ => abs_nonneg (C m)
    linarith
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hD : ∀ m ≤ n, C m ≤ D := by
    intro m hm
    have h1 : |C m| ≤ ∑ m ∈ Finset.range (n + 1), |C m| :=
      Finset.single_le_sum (f := fun m => |C m|) (fun m _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have := le_abs_self (C m)
    linarith
  have hnT : 0 ≤ ((n : ℝ) + 1) * T := mul_nonneg (by positivity) hT0
  refine ⟨(n : ℝ) ^ n * D ^ n * (((n : ℝ) + 1) * T) ^ n,
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hD0 _)) (pow_nonneg hnT _), ?_⟩
  intro M N ρ _ cP cS B K b hN hM hK hb0 hb1 hmean hρ hcP hcS _hcS1 hcS2 hB hodd hdS3
  set β : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hβdef
  have hβ : β = (Real.sqrt N)⁻¹ := column_rpow_eq N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβpos : 0 < β := by rw [hβ]; exact inv_pos.2 (Real.sqrt_pos.2 hNpos)
  have hβ0 : 0 ≤ β := hβpos.le
  have hβ1 : β ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have hβN : β ^ 2 * N = 1 := by
    rw [hβ, inv_pow, Real.sq_sqrt hNpos.le, inv_mul_cancel₀ hNpos.ne']
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  set tgt : ℝ := β * b ^ (dP + dS - if dS = 3 then 1 else 0) with htgt
  have htgt0 : 0 ≤ tgt := mul_nonneg hβ0 (pow_nonneg hb0 _)
  -- the linear forms of both classes, and the index tuples
  let κ := Fin dP ⊕ Fin dS
  let c : κ → Fin M → ℂ := Sum.elim cP cS
  let ι := κ ⊕ (Fin k ⊕ Fin k)
  have hcard : Fintype.card ι = n := by
    simp only [ι, κ, Fintype.card_sum, Fintype.card_fin]; omega
  let coef : (ι → Fin M) → ℂ := fun J =>
    (∏ l, c l (J (Sum.inl l))) * ∏ t, B t (J (Sum.inr (Sum.inl t))) (J (Sum.inr (Sum.inr t)))
  let w : ι → Fin M → ℝ := Sum.elim (fun l x => ‖c l x‖) (fun _ _ => 1)
  have hw : ∀ a x, 0 ≤ w a x := by intro a x; cases a <;> simp [w]
  let F : (ι → Fin M) → ℝ := fun J => ∏ a, w a (J a)
  have hF0 : ∀ J, 0 ≤ F J := fun J => Finset.prod_nonneg fun a _ => hw _ _
  have hcoef : ∀ J, ‖coef J‖ ≤ K ^ k * F J := by
    intro J
    have hFJ : F J = ∏ l, ‖c l (J (Sum.inl l))‖ := by
      change ∏ a : κ ⊕ (Fin k ⊕ Fin k), w a (J a) = _
      simp only [Fintype.prod_sum_type, w, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one,
        mul_one]
    have hBk : ∏ t, ‖B t (J (Sum.inr (Sum.inl t))) (J (Sum.inr (Sum.inr t)))‖ ≤ K ^ k := by
      calc _ ≤ ∏ _t : Fin k, K := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            fun t _ => hB _ _ _
        _ = K ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [coef, norm_mul, norm_prod]
    rw [hFJ, mul_comm (K ^ k)]
    exact mul_le_mul_of_nonneg_left hBk (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  let P : (ι → Fin M) → Prop := fun J => ∀ x, (Finset.univ.filter fun a => J a = x).card ≠ 1
  have hmono := fun J => column_monomial (ι := ι) ρ hN hmean hρ hD1
    (by rw [hcard]; exact hD) J
  -- the integrand: both classes form one product over `κ`
  have hfold : ∀ y : Fin M → ℝ, (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) *
      ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
      (∏ l, ∑ j, c l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' := by
    intro y
    rw [show (∏ l, ∑ j, c l j * (y j : ℂ)) =
        (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) from
      Fintype.prod_sum_type _]
  -- the integral as a sum over index tuples
  have hint_eq : ∫ y, (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) *
      ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' ∂(Measure.pi ρ) =
      ∑ J : ι → Fin M, coef J * ((∫ y, ∏ a, y (J a) ∂(Measure.pi ρ) : ℝ) : ℂ) := by
    have hexp : ∀ y : Fin M → ℝ, (∏ l, ∑ j, cP l j * (y j : ℂ)) *
        (∏ l, ∑ j, cS l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
        ∑ J : ι → Fin M, coef J * ((∏ a, y (J a) : ℝ) : ℂ) := fun y => by
      rw [hfold]; exact column_expand c B y
    rw [show (fun y : Fin M → ℝ => (∏ l, ∑ j, cP l j * (y j : ℂ)) *
        (∏ l, ∑ j, cS l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j') =
        fun y => ∑ J : ι → Fin M, coef J * ((∏ a, y (J a) : ℝ) : ℂ) from funext hexp]
    rw [integral_finsetSum _ fun J _ => ?_]
    · refine Finset.sum_congr rfl fun J _ => ?_
      rw [integral_const_mul, integral_complex_ofReal]
    · exact ((hmono J).1.ofReal (𝕜 := ℂ)).const_mul (coef J)
  -- one pattern of coincidences
  have hpat : ∀ f : ι → ι,
      ∑ J ∈ (Finset.univ.filter P).filter (fun J => column_rep J = f), F J * β ^ n ≤
        (((n : ℝ) + 1) * T) ^ n * K ^ dS * tgt := by
    intro f
    have hR0 : 0 ≤ (((n : ℝ) + 1) * T) ^ n * K ^ dS * tgt :=
      mul_nonneg (mul_nonneg (pow_nonneg hnT _) (pow_nonneg hK0 _)) htgt0
    by_cases hne : ((Finset.univ.filter P).filter (fun J => column_rep J = f)).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]; exact hR0
    obtain ⟨J0, hJ0⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ0
    obtain ⟨hPJ0, hf⟩ := hJ0
    have hidem : ∀ a, f (f a) = f a := by
      intro a; rw [← hf]; exact column_rep_congr J0 (column_rep_spec J0 a)
    have hs : ∀ J ∈ (Finset.univ.filter P).filter (fun J => column_rep J = f),
        ∀ a, J (f a) = J a := by
      intro J hJ a; rw [← (Finset.mem_filter.1 hJ).2]; exact column_rep_spec J a
    have hfib := column_fiber w hw f hidem _ hs
    rw [← Finset.sum_mul]
    set L := Finset.univ.filter fun r => f r = r with hL
    set sz : ι → ℕ := fun r => (Finset.univ.filter fun a => f a = r).card with hsz
    set pp : ι → ℕ := fun r =>
      (Finset.univ.filter fun l : Fin dP => f (Sum.inl (Sum.inl l)) = r).card with hpp_def
    set ss : ι → ℕ := fun r =>
      (Finset.univ.filter fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r).card with hss_def
    have hiff : ∀ r ∈ L, ∀ a, f a = r ↔ J0 a = J0 r := by
      intro r hr a
      have hr' : f r = r := (Finset.mem_filter.1 hr).2
      constructor
      · intro h
        have := column_rep_spec J0 a
        rw [hf, h] at this; exact this.symm
      · intro h
        rw [← hf] at hr' ⊢; rw [column_rep_congr J0 h]; exact hr'
    have hsz2 : ∀ r ∈ L, 2 ≤ sz r := by
      intro r hr
      have heq : (Finset.univ.filter fun a => f a = r) =
          Finset.univ.filter fun a => J0 a = J0 r := Finset.filter_congr fun a _ => hiff r hr a
      have h1 : (Finset.univ.filter fun a => J0 a = J0 r).card ≠ 1 := hPJ0 (J0 r)
      have h2 : 0 < (Finset.univ.filter fun a => J0 a = J0 r).card :=
        Finset.card_pos.2 ⟨r, by simp⟩
      change 2 ≤ (Finset.univ.filter fun a => f a = r).card
      rw [heq]; omega
    have hmaps : ∀ a, f a ∈ L := fun a => Finset.mem_filter.2 ⟨Finset.mem_univ _, hidem a⟩
    have hsum_sz : ∑ r ∈ L, sz r = dP + dS + 2 * k := by
      have := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := L)
        (fun a _ => hmaps a)
      rw [Finset.card_univ, hcard] at this; exact this.symm
    have hsum_pp : ∑ r ∈ L, pp r = dP := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun l : Fin dP => f (Sum.inl (Sum.inl l)))
        (s := Finset.univ) (t := L) (fun l _ => hmaps _)
      rw [Finset.card_univ, Fintype.card_fin] at this; exact this.symm
    have hsum_ss : ∑ r ∈ L, ss r = dS := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun l : Fin dS => f (Sum.inl (Sum.inr l)))
        (s := Finset.univ) (t := L) (fun l _ => hmaps _)
      rw [Finset.card_univ, Fintype.card_fin] at this; exact this.symm
    have hssn : ∀ r, ss r ≤ n := fun r => by
      have : ss r ≤ dS := by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin dS))
          (fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r)
      omega
    have hSr : ∀ r, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x =
        ∑ x, (∏ l ∈ Finset.univ.filter (fun l : Fin dP => f (Sum.inl (Sum.inl l)) = r),
          ‖cP l x‖) *
          ∏ l ∈ Finset.univ.filter (fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r), ‖cS l x‖ := by
      intro r; refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type,
        Fintype.prod_sum_type]
      simp [w, c]
    have hblock : ∀ r ∈ L, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x ≤
        b ^ pp r * (((n : ℝ) + 1) * (T * N * b ^ min (ss r) 2 * K ^ (ss r - 2))) := by
      intro r _
      rw [hSr]
      have hPb : ∀ x, ∏ l ∈ Finset.univ.filter (fun l : Fin dP => f (Sum.inl (Sum.inl l)) = r),
          ‖cP l x‖ ≤ b ^ pp r := fun x => by
        calc _ ≤ ∏ _l ∈ Finset.univ.filter (fun l : Fin dP => f (Sum.inl (Sum.inl l)) = r), b :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => hcP l x
          _ = b ^ pp r := Finset.prod_const _
      have hblk := column_block hτ hK hb0 hM cS hcS hcS2
        (Finset.univ.filter fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r)
      have hB0 : 0 ≤ T * N * b ^ min (ss r) 2 * K ^ (ss r - 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg hT0 hNpos.le) (pow_nonneg hb0 _)) (pow_nonneg hK0 _)
      have hcardle : ((ss r : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have := hssn r
        have : ((ss r : ℕ) : ℝ) ≤ n := by exact_mod_cast this
        linarith
      calc ∑ x, (∏ l ∈ Finset.univ.filter (fun l : Fin dP => f (Sum.inl (Sum.inl l)) = r),
            ‖cP l x‖) *
            ∏ l ∈ Finset.univ.filter (fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r), ‖cS l x‖
          ≤ ∑ x, b ^ pp r *
            ∏ l ∈ Finset.univ.filter (fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r),
              ‖cS l x‖ :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hPb x)
              (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ = b ^ pp r * ∑ x,
            ∏ l ∈ Finset.univ.filter (fun l : Fin dS => f (Sum.inl (Sum.inr l)) = r),
              ‖cS l x‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ b ^ pp r * (((ss r : ℕ) + 1) * (T * N * b ^ min (ss r) 2 * K ^ (ss r - 2))) :=
            mul_le_mul_of_nonneg_left hblk (pow_nonneg hb0 _)
        _ ≤ b ^ pp r * (((n : ℝ) + 1) * (T * N * b ^ min (ss r) 2 * K ^ (ss r - 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardle hB0) (pow_nonneg hb0 _)
    have hβn : β ^ n = ∏ r ∈ L, β ^ sz r := by rw [Finset.prod_pow_eq_pow_sum, hsum_sz]
    calc _ ≤ (∏ r ∈ L, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ n :=
          mul_le_mul_of_nonneg_right hfib (pow_nonneg hβ0 _)
      _ = ∏ r ∈ L, ((∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ sz r) := by
          rw [hβn, ← Finset.prod_mul_distrib]
      _ ≤ ∏ r ∈ L, ((((n : ℝ) + 1) * T * K ^ (ss r - 2)) *
            (β ^ (sz r - 2) * b ^ (pp r + min (ss r) 2))) := by
          refine Finset.prod_le_prod₀ (fun r _ => mul_nonneg (Finset.sum_nonneg fun x _ =>
            Finset.prod_nonneg fun a _ => hw _ _) (pow_nonneg hβ0 _)) fun r hr => ?_
          obtain ⟨m, hm⟩ : ∃ m, sz r = m + 2 := ⟨sz r - 2, by have := hsz2 r hr; omega⟩
          have hpow : β ^ sz r * N = β ^ (sz r - 2) := by
            rw [hm, Nat.add_sub_cancel, pow_add, mul_assoc, hβN, mul_one]
          calc (∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ sz r
              ≤ (b ^ pp r * (((n : ℝ) + 1) * (T * N * b ^ min (ss r) 2 * K ^ (ss r - 2)))) *
                  β ^ sz r :=
                mul_le_mul_of_nonneg_right (hblock r hr) (pow_nonneg hβ0 _)
            _ = (((n : ℝ) + 1) * T * K ^ (ss r - 2)) *
                  ((b ^ pp r * b ^ min (ss r) 2) * (β ^ sz r * N)) := by ring
            _ = _ := by rw [hpow, ← pow_add]; ring
      _ = (∏ r ∈ L, (((n : ℝ) + 1) * T * K ^ (ss r - 2))) *
            ∏ r ∈ L, (β ^ (sz r - 2) * b ^ (pp r + min (ss r) 2)) := Finset.prod_mul_distrib
      _ ≤ ((((n : ℝ) + 1) * T) ^ n * K ^ dS) * tgt := by
          refine mul_le_mul ?_ (column_exp_two L sz pp ss hsz2 hsum_sz hsum_pp hsum_ss hodd hdS3
              hβ0 hβ1 hb0 hb1)
            (Finset.prod_nonneg fun r _ => mul_nonneg (pow_nonneg hβ0 _) (pow_nonneg hb0 _))
            (mul_nonneg (pow_nonneg hnT _) (pow_nonneg hK0 _))
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
          have hL1 : 1 ≤ ((n : ℝ) + 1) * T := by
            have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
            nlinarith
          refine mul_le_mul (pow_le_pow_right₀ hL1 ?_) (pow_le_pow_right₀ hK ?_)
            (pow_nonneg hK0 _) (pow_nonneg hnT _)
          · rw [← hcard]; exact Finset.card_le_univ L
          · exact (Finset.sum_le_sum fun r _ => Nat.sub_le _ _).trans hsum_ss.le
  rw [hint_eq]
  calc ‖∑ J : ι → Fin M, coef J * ((∫ y, ∏ a, y (J a) ∂(Measure.pi ρ) : ℝ) : ℂ)‖
      ≤ ∑ J : ι → Fin M, ‖coef J‖ * |∫ y, ∏ a, y (J a) ∂(Measure.pi ρ)| := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun J _ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ J : ι → Fin M, (if P J then K ^ k * F J * (D * β) ^ n else 0) := by
        refine Finset.sum_le_sum fun J _ => ?_
        have hm := (hmono J).2
        by_cases hPJ : P J
        · rw [ite_eq_left hPJ]
          have hPJ' : ∀ x, (Finset.univ.filter fun a => J a = x).card ≠ 1 := hPJ
          rw [ite_eq_left hPJ', ← hβ, hcard] at hm
          exact mul_le_mul (hcoef J) hm (abs_nonneg _)
            (mul_nonneg (pow_nonneg hK0 _) (hF0 J))
        · rw [ite_eq_right hPJ]
          have hPJ' : ¬ ∀ x, (Finset.univ.filter fun a => J a = x).card ≠ 1 := hPJ
          rw [ite_eq_right hPJ'] at hm
          have : |∫ y, ∏ a, y (J a) ∂(Measure.pi ρ)| = 0 := le_antisymm hm (abs_nonneg _)
          rw [this, mul_zero]
    _ = ∑ J ∈ Finset.univ.filter P, K ^ k * F J * (D * β) ^ n := (Finset.sum_filter _ _).symm
    _ = K ^ k * D ^ n * ∑ J ∈ Finset.univ.filter P, F J * β ^ n := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun J _ => ?_
        change K ^ k * F J * (D * β) ^ n = K ^ k * D ^ n * (F J * β ^ n)
        rw [mul_pow]; ring
    _ = K ^ k * D ^ n * ∑ f : ι → ι,
          ∑ J ∈ (Finset.univ.filter P).filter (fun J => column_rep J = f), F J * β ^ n := by
        rw [Finset.sum_fiberwise]
    _ ≤ K ^ k * D ^ n * ∑ _f : ι → ι, ((((n : ℝ) + 1) * T) ^ n * K ^ dS * tgt) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hpat f)
          (mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hD0 _))
    _ = (n : ℝ) ^ n * D ^ n * (((n : ℝ) + 1) * T) ^ n * K ^ (k + dS) * β *
          b ^ (dP + dS - if dS = 3 then 1 else 0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, hcard, nsmul_eq_mul, pow_add,
          htgt]
        push_cast
        ring

section Lem87

/-- The coefficient vectors of `[G_{xy}]^s`, each labelled `true` if its letter is `I`. -/
private def column_brackFormsL (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    List (Bool × (Fin M → ℂ)) :=
  if s = 0 then []
  else if s = 1 then
    (if x = .M then [] else [(decide (x = .I), colC Sig A z (letVec Sig v i μ x) μ)]) ++
      (if y = .M then [] else [(decide (y = .I), rowC Sig A z (letVec Sig v i μ y) μ)])
  else if x = .V then
    (if y = .M then [] else [(decide (y = .I), rowC Sig A z (letVec Sig v i μ y) μ)])
  else if y = .V then
    (if x = .M then [] else [(decide (x = .I), colC Sig A z (letVec Sig v i μ x) μ)])
  else []

/-- The coefficient vectors of `A⁺(w, σ)`, each labelled `true` if it is an `i`-form. -/
private def column_tagFormsL (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    (n : ℕ) → Word n → (Fin (n + 1) → Fin 3) → List (Bool × (Fin M → ℂ))
  | 0, _, σ => (emptyForms Sig A z v μ (σ 0)).map fun c => (false, c)
  | k + 1, w, σ => (List.ofFn fun l : Fin (k + 2) =>
      column_brackFormsL Sig A z v i μ (factorX w l) (factorY w l) (σ l)).flatten

/-- A labelled form is `colC`/`rowC` of `e_i` (label `true`) or of `v̄` (label `false`). -/
private def column_lab (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (q : Bool × (Fin M → ℂ)) : Prop :=
  (q.1 = true → q.2 = colC Sig A z (eI (Sum.inl i)) μ ∨ q.2 = rowC Sig A z (eI (Sum.inl i)) μ) ∧
    (q.1 = false → q.2 = colC Sig A z (vbar Sig v) μ ∨ q.2 = rowC Sig A z (vbar Sig v) μ)

private theorem column_brackFormsL_snd (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) :
    (column_brackFormsL Sig A z v i μ x y s).map Prod.snd = brackForms Sig A z v i μ x y s := by
  cases x <;> cases y <;> fin_cases s <;> simp [column_brackFormsL, brackForms]

private theorem column_brackFormsL_count (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) :
    ((column_brackFormsL Sig A z v i μ x y s).filter fun q => q.1).length = degTabI x y s := by
  cases x <;> cases y <;> fin_cases s <;> simp [column_brackFormsL, degTabI]

private theorem column_brackFormsL_lab (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) :
    ∀ q ∈ column_brackFormsL Sig A z v i μ x y s, column_lab Sig A z v i μ q := by
  cases x <;> cases y <;> fin_cases s <;> simp [column_brackFormsL, column_lab, letVec]

private theorem column_tagFormsL_snd (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    (column_tagFormsL Sig A z v i μ n w σ).map Prod.snd = tagForms Sig A z v i μ n w σ := by
  cases n with
  | zero => simp [column_tagFormsL, tagForms, List.map_map, Function.comp_def]
  | succ k =>
    simp only [column_tagFormsL, tagForms, List.map_flatten, List.map_ofFn, Function.comp_def,
      column_brackFormsL_snd]

private theorem column_tagFormsL_count (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    ((column_tagFormsL Sig A z v i μ n w σ).filter fun q => q.1).length = tagDegI n w σ := by
  cases n with
  | zero => simp [column_tagFormsL, tagDegI, List.filter_map, Function.comp_def]
  | succ k =>
    simp only [column_tagFormsL, tagDegI, List.filter_flatten, List.length_flatten, List.map_ofFn,
      List.sum_ofFn, Function.comp_def, column_brackFormsL_count]

private theorem column_tagFormsL_lab (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) :
    ∀ q ∈ column_tagFormsL Sig A z v i μ n w σ, column_lab Sig A z v i μ q := by
  intro q hq
  cases n with
  | zero =>
    have h2 : σ 0 ≠ 2 := by
      intro h; simp [tagV, h] at hv
    simp only [column_tagFormsL, emptyForms] at hq
    split_ifs at hq with h0 h1
    · simp at hq
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [column_lab]
    · exact absurd (by revert h0 h1 h2; generalize σ 0 = t; revert t; decide) h2
  | succ k =>
    simp only [column_tagFormsL, List.mem_flatten, List.mem_ofFn] at hq
    obtain ⟨L, ⟨l, rfl⟩, hq⟩ := hq
    exact column_brackFormsL_lab Sig A z v i μ _ _ _ q hq

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem column_vbar_eI (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
    vbar Sig (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) = eI (Sum.inr ν) := by
  funext s
  cases s with
  | inl j =>
    have : (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl = 0 := by
      funext j; simp [eI]
    simp only [vbar, Sum.elim_inl, this, Matrix.mulVec_zero, Pi.zero_apply]
    simp [eI]
  | inr ν' => simp [vbar, eI, Pi.single_apply]

private theorem column_norm_conjIf (b : Bool) (x : ℂ) : ‖conjIf b x‖ = ‖x‖ := by
  cases b <;> simp [conjIf]

/-- `(L.map g).prod` splits into the forms labelled `false` and those labelled `true`. -/
private theorem column_prod_split {α : Type*} [CommMonoid α] (L : List (Bool × (Fin M → ℂ)))
    (g : Bool × (Fin M → ℂ) → α) :
    (L.map g).prod =
      ((L.filter fun q => !q.1).map g).prod * ((L.filter fun q => q.1).map g).prod := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rcases q with ⟨_ | _, c⟩ <;> simp [ih, mul_comm, mul_left_comm, mul_assoc]

private theorem column_length_split (L : List (Bool × (Fin M → ℂ))) :
    L.length = (L.filter fun q => !q.1).length + (L.filter fun q => q.1).length := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rcases q with ⟨_ | _, c⟩ <;> simp [ih] <;> omega

/-- `(L.map g).prod = ∏_{l < |L|} g(L_l)`. -/
private theorem column_list_prod {α : Type*} [CommMonoid α] (L : List (Bool × (Fin M → ℂ)))
    (g : Bool × (Fin M → ℂ) → α) : (L.map g).prod = ∏ l : Fin L.length, g (L.get l) := by
  conv_lhs => rw [← List.ofFn_get L]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- `conj` passes to the coefficients of a product of linear forms of a real vector. -/
private theorem column_conj_prod (b : Bool) (L : List (Fin M → ℂ)) (y : Fin M → ℝ) :
    conjIf b ((L.map fun c => linForm c y).prod) =
      ((L.map fun c j => conjIf b (c j)).map fun c => linForm c y).prod := by
  cases b
  · simp [conjIf]
  · simp only [conjIf, ite_true, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp [linForm, map_sum, map_mul, Complex.conj_ofReal]

/-- `Q_μ` at the column `y`, possibly conjugated, as a quadratic form in `y`. -/
private theorem column_conj_Qmu (b : Bool) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (y : Fin M → ℝ) :
    conjIf b (Qmu Sig (updCol A μ y) z μ) =
      ∑ j, ∑ j', (y j : ℂ) * conjIf b (Gmu Sig A z μ (Sum.inl j) (Sum.inl j')) * y j' := by
  rw [Qmu_updCol]
  cases b
  · simp [conjIf]
  · simp [conjIf, map_sum, map_mul, Complex.conj_ofReal]


private theorem column_degTab_le (x y : Letter) (s : Fin 3) : degTab x y s ≤ 2 := by
  revert x y s; decide

/-- `deg A(w, σ) ≤ 2 (n(w) + 1)`. -/
private theorem column_tagDeg_le (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagDeg n w σ ≤ 2 * (n + 1) := by
  cases n with
  | zero => simp only [tagDeg]; split_ifs <;> omega
  | succ k =>
    simp only [tagDeg]
    calc ∑ l, degTab (factorX w l) (factorY w l) (σ l) ≤ ∑ _l : Fin (k + 2), 2 :=
          Finset.sum_le_sum fun l _ => column_degTab_le _ _ _
      _ = 2 * (k + 1 + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring


end Lem87

/-- (A+_avg) for tagged words with `ℤ₂` tags, `v_r = e_{ν_r}`, `ν_r ≠ μ`: with the a priori
bounds `|G^{(μ)}_{ν_r j}|, |G^{(μ)}_{j ν_r}| ≤ b`, `∑_j |G^{(μ)}_{ij}|^a ≤ N b^a` (`a = 1, 2`, both
orders) and `|G^{(μ)}_{jj'}| ≤ K`, the column expectation of `∏_r A⁺(r) ∏_{t<k} Q_μ` (each factor
possibly conjugated) is at most `K' K^{d_X + k} N^{−1/2} b^{d_X − [d_{X,i} = 3]}`. -/
theorem lem87_avg (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p k : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (νs : Fin p → Fin N)
      (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)] (K b : ℝ),
      1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ K → 0 ≤ b → b ≤ 1 →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ r, νs r ≠ μ) →
      (∀ r j, ‖Gmu Sig A z μ (Sum.inr (νs r)) (Sum.inl j)‖ ≤ b ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr (νs r))‖ ≤ b) →
      (∀ j j', ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j')‖ ≤ K) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2) →
      ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
        (cs : Fin p → Bool) (ct : Fin k → Bool), ∑ r, ns r = 3 →
        (∀ r, tagNZ (ns r) (ws r) (σs r) = true) → (∀ r, tagV (σs r) = 0) →
        ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r)
            (σs r)).map fun c => linForm c y).prod)) *
            ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂(Measure.pi ρ)‖ ≤
          K' * K ^ (dXof ns ws σs + k) * (N : ℝ) ^ (-(1 : ℝ) / 2) *
            b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) := by
  choose Kf hKf0 hKf using fun dP dS : ℕ => colPoly_bound_two C τ hτ dP dS k
  have hK'0 : 0 ≤ ∑ dP ∈ Finset.range (2 * p + 7), ∑ dS ∈ Finset.range 4, Kf dP dS :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hKf0 _ _
  refine ⟨∑ dP ∈ Finset.range (2 * p + 7), ∑ dS ∈ Finset.range 4, Kf dP dS, hK'0, ?_⟩
  intro M N Sig A z i μ νs ρ _ K b hN hM hK hb0 hb1 hmean hρ _hνμ hGν hGjj hS1 hS1' hS2 hS2'
    ns ws σs cs ct hns hnz hv
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  set β : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hβdef
  have hβ0 : 0 ≤ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set dX : ℕ := dXof ns ws σs with hdX
  set dXI : ℕ := dXIof ns ws σs with hdXI
  set Lr : Fin p → List (Bool × (Fin M → ℂ)) := fun r =>
    column_tagFormsL Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r) (σs r) with hLr
  set Ls : List (Bool × (Fin M → ℂ)) :=
    (List.ofFn fun r => (Lr r).map fun q => (q.1, fun j => conjIf (cs r) (q.2 j))).flatten
    with hLs
  set LP := Ls.filter fun q => !q.1 with hLP
  set LS := Ls.filter fun q => q.1 with hLS
  have hlenS : LS.length = dXI := by
    simp only [LS, Ls, List.filter_flatten, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_def, List.filter_map, List.length_map, Lr, column_tagFormsL_count, dXI, dXIof]
  have hlen : LP.length + LS.length = dX := by
    rw [← column_length_split Ls]
    simp only [Ls, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      List.length_map, Lr]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← tagForms_length Sig A z (eI (Sum.inr (νs r))) i μ, ← column_tagFormsL_snd,
      List.length_map]
  set dP := LP.length with hdP
  set dS := LS.length with hdS
  let cP : Fin dP → Fin M → ℂ := fun l => (LP.get l).2
  let cS : Fin dS → Fin M → ℂ := fun l => (LS.get l).2
  let B' : Fin k → Fin M → Fin M → ℂ := fun t j j' =>
    conjIf (ct t) (Gmu Sig A z μ (Sum.inl j) (Sum.inl j'))
  -- every form of `Ls` is a (conjugated) labelled form of one word
  have hmem : ∀ q ∈ Ls, ∃ r, ∃ q0, column_lab Sig A z (eI (Sum.inr (νs r))) i μ q0 ∧
      q = (q0.1, fun j => conjIf (cs r) (q0.2 j)) := by
    intro q hq
    simp only [Ls, List.mem_flatten, List.mem_ofFn] at hq
    obtain ⟨L, ⟨r, hL⟩, hqL⟩ := hq
    subst hL
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hqL
    exact ⟨r, q0, column_tagFormsL_lab _ _ _ _ _ _ _ _ _ (hv r) q0 hq0, rfl⟩
  have hcolI : ∀ j, colC Sig A z (eI (Sum.inl i)) μ j = Gmu Sig A z μ (Sum.inl i) (Sum.inl j) :=
    fun j => ent_eI_eI _ _ _
  have hrowI : ∀ j, rowC Sig A z (eI (Sum.inl i)) μ j = Gmu Sig A z μ (Sum.inl j) (Sum.inl i) :=
    fun j => ent_eI_eI _ _ _
  have hcolV : ∀ (ν : Fin N) j, colC Sig A z (vbar Sig (eI (Sum.inr ν))) μ j =
      Gmu Sig A z μ (Sum.inr ν) (Sum.inl j) := fun ν j => by
    rw [colC, column_vbar_eI]; exact ent_eI_eI _ _ _
  have hrowV : ∀ (ν : Fin N) j, rowC Sig A z (vbar Sig (eI (Sum.inr ν))) μ j =
      Gmu Sig A z μ (Sum.inl j) (Sum.inr ν) := fun ν j => by
    rw [rowC, column_vbar_eI]; exact ent_eI_eI _ _ _
  -- the pointwise class
  have hcP : ∀ l j, ‖cP l j‖ ≤ b := by
    intro l j
    have hq : LP.get l ∈ LP := List.get_mem LP l
    obtain ⟨hqs, hq1⟩ := List.mem_filter.1 hq
    obtain ⟨r, q0, ⟨_, hlab⟩, he⟩ := hmem _ hqs
    have h1 : q0.1 = false := by rw [he] at hq1; simpa using hq1
    change ‖(LP.get l).2 j‖ ≤ b
    rw [he]
    simp only [column_norm_conjIf]
    rcases hlab h1 with h | h <;> rw [h]
    · rw [hcolV]; exact (hGν r j).1
    · rw [hrowV]; exact (hGν r j).2
  -- the summed class
  have hcS : ∀ l, (∀ j, ‖cS l j‖ ≤ K) ∧ ∑ j, ‖cS l j‖ ≤ N * b ∧ ∑ j, ‖cS l j‖ ^ 2 ≤ N * b ^ 2 := by
    intro l
    have hq : LS.get l ∈ LS := List.get_mem LS l
    obtain ⟨hqs, hq1⟩ := List.mem_filter.1 hq
    obtain ⟨r, q0, ⟨hlab, _⟩, he⟩ := hmem _ hqs
    have h1 : q0.1 = true := by rw [he] at hq1; simpa using hq1
    change (∀ j, ‖(LS.get l).2 j‖ ≤ K) ∧ ∑ j, ‖(LS.get l).2 j‖ ≤ N * b ∧
      ∑ j, ‖(LS.get l).2 j‖ ^ 2 ≤ N * b ^ 2
    rw [he]
    simp only [column_norm_conjIf]
    rcases hlab h1 with h | h <;> rw [h]
    · simp only [hcolI]; exact ⟨fun j => hGjj i j, hS1, hS2⟩
    · simp only [hrowI]; exact ⟨fun j => hGjj j i, hS1', hS2'⟩
  have hB' : ∀ t j j', ‖B' t j j'‖ ≤ K := fun t j j' => by
    simp only [B', column_norm_conjIf]; exact hGjj j j'
  -- `d_S = d_{X,i} ≤ 3`, `d_P + d_S = d_X` odd, `d_X ≤ 2p + 6`
  have hdS3 : dS ≤ 3 := hlenS ▸ column_dXI_le ns ws σs hns hnz hv
  have hodd : Odd (dP + dS) := by
    rw [hlen]
    exact dX_odd ns ws σs hns hnz (Finset.sum_eq_zero fun r _ => hv r)
  have hdXle : dX ≤ 2 * p + 6 := by
    calc dX = ∑ r, tagDeg (ns r) (ws r) (σs r) := rfl
      _ ≤ ∑ r, 2 * (ns r + 1) := Finset.sum_le_sum fun r _ => column_tagDeg_le _ _ _
      _ = 2 * p + 6 := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hns, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]; ring
  -- the integrand
  have hint : ∀ y : Fin M → ℝ,
      (∏ r, conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r)
          (σs r)).map fun c => linForm c y).prod)) *
          ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) =
        (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) *
          ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j' := by
    intro y
    have h1 : ∏ r, conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r)
        (σs r)).map fun c => linForm c y).prod) = (Ls.map fun q => linForm q.2 y).prod := by
      simp only [Ls, List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn,
        Function.comp_def]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← column_tagFormsL_snd, column_conj_prod, List.map_map, List.map_map, List.map_map]
      rfl
    have h2 : (Ls.map fun q => linForm q.2 y).prod =
        (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) := by
      rw [column_prod_split, column_list_prod LP, column_list_prod LS]
      rfl
    have h3 : ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) =
        ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j' :=
      Finset.prod_congr rfl fun t _ => column_conj_Qmu (ct t) Sig A z μ y
    rw [h1, h2, h3]
  have hcp := hKf dP dS M N ρ cP cS B' K b hN hM hK hb0 hb1 hmean hρ hcP
    (fun l => (hcS l).1) (fun l => (hcS l).2.1) (fun l => (hcS l).2.2) hB' hodd hdS3
  have hKle : Kf dP dS ≤ ∑ dP ∈ Finset.range (2 * p + 7), ∑ dS ∈ Finset.range 4, Kf dP dS := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun d => ∑ dS ∈ Finset.range 4, Kf d dS)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hKf0 _ _) (a := dP)
      (Finset.mem_range.2 (by omega)))
    exact Finset.single_le_sum (f := fun e => Kf dP e) (fun _ _ => hKf0 _ _) (a := dS)
      (Finset.mem_range.2 (by omega))
  have hexp : dP + dS - (if dS = 3 then 1 else 0) = dX - if dXI = 3 then 1 else 0 := by
    rw [hlen, hlenS]
  calc ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r)
          (σs r)).map fun c => linForm c y).prod)) *
          ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂(Measure.pi ρ)‖
      = ‖∫ y, (∏ l, ∑ j, cP l j * (y j : ℂ)) * (∏ l, ∑ j, cS l j * (y j : ℂ)) *
          ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j' ∂(Measure.pi ρ)‖ := by
        simp_rw [hint]
    _ ≤ Kf dP dS * K ^ (k + dS) * β * b ^ (dP + dS - if dS = 3 then 1 else 0) := hcp
    _ ≤ (∑ dP ∈ Finset.range (2 * p + 7), ∑ dS ∈ Finset.range 4, Kf dP dS) * K ^ (dX + k) * β *
          b ^ (dX - if dXI = 3 then 1 else 0) := by
        rw [hexp]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hKle (pow_le_pow_right₀ hK (by omega)) (pow_nonneg hK0 _) hK'0) hβ0)
          (pow_nonneg hb0 _)


/-- The equality case of (cond_avg_pf): three words `𝐢𝛍` with tags `(0, 1)`: `d_X = 3`,
`d_{X,i} = 0`, both sides `6`. -/
example : tagNZ 1 (fun _ => true) ![0, 1] = true ∧ tagDeg 1 (fun _ => true) ![0, 1] = 1 ∧
    tagDegI 1 (fun _ => true) ![0, 1] = 0 ∧ tagDeg 1 (fun _ => true) ![1, 1] = 3 ∧
    tagDegI 1 (fun _ => true) ![1, 1] = 1 := by
  decide

/-- The word `𝛍𝐢𝐢𝛍` at `v̄ = e_μ`: tags `(2, s, 2)`, degree `0` (`s = 0`) or `2` (`s = 1`),
two `i`-forms for `s = 1`, `|σ|_v = 2`. -/
example : tagNZ 2 ![false, true] ![2, 0, 2] = true ∧ tagDeg 2 ![false, true] ![2, 0, 2] = 0 ∧
    tagDeg 2 ![false, true] ![2, 1, 2] = 2 ∧ tagDegI 2 ![false, true] ![2, 1, 2] = 2 ∧
    tagV (n := 2) ![2, 1, 2] = 2 := by
  decide

/-! ### Compiled instances -/

section Checks


/-- `cond_avg_pf` at its equality case: three words `𝐢𝛍` with tags `(0, 1)`. -/
example : 2 * (Finset.univ.filter fun _ : Fin 3 => 1 ≤ 1).card +
        2 * (∑ _r ∈ Finset.univ.filter (fun _ : Fin 3 => 1 = 0), tagMu (n := 1) ![0, 1]) +
        (if dXIof (fun _ : Fin 3 => 1) (fun _ _ => true) (fun _ => ![0, 1]) = 3 then 1 else 0) ≤
      dXof (fun _ : Fin 3 => 1) (fun _ _ => true) (fun _ => ![0, 1]) +
        ∑ _r ∈ Finset.univ.filter (fun _ : Fin 3 => 1 ≤ 1),
          (2 - tagDeg 1 (fun _ => true) ![0, 1]) :=
  cond_avg_pf (fun _ : Fin 3 => 1) (fun _ _ => true) (fun _ => ![0, 1]) (by decide)
    (fun _ => by decide) (fun _ => by decide)

end Checks

end Anisotropic

#print axioms Anisotropic.degTabI
#print axioms Anisotropic.tagDegI
#print axioms Anisotropic.dXIof
#print axioms Anisotropic.tagNZ2
#print axioms Anisotropic.avgCase_one
#print axioms Anisotropic.avgCase_two
#print axioms Anisotropic.avgCase_three
#print axioms Anisotropic.cond_avg_pf
#print axioms Anisotropic.colPoly_bound_two
#print axioms Anisotropic.lem87_avg
