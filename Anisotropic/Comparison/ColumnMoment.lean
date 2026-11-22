module

public import Anisotropic.Comparison.DegreeCount
public import Anisotropic.Comparison.PrelimBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Conditional expectation in the column `μ` and Lemma 8.11 (`colLaw`, `integral_colSplit`, `colPoly_bound`, `lem87`) -/

/-- The law `⊗_j law(X_{jμ})` of the column `μ`; `E_μ` (cond_exp) is integration against it. -/
def colLaw {Ω : Type*} [MeasureSpace Ω] (X : Ω → Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) :
    Measure (Fin M → ℝ) :=
  Measure.pi fun j => entryLaw X (j, μ)

section ColSplit

private theorem columnMoment_updCol_measurable (μ : Fin N) :
    Measurable fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin N) ℝ => updCol q.2 μ q.1 := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun ν => ?_
  by_cases h : ν = μ
  · simp only [updCol, h, ite_true]
    exact (measurable_pi_apply j).comp measurable_fst
  · simp only [updCol, h, ite_false]
    exact (measurable_pi_apply ν).comp ((measurable_pi_apply j).comp measurable_snd)

end ColSplit

/-- `E F(X) = E E_μ F(X)`: the column `μ` is independent of `X^{(μ)}`. -/
theorem integral_colSplit {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N)
    {F : Matrix (Fin M) (Fin N) ℝ → ℂ} (hF : Measurable F)
    (hint : Integrable fun ω => F (X ω)) :
    ∫ ω, F (X ω) = ∫ ω, ∫ y, F (updCol (X ω) μ y) ∂(colLaw X μ) := by
  set Y : Ω → Fin M → ℝ := fun ω j => X ω j μ with hYdef
  set R : Ω → Matrix (Fin M) (Fin N) ℝ := fun ω => updCol (X ω) μ 0 with hRdef
  set Φ : (Fin M → ℝ) × Matrix (Fin M) (Fin N) ℝ → ℂ := fun q => F (updCol q.2 μ q.1) with hΦdef
  have hΦ : Measurable Φ := hF.comp (columnMoment_updCol_measurable μ)
  have hmeas : ∀ (p : Fin M × Fin N), Measurable fun ω => X ω p.1 p.2 :=
    fun p => hX.measurable p.1 p.2
  have hYm : Measurable Y := measurable_pi_iff.mpr fun j => hX.measurable j μ
  have hRm : Measurable R := by
    refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun ν => ?_
    by_cases h : ν = μ
    · simp only [hRdef, updCol, h, ite_true]
      exact measurable_const
    · simp only [hRdef, updCol, h, ite_false]
      exact hX.measurable j ν
  -- the law of the column
  have hcol : iIndepFun (fun j ω => X ω j μ) ℙ :=
    hX.indep.precomp (g := fun j : Fin M => (j, μ)) fun a b h => (Prod.ext_iff.1 h).1
  have hY : (ℙ : Measure Ω).map Y = colLaw X μ :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hX.measurable j μ).aemeasurable)).1 hcol
  -- independence of the column and the rest
  have hind : IndepFun Y R ℙ := by
    let S : Finset (Fin M × Fin N) := Finset.univ.filter fun p => p.2 = μ
    let T : Finset (Fin M × Fin N) := Finset.univ.filter fun p => p.2 ≠ μ
    have hST : Disjoint S T := Finset.disjoint_filter.2 fun _ _ h h' => h' h
    have h0 := hX.indep.indepFun_finset S T hST hmeas
    let φ₁ : (S → ℝ) → Fin M → ℝ := fun u j => u ⟨(j, μ), by simp [S]⟩
    let φ₂ : (T → ℝ) → Matrix (Fin M) (Fin N) ℝ := fun r j ν =>
      if h : ν = μ then 0 else r ⟨(j, ν), by simp [T, h]⟩
    have hφ₁ : Measurable φ₁ := measurable_pi_iff.mpr fun j => measurable_pi_apply _
    have hφ₂ : Measurable φ₂ := by
      refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun ν => ?_
      by_cases h : ν = μ
      · simp only [φ₂, h, dite_true]
        exact measurable_const
      · simp only [φ₂, h, dite_false]
        exact measurable_pi_apply _
    have h1 := h0.comp hφ₁ hφ₂
    have e1 : φ₁ ∘ (fun ω (i : S) => X ω (i : Fin M × Fin N).1 (i : Fin M × Fin N).2) = Y := by
      funext ω j; rfl
    have e2 : φ₂ ∘ (fun ω (i : T) => X ω (i : Fin M × Fin N).1 (i : Fin M × Fin N).2) = R := by
      funext ω j ν
      show (if h : ν = μ then (0 : ℝ) else X ω j ν) = updCol (X ω) μ 0 j ν
      by_cases h : ν = μ <;> simp [updCol, h]
    rw [e1, e2] at h1
    exact h1
  have hprod : (ℙ : Measure Ω).map (fun ω => (Y ω, R ω)) =
      ((ℙ : Measure Ω).map Y).prod ((ℙ : Measure Ω).map R) :=
    (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hRm.aemeasurable).1 hind
  have hpair : Measurable fun ω => (Y ω, R ω) := hYm.prodMk hRm
  have hXR : ∀ ω, updCol (R ω) μ (Y ω) = X ω := by
    intro ω; funext j ν
    by_cases h : ν = μ
    · subst h; simp [updCol, hYdef]
    · simp [hRdef, updCol, h]
  have hRy : ∀ ω y, updCol (R ω) μ y = updCol (X ω) μ y := by
    intro ω y; funext j ν
    by_cases h : ν = μ
    · simp [updCol, h]
    · simp [hRdef, updCol, h]
  have hintΦ : Integrable Φ (((ℙ : Measure Ω).map Y).prod ((ℙ : Measure Ω).map R)) := by
    rw [← hprod]
    refine (integrable_map_measure hΦ.aestronglyMeasurable hpair.aemeasurable).2 ?_
    have : Φ ∘ (fun ω => (Y ω, R ω)) = fun ω => F (X ω) := by
      funext ω; simp only [Function.comp, hΦdef, hXR]
    rw [this]; exact hint
  have hsm : StronglyMeasurable fun r : Matrix (Fin M) (Fin N) ℝ =>
      ∫ y, Φ (y, r) ∂((ℙ : Measure Ω).map Y) :=
    StronglyMeasurable.integral_prod_left (f := fun y r => Φ (y, r)) hΦ.stronglyMeasurable
  calc ∫ ω, F (X ω) = ∫ ω, Φ (Y ω, R ω) := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [hΦdef, hXR]
    _ = ∫ q, Φ q ∂((ℙ : Measure Ω).map fun ω => (Y ω, R ω)) :=
        (integral_map hpair.aemeasurable hΦ.aestronglyMeasurable).symm
    _ = ∫ r, ∫ y, Φ (y, r) ∂((ℙ : Measure Ω).map Y) ∂((ℙ : Measure Ω).map R) := by
        rw [hprod]; exact integral_prod_symm Φ hintΦ
    _ = ∫ ω, ∫ y, Φ (y, R ω) ∂((ℙ : Measure Ω).map Y) :=
        integral_map hRm.aemeasurable hsm.aestronglyMeasurable
    _ = ∫ ω, ∫ y, F (updCol (X ω) μ y) ∂(colLaw X μ) := by
        rw [hY]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [hΦdef, hRy]

section ColPoly

/-- `N^{−1/2} = (√N)⁻¹`. -/
private theorem columnMoment_rpow_eq (N : ℕ) : (N : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), neg_div]

/-- `|E y^m| ≤ C_m N^{−m/2}` under (moments of X-1). -/
private theorem columnMoment_coord {N : ℕ} {C : ℕ → ℝ} {ρ : Measure ℝ} (hN : 1 ≤ N)
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
private theorem columnMoment_monomial {ι : Type*} [Fintype ι] {M N : ℕ} {C : ℕ → ℝ}
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
                    columnMoment_coord hN (hρ x) _
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
private def columnMoment_rep {ι : Type*} {M : ℕ} (J : ι → Fin M) (a : ι) : ι :=
  @Classical.epsilon ι ⟨a⟩ fun a' => J a' = J a

private theorem columnMoment_rep_spec {ι : Type*} {M : ℕ} (J : ι → Fin M) (a : ι) :
    J (columnMoment_rep J a) = J a :=
  @Classical.epsilon_spec ι (fun a' => J a' = J a) ⟨a, rfl⟩

private theorem columnMoment_rep_congr {ι : Type*} {M : ℕ} (J : ι → Fin M) {a b : ι}
    (h : J a = J b) : columnMoment_rep J a = columnMoment_rep J b := by
  unfold columnMoment_rep
  simp only [h]

/-- Summing a product weight over the tuples `J` that are constant on the fibres of an idempotent
`f`: the sum factorises over the representatives `r = f r`. -/
private theorem columnMoment_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
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

/-- The power count after (730): for blocks `r` of sizes `s_r ≥ 2` containing `d_r ≤ s_r` linear
indices, `∏_r N^{1 − s_r/2} b^{d_r ∧ 2} ≤ b^d`, and `≤ N^{−1/2} b^{d − [d ≥ 3]}` if `d` is odd
(here `β = N^{−1/2} ≤ b ≤ 1`). -/
private theorem columnMoment_exp {α : Type*} (L : Finset α) (s dd : α → ℕ)
    (hs : ∀ r ∈ L, 2 ≤ s r) (hds : ∀ r ∈ L, dd r ≤ s r) {d k : ℕ}
    (hsum_s : ∑ r ∈ L, s r = d + 2 * k) (hsum_d : ∑ r ∈ L, dd r = d) {β b : ℝ}
    (hβ : 0 < β) (hβb : β ≤ b) (hb : b ≤ 1) :
    ∏ r ∈ L, (β ^ (s r - 2) * b ^ min (dd r) 2) ≤
      if Odd d then β * b ^ (d - if 3 ≤ d then 1 else 0) else b ^ d := by
  have hb0 : 0 ≤ b := hβ.le.trans hβb
  have hfac : ∀ r ∈ L, β ^ (s r - 2) * b ^ min (dd r) 2 ≤ b ^ dd r := by
    intro r hr
    calc β ^ (s r - 2) * b ^ min (dd r) 2 ≤ b ^ (s r - 2) * b ^ min (dd r) 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ.le hβb _) (pow_nonneg hb0 _)
      _ = b ^ (s r - 2 + min (dd r) 2) := (pow_add _ _ _).symm
      _ ≤ b ^ dd r := pow_le_pow_of_le_one hb0 hb (by
          have := hs r hr; have := hds r hr; omega)
  have hnn : ∀ r ∈ L, 0 ≤ β ^ (s r - 2) * b ^ min (dd r) 2 := fun r _ => by positivity
  have hall : ∏ r ∈ L, (β ^ (s r - 2) * b ^ min (dd r) 2) ≤ b ^ d := by
    calc _ ≤ ∏ r ∈ L, b ^ dd r := Finset.prod_le_prod₀ hnn hfac
      _ = b ^ d := by rw [Finset.prod_pow_eq_pow_sum, hsum_d]
  by_cases hd : Odd d
  · simp only [hd, ↓reduceIte]
    obtain ⟨r0, hr0, hodd⟩ : ∃ r ∈ L, Odd (s r) := by
      by_contra hne
      simp only [not_exists, not_and] at hne
      have : Even (∑ r ∈ L, s r) :=
        Finset.even_sum _ fun r hr => Nat.not_odd_iff_even.1 (hne r hr)
      rw [hsum_s] at this
      exact (Nat.not_even_iff_odd.2 (hd.add_even (even_two_mul k))) this
    have hdr0 : dd r0 ≤ d := hsum_d ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr0
    have h3 : 3 ≤ s r0 := by
      have := hs r0 hr0; obtain ⟨m, hm⟩ := hodd; omega
    set e : ℕ := if 2 ≤ dd r0 then 1 else 0 with he_def
    set e' : ℕ := if 3 ≤ d then 1 else 0 with he'_def
    have he : e ≤ dd r0 := by simp only [e]; split_ifs <;> omega
    have hee' : e ≤ e' := by
      obtain ⟨m, hm⟩ := hd
      simp only [e, e']; split_ifs <;> omega
    have hf0 : β ^ (s r0 - 2) * b ^ min (dd r0) 2 ≤ β * b ^ (dd r0 - e) := by
      have hsplit : s r0 - 2 = (s r0 - 3) + 1 := by omega
      calc β ^ (s r0 - 2) * b ^ min (dd r0) 2 = β * (β ^ (s r0 - 3) * b ^ min (dd r0) 2) := by
            rw [hsplit, pow_succ]; ring
        _ ≤ β * (b ^ (s r0 - 3) * b ^ min (dd r0) 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hβ.le hβb _) (pow_nonneg hb0 _)) hβ.le
        _ = β * b ^ (s r0 - 3 + min (dd r0) 2) := by rw [pow_add]
        _ ≤ β * b ^ (dd r0 - e) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0 hb (by
            have := hds r0 hr0; simp only [e]; split_ifs <;> omega)) hβ.le
    have hrest : ∏ r ∈ L.erase r0, (β ^ (s r - 2) * b ^ min (dd r) 2) ≤ b ^ (d - dd r0) := by
      calc _ ≤ ∏ r ∈ L.erase r0, b ^ dd r :=
            Finset.prod_le_prod₀ (fun r hr => hnn r (Finset.mem_of_mem_erase hr))
              (fun r hr => hfac r (Finset.mem_of_mem_erase hr))
        _ = b ^ (d - dd r0) := by
            rw [Finset.prod_pow_eq_pow_sum]; congr 1
            have := Finset.add_sum_erase L dd hr0
            omega
    calc ∏ r ∈ L, (β ^ (s r - 2) * b ^ min (dd r) 2)
        = (β ^ (s r0 - 2) * b ^ min (dd r0) 2) *
            ∏ r ∈ L.erase r0, (β ^ (s r - 2) * b ^ min (dd r) 2) :=
          (Finset.mul_prod_erase L _ hr0).symm
      _ ≤ (β * b ^ (dd r0 - e)) * b ^ (d - dd r0) :=
          mul_le_mul hf0 hrest (Finset.prod_nonneg fun r hr => hnn r (Finset.mem_of_mem_erase hr))
            (by positivity)
      _ = β * b ^ (d - e) := by
          rw [mul_assoc, ← pow_add]; congr 2; omega
      _ ≤ β * b ^ (d - e') :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0 hb (by omega)) hβ.le
  · simp only [hd, ↓reduceIte]; exact hall

/-- `∏_{l ∈ s} a_l ≤ ∑_{l ∈ s} a_l^{|s|}` for `a ≥ 0`, `s ≠ ∅`. -/
private theorem columnMoment_prod_le_sum_pow {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (a : α → ℝ) (ha : ∀ l, 0 ≤ a l) : ∏ l ∈ s, a l ≤ ∑ l ∈ s, a l ^ s.card := by
  obtain ⟨l0, hl0, hmax⟩ := s.exists_max_image a hs
  calc ∏ l ∈ s, a l ≤ ∏ l ∈ s, a l0 := Finset.prod_le_prod₀ (fun l _ => ha l) hmax
    _ = a l0 ^ s.card := Finset.prod_const _
    _ ≤ ∑ l ∈ s, a l ^ s.card :=
        Finset.single_le_sum (f := fun l => a l ^ s.card) (fun l _ => pow_nonneg (ha l) _) hl0

/-- One block of (730): `∑_j ∏_{l ∈ s} |c_{lj}| ≤ (|s| + 1) τ'⁻¹ N b^{|s| ∧ 2} K^{|s| − 2}`
with `τ' = min(τ, 1)`, from (bound_sum_hat). -/
private theorem columnMoment_block {M N d : ℕ} {τ K b : ℝ} (hτ : 0 < τ) (hK : 1 ≤ K)
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
          Finset.sum_le_sum fun j _ => columnMoment_prod_le_sum_pow s h _ fun _ => norm_nonneg _
      _ = ∑ l ∈ s, ∑ j, ‖c l j‖ ^ s.card := Finset.sum_comm
      _ ≤ ∑ l ∈ s, ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) :=
          Finset.sum_le_sum fun l _ =>
            bound_sum_hat hτ' (min_le_right _ _) hK hb hM' (c l) (hc l) (hc2 l) s.card
      _ = s.card * ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card + 1) * ((min τ 1)⁻¹ * N * b ^ min s.card 2 * K ^ (s.card - 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hB

/-- The expansion (prod_pA1) of `∏_l L_l ∏_t Q_t` over index tuples
`J : Fin d ⊕ (Fin k ⊕ Fin k) → Fin M`. -/
private theorem columnMoment_expand {M d k : ℕ} (c : Fin d → Fin M → ℂ)
    (B : Fin k → Fin M → Fin M → ℂ) (y : Fin M → ℝ) :
    (∏ l, ∑ j, c l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
      ∑ J : Fin d ⊕ (Fin k ⊕ Fin k) → Fin M,
        ((∏ l, c l (J (Sum.inl l))) *
          ∏ t, B t (J (Sum.inr (Sum.inl t))) (J (Sum.inr (Sum.inr t)))) *
          ((∏ a, y (J a) : ℝ) : ℂ) := by
  have h1 : ∏ l, ∑ j, c l j * (y j : ℂ) = ∑ u : Fin d → Fin M, ∏ l, (c l (u l) * (y (u l) : ℂ)) :=
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
    ← (Equiv.sumArrowEquivProdArrow (Fin d) (Fin k ⊕ Fin k) (Fin M)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Fintype.prod_sum_type, Complex.ofReal_mul,
    Complex.ofReal_prod, Finset.prod_mul_distrib]
  ring

end ColPoly


/-- Lemma 8.11 (`lem:87`), deterministic core: for independent centred coordinates with
`E|√N y_j|^n ≤ C_n`, linear forms `∑_j c_{lj} y_j` (`l < d`) and quadratic forms
`∑_{j,j'} y_j B_{tjj'} y_{j'}` (`t < k`) with entries at most `K` and `∑_j |c_{lj}|² ≤ N b²`:
`|E ∏ ∏| ≤ K' K^{d+k} b^d`, and `≤ K' K^{d+k} N^{−1/2} b^{d − [d ≥ 3]}` when `d` is odd. -/
theorem colPoly_bound (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (d k : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)]
      (c : Fin d → Fin M → ℂ) (B : Fin k → Fin M → Fin M → ℂ) (K b : ℝ),
      1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ K → (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b → b ≤ 1 →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ l j, ‖c l j‖ ≤ K) → (∀ t j j', ‖B t j j'‖ ≤ K) → (∀ l, ∑ j, ‖c l j‖ ^ 2 ≤ N * b ^ 2) →
      ‖∫ y, (∏ l, ∑ j, c l j * (y j : ℂ)) * ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j'
          ∂(Measure.pi ρ)‖ ≤
        K' * K ^ (d + k) *
          (if Odd d then (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (d - if 3 ≤ d then 1 else 0)
            else b ^ d) := by
  set n : ℕ := d + 2 * k with hn
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
  intro M N ρ _ c B K b hN hM hK hβb hb1 hmean hρ hc hB hc2
  set β : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hβdef
  have hβ : β = (Real.sqrt N)⁻¹ := columnMoment_rpow_eq N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβpos : 0 < β := by rw [hβ]; exact inv_pos.2 (Real.sqrt_pos.2 hNpos)
  have hβ0 : 0 ≤ β := hβpos.le
  have hβN : β ^ 2 * N = 1 := by
    rw [hβ, inv_pow, Real.sq_sqrt hNpos.le, inv_mul_cancel₀ hNpos.ne']
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hb0 : 0 ≤ b := hβ0.trans hβb
  set tgt : ℝ := if Odd d then β * b ^ (d - if 3 ≤ d then 1 else 0) else b ^ d with htgt
  have htgt0 : 0 ≤ tgt := by
    rw [htgt]; by_cases hd : Odd d
    · simp only [hd, ↓reduceIte]; exact mul_nonneg hβ0 (pow_nonneg hb0 _)
    · simp only [hd, ↓reduceIte]; exact pow_nonneg hb0 _
  -- the index tuples
  let ι := Fin d ⊕ (Fin k ⊕ Fin k)
  have hcard : Fintype.card ι = n := by
    simp only [ι, Fintype.card_sum, Fintype.card_fin]; omega
  let coef : (ι → Fin M) → ℂ := fun J =>
    (∏ l, c l (J (Sum.inl l))) * ∏ t, B t (J (Sum.inr (Sum.inl t))) (J (Sum.inr (Sum.inr t)))
  let w : ι → Fin M → ℝ := Sum.elim (fun l x => ‖c l x‖) (fun _ _ => 1)
  have hw : ∀ a x, 0 ≤ w a x := by intro a x; cases a <;> simp [w]
  let F : (ι → Fin M) → ℝ := fun J => ∏ a, w a (J a)
  have hF0 : ∀ J, 0 ≤ F J := fun J => Finset.prod_nonneg fun a _ => hw _ _
  have hcoef : ∀ J, ‖coef J‖ ≤ K ^ k * F J := by
    intro J
    have hFJ : F J = ∏ l, ‖c l (J (Sum.inl l))‖ := by
      show ∏ a : Fin d ⊕ (Fin k ⊕ Fin k), w a (J a) = _
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
  have hmono := fun J => columnMoment_monomial (ι := ι) ρ hN hmean hρ hD1
    (by rw [hcard]; exact hD) J
  -- the integral as a sum over index tuples
  have hint_eq : ∫ y, (∏ l, ∑ j, c l j * (y j : ℂ)) *
      ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' ∂(Measure.pi ρ) =
      ∑ J : ι → Fin M, coef J * ((∫ y, ∏ a, y (J a) ∂(Measure.pi ρ) : ℝ) : ℂ) := by
    have hexp : ∀ y : Fin M → ℝ, (∏ l, ∑ j, c l j * (y j : ℂ)) *
        ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j' =
        ∑ J : ι → Fin M, coef J * ((∏ a, y (J a) : ℝ) : ℂ) := fun y => columnMoment_expand c B y
    rw [show (fun y : Fin M → ℝ => (∏ l, ∑ j, c l j * (y j : ℂ)) *
        ∏ t, ∑ j, ∑ j', (y j : ℂ) * B t j j' * y j') =
        fun y => ∑ J : ι → Fin M, coef J * ((∏ a, y (J a) : ℝ) : ℂ) from funext hexp]
    rw [integral_finsetSum _ fun J _ => ?_]
    · refine Finset.sum_congr rfl fun J _ => ?_
      rw [integral_const_mul, integral_complex_ofReal]
    · exact ((hmono J).1.ofReal (𝕜 := ℂ)).const_mul (coef J)
  -- one pattern of coincidences
  have hpat : ∀ f : ι → ι,
      ∑ J ∈ (Finset.univ.filter P).filter (fun J => columnMoment_rep J = f), F J * β ^ n ≤
        (((n : ℝ) + 1) * T) ^ n * K ^ d * tgt := by
    intro f
    have hR0 : 0 ≤ (((n : ℝ) + 1) * T) ^ n * K ^ d * tgt :=
      mul_nonneg (mul_nonneg (pow_nonneg hnT _) (pow_nonneg hK0 _)) htgt0
    by_cases hne : ((Finset.univ.filter P).filter (fun J => columnMoment_rep J = f)).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]; exact hR0
    obtain ⟨J0, hJ0⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ0
    obtain ⟨hPJ0, hf⟩ := hJ0
    have hidem : ∀ a, f (f a) = f a := by
      intro a; rw [← hf]; exact columnMoment_rep_congr J0 (columnMoment_rep_spec J0 a)
    have hs : ∀ J ∈ (Finset.univ.filter P).filter (fun J => columnMoment_rep J = f),
        ∀ a, J (f a) = J a := by
      intro J hJ a; rw [← (Finset.mem_filter.1 hJ).2]; exact columnMoment_rep_spec J a
    have hfib := columnMoment_fiber w hw f hidem _ hs
    rw [← Finset.sum_mul]
    set L := Finset.univ.filter fun r => f r = r with hL
    set sz : ι → ℕ := fun r => (Finset.univ.filter fun a => f a = r).card with hsz
    set dd : ι → ℕ := fun r => (Finset.univ.filter fun l : Fin d => f (Sum.inl l) = r).card
      with hdd_def
    have hiff : ∀ r ∈ L, ∀ a, f a = r ↔ J0 a = J0 r := by
      intro r hr a
      have hr' : f r = r := (Finset.mem_filter.1 hr).2
      constructor
      · intro h
        have := columnMoment_rep_spec J0 a
        rw [hf, h] at this; exact this.symm
      · intro h
        rw [← hf] at hr' ⊢; rw [columnMoment_rep_congr J0 h]; exact hr'
    have hsz2 : ∀ r ∈ L, 2 ≤ sz r := by
      intro r hr
      have heq : (Finset.univ.filter fun a => f a = r) =
          Finset.univ.filter fun a => J0 a = J0 r := Finset.filter_congr fun a _ => hiff r hr a
      have h1 : (Finset.univ.filter fun a => J0 a = J0 r).card ≠ 1 := hPJ0 (J0 r)
      have h2 : 0 < (Finset.univ.filter fun a => J0 a = J0 r).card :=
        Finset.card_pos.2 ⟨r, by simp⟩
      show 2 ≤ (Finset.univ.filter fun a => f a = r).card
      rw [heq]; omega
    have hmaps : ∀ a, f a ∈ L := fun a => Finset.mem_filter.2 ⟨Finset.mem_univ _, hidem a⟩
    have hsum_sz : ∑ r ∈ L, sz r = d + 2 * k := by
      have := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := L)
        (fun a _ => hmaps a)
      rw [Finset.card_univ, hcard] at this; exact this.symm
    have hsum_dd : ∑ r ∈ L, dd r = d := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun l : Fin d => f (Sum.inl l))
        (s := Finset.univ) (t := L) (fun l _ => hmaps _)
      rw [Finset.card_univ, Fintype.card_fin] at this; exact this.symm
    have hdd : ∀ r ∈ L, dd r ≤ sz r := fun r _ =>
      Finset.card_le_card_of_injOn Sum.inl (fun l hl => by simpa using hl)
        (fun _ _ _ _ h => Sum.inl_injective h)
    have hddn : ∀ r, dd r ≤ n := fun r => by
      have : dd r ≤ d := by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin d))
          (fun l : Fin d => f (Sum.inl l) = r)
      omega
    have hSr : ∀ r, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x =
        ∑ x, ∏ l ∈ Finset.univ.filter (fun l : Fin d => f (Sum.inl l) = r), ‖c l x‖ := by
      intro r; refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type]
      simp [w]
    have hblock : ∀ r ∈ L, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x ≤
        ((n : ℝ) + 1) * (T * N * b ^ min (dd r) 2 * K ^ (dd r - 2)) := by
      intro r hr
      rw [hSr]
      refine (columnMoment_block hτ hK hb0 hM c hc hc2 _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by
        exact mul_nonneg (mul_nonneg (mul_nonneg hT0 hNpos.le) (pow_nonneg hb0 _))
          (pow_nonneg hK0 _))
      have := hddn r
      have : ((dd r : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      simp only [hdd_def] at this ⊢
      linarith
    have hβn : β ^ n = ∏ r ∈ L, β ^ sz r := by rw [Finset.prod_pow_eq_pow_sum, hsum_sz]
    calc _ ≤ (∏ r ∈ L, ∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ n :=
          mul_le_mul_of_nonneg_right hfib (pow_nonneg hβ0 _)
      _ = ∏ r ∈ L, ((∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ sz r) := by
          rw [hβn, ← Finset.prod_mul_distrib]
      _ ≤ ∏ r ∈ L, ((((n : ℝ) + 1) * T * K ^ (dd r - 2)) *
            (β ^ (sz r - 2) * b ^ min (dd r) 2)) := by
          refine Finset.prod_le_prod₀ (fun r _ => mul_nonneg (Finset.sum_nonneg fun x _ =>
            Finset.prod_nonneg fun a _ => hw _ _) (pow_nonneg hβ0 _)) fun r hr => ?_
          obtain ⟨m, hm⟩ : ∃ m, sz r = m + 2 := ⟨sz r - 2, by have := hsz2 r hr; omega⟩
          have hpow : β ^ sz r * N = β ^ (sz r - 2) := by
            rw [hm, Nat.add_sub_cancel, pow_add, mul_assoc, hβN, mul_one]
          calc (∑ x, ∏ a ∈ Finset.univ.filter (fun a => f a = r), w a x) * β ^ sz r
              ≤ (((n : ℝ) + 1) * (T * N * b ^ min (dd r) 2 * K ^ (dd r - 2))) * β ^ sz r :=
                mul_le_mul_of_nonneg_right (hblock r hr) (pow_nonneg hβ0 _)
            _ = (((n : ℝ) + 1) * T * K ^ (dd r - 2)) * (b ^ min (dd r) 2 * (β ^ sz r * N)) := by
                ring
            _ = _ := by rw [hpow]; ring
      _ = (∏ r ∈ L, (((n : ℝ) + 1) * T * K ^ (dd r - 2))) *
            ∏ r ∈ L, (β ^ (sz r - 2) * b ^ min (dd r) 2) := Finset.prod_mul_distrib
      _ ≤ ((((n : ℝ) + 1) * T) ^ n * K ^ d) * tgt := by
          refine mul_le_mul ?_ (columnMoment_exp L sz dd hsz2 hdd hsum_sz hsum_dd hβpos hβb hb1)
            (Finset.prod_nonneg fun r _ => mul_nonneg (pow_nonneg hβ0 _) (pow_nonneg hb0 _))
            (mul_nonneg (pow_nonneg hnT _) (pow_nonneg hK0 _))
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
          have hL1 : 1 ≤ ((n : ℝ) + 1) * T := by
            have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
            nlinarith
          refine mul_le_mul (pow_le_pow_right₀ hL1 ?_) (pow_le_pow_right₀ hK ?_)
            (pow_nonneg hK0 _) (pow_nonneg hnT _)
          · rw [← hcard]; exact Finset.card_le_univ L
          · exact (Finset.sum_le_sum fun r _ => Nat.sub_le _ _).trans hsum_dd.le
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
        show K ^ k * F J * (D * β) ^ n = K ^ k * D ^ n * (F J * β ^ n)
        rw [mul_pow]; ring
    _ = K ^ k * D ^ n * ∑ f : ι → ι,
          ∑ J ∈ (Finset.univ.filter P).filter (fun J => columnMoment_rep J = f), F J * β ^ n := by
        rw [Finset.sum_fiberwise]
    _ ≤ K ^ k * D ^ n * ∑ _f : ι → ι, ((((n : ℝ) + 1) * T) ^ n * K ^ d * tgt) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hpat f)
          (mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hD0 _))
    _ = (n : ℝ) ^ n * D ^ n * (((n : ℝ) + 1) * T) ^ n * K ^ (d + k) * tgt := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, hcard, nsmul_eq_mul, pow_add]
        push_cast
        ring

section Lem87

private theorem columnMoment_degTab_le (x y : Letter) (s : Fin 3) : degTab x y s ≤ 2 := by
  revert x y s; decide

/-- `deg A(w, σ) ≤ 2 (n(w) + 1)`. -/
private theorem columnMoment_tagDeg_le (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagDeg n w σ ≤ 2 * (n + 1) := by
  cases n with
  | zero => simp only [tagDeg]; split_ifs <;> omega
  | succ k =>
    simp only [tagDeg]
    calc ∑ l, degTab (factorX w l) (factorY w l) (σ l) ≤ ∑ _l : Fin (k + 2), 2 :=
          Finset.sum_le_sum fun l _ => columnMoment_degTab_le _ _ _
      _ = 2 * (k + 1 + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

/-- Coefficient vectors with entries at most `2K` and `∑_j |c_j|² ≤ 4 N b²`. -/
private def columnMoment_good (K b : ℝ) (N : ℕ) (c : Fin M → ℂ) : Prop :=
  (∀ j, ‖c j‖ ≤ 2 * K) ∧ ∑ j, ‖c j‖ ^ 2 ≤ 4 * (N * b ^ 2)

private theorem columnMoment_good_of {K b : ℝ} {c : Fin M → ℂ} (hK : 0 ≤ K)
    (h1 : ∀ j, ‖c j‖ ≤ K) (h2 : ∑ j, ‖c j‖ ^ 2 ≤ N * b ^ 2) : columnMoment_good K b N c := by
  have : (0 : ℝ) ≤ N * b ^ 2 := by positivity
  exact ⟨fun j => (h1 j).trans (by linarith), h2.trans (by linarith)⟩

/-- On `GoodMinor`, every coefficient vector of `A⁺(w, σ)` is good. -/
private theorem columnMoment_forms_good {K b : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hG : GoodMinor K b Sig A z v μ) (hK : 0 ≤ K) (i : Fin M) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) :
    ∀ c ∈ tagForms Sig A z v i μ n w σ, columnMoment_good K b N c := by
  have hvc : columnMoment_good K b N (colC Sig A z (vbar Sig v) μ) :=
    columnMoment_good_of hK (fun j => (hG.ent_vj j).1) hG.ward_v.1
  have hvr : columnMoment_good K b N (rowC Sig A z (vbar Sig v) μ) :=
    columnMoment_good_of hK (fun j => (hG.ent_vj j).2) hG.ward_v.2
  have hic : columnMoment_good K b N (colC Sig A z (eI (Sum.inl i)) μ) := by
    have e : ∀ j, colC Sig A z (eI (Sum.inl i)) μ j = Gmu Sig A z μ (Sum.inl i) (Sum.inl j) :=
      fun j => ent_eI_eI _ _ _
    exact columnMoment_good_of hK (fun j => by rw [e]; exact hG.ent_jk i j)
      (by simp only [e]; exact (hG.ward_j i).1)
  have hir : columnMoment_good K b N (rowC Sig A z (eI (Sum.inl i)) μ) := by
    have e : ∀ j, rowC Sig A z (eI (Sum.inl i)) μ j = Gmu Sig A z μ (Sum.inl j) (Sum.inl i) :=
      fun j => ent_eI_eI _ _ _
    exact columnMoment_good_of hK (fun j => by rw [e]; exact hG.ent_jk j i)
      (by simp only [e]; exact (hG.ward_j i).2)
  have hsum : columnMoment_good K b N
      (colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) := by
    refine ⟨fun j => ?_, ?_⟩
    · calc ‖(colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) j‖
          ≤ ‖colC Sig A z (vbar Sig v) μ j‖ + ‖rowC Sig A z (vbar Sig v) μ j‖ := norm_add_le _ _
        _ ≤ K + K := add_le_add (hG.ent_vj j).1 (hG.ent_vj j).2
        _ = 2 * K := by ring
    · calc ∑ j, ‖(colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) j‖ ^ 2
          ≤ ∑ j, (2 * ‖colC Sig A z (vbar Sig v) μ j‖ ^ 2 +
              2 * ‖rowC Sig A z (vbar Sig v) μ j‖ ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h := norm_add_le (colC Sig A z (vbar Sig v) μ j) (rowC Sig A z (vbar Sig v) μ j)
            have h0 := norm_nonneg (colC Sig A z (vbar Sig v) μ j + rowC Sig A z (vbar Sig v) μ j)
            have ha := norm_nonneg (colC Sig A z (vbar Sig v) μ j)
            have hb := norm_nonneg (rowC Sig A z (vbar Sig v) μ j)
            simp only [Pi.add_apply]
            nlinarith [sq_nonneg
              (‖colC Sig A z (vbar Sig v) μ j‖ - ‖rowC Sig A z (vbar Sig v) μ j‖)]
        _ = 2 * ∑ j, ‖colC Sig A z (vbar Sig v) μ j‖ ^ 2 +
              2 * ∑ j, ‖rowC Sig A z (vbar Sig v) μ j‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * (N * b ^ 2) + 2 * (N * b ^ 2) := by linarith [hG.ward_v.1, hG.ward_v.2]
        _ = 4 * (N * b ^ 2) := by ring
  have hcolL : ∀ x : Letter, x ≠ .M →
      columnMoment_good K b N (colC Sig A z (letVec Sig v i μ x) μ) := by
    intro x hx; cases x
    · exact hvc
    · exact hic
    · exact absurd rfl hx
  have hrowL : ∀ x : Letter, x ≠ .M →
      columnMoment_good K b N (rowC Sig A z (letVec Sig v i μ x) μ) := by
    intro x hx; cases x
    · exact hvr
    · exact hir
    · exact absurd rfl hx
  intro c hc
  cases n with
  | zero =>
    simp only [tagForms, emptyForms] at hc
    split_ifs at hc <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl
      · exact hvc
      · exact hvr
    · subst hc; exact hsum
  | succ k =>
    simp only [tagForms, List.mem_flatten, List.mem_ofFn] at hc
    obtain ⟨L, ⟨l, rfl⟩, hcL⟩ := hc
    simp only [brackForms] at hcL
    split_ifs at hcL <;>
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.nil_append, List.append_nil] at hcL <;>
      rcases hcL with rfl | rfl <;>
      first | with_reducible exact hcolL _ ‹_› | with_reducible exact hrowL _ ‹_›

/-- `(L.map (linForm · y)).prod = ∏_{l < d} linForm(L_l, y)` for a list of length `d`. -/
private theorem columnMoment_list_prod {d : ℕ} (Ls : List (Fin M → ℂ)) (h : Ls.length = d)
    (g : (Fin M → ℂ) → ℂ) : (Ls.map g).prod = ∏ l : Fin d, g (Ls.get (Fin.cast h.symm l)) := by
  subst h
  conv_lhs => rw [← List.ofFn_get Ls]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- `conj` passes to the coefficients of a product of linear forms of a real vector. -/
private theorem columnMoment_conj_prod (b : Bool) (L : List (Fin M → ℂ)) (y : Fin M → ℝ) :
    conjIf b ((L.map fun c => linForm c y).prod) =
      ((L.map fun c j => conjIf b (c j)).map fun c => linForm c y).prod := by
  cases b
  · simp [conjIf]
  · simp only [conjIf, ite_true, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp [linForm, map_sum, map_mul, Complex.conj_ofReal]

/-- `Q_μ` at the column `y`, possibly conjugated, as a quadratic form in `y`. -/
private theorem columnMoment_conj_Qmu (b : Bool) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (y : Fin M → ℝ) :
    conjIf b (Qmu Sig (updCol A μ y) z μ) =
      ∑ j, ∑ j', (y j : ℂ) * conjIf b (Gmu Sig A z μ (Sum.inl j) (Sum.inl j')) * y j' := by
  rw [Qmu_updCol]
  cases b
  · simp [conjIf]
  · simp [conjIf, map_sum, map_mul, Complex.conj_ofReal]

end Lem87

/-- Lemma 8.11 (`lem:87`) for tagged words: on `GoodMinor` with `K = N^κ`, the conditional
expectation of `∏_r A⁺(w_r, σ_r) ∏_{t<k} Q_μ` (each factor possibly conjugated) is at most
`K' K^{d_X + k} N^{−[d_v = 0]/2} b^{d_X − [d_X ≥ 3][d_v = 0]}` (with the factor `K^{d_X+k}`
explicit). -/
theorem lem87 (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p k : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
      (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (ρ : Fin M → Measure ℝ)
      [∀ j, IsProbabilityMeasure (ρ j)] (K b : ℝ),
      1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ K → (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b → b ≤ 1 →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      GoodMinor K b Sig A z v μ →
      ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
        (cs : Fin p → Bool) (ct : Fin k → Bool), ∑ r, ns r = 3 →
        (∀ r, tagNZ (ns r) (ws r) (σs r) = true) →
        ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
            fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)
            ∂(Measure.pi ρ)‖ ≤
          K' * K ^ (dXof ns ws σs + k) *
            (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
                b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0)
              else b ^ dXof ns ws σs) := by
  choose Kf hKf0 hKf using fun d : ℕ => colPoly_bound C τ hτ d k
  refine ⟨∑ d ∈ Finset.range (2 * p + 7), 2 ^ d * Kf d,
    Finset.sum_nonneg fun d _ => mul_nonneg (by positivity) (hKf0 d), ?_⟩
  intro M N Sig A z v i μ ρ _ K b hN hM hK hβb hb1 hmean hρ hG ns ws σs cs ct hns hnz
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  set β : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hβdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hNpos.le _
  have hβ1 : β ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have hb0 : 0 ≤ b := hβ0.trans hβb
  set dX : ℕ := dXof ns ws σs with hdX
  set Lr : Fin p → List (Fin M → ℂ) := fun r => tagForms Sig A z v i μ (ns r) (ws r) (σs r)
    with hLr
  set Ls : List (Fin M → ℂ) :=
    (List.ofFn fun r => (Lr r).map fun c j => conjIf (cs r) (c j)).flatten with hLs
  have hlen : Ls.length = dX := by
    simp only [Ls, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      List.length_map, Lr, tagForms_length, dX, dXof]
  let c' : Fin dX → Fin M → ℂ := fun l j => (1 / 2 : ℂ) * Ls.get (Fin.cast hlen.symm l) j
  let B' : Fin k → Fin M → Fin M → ℂ := fun t j j' =>
    conjIf (ct t) (Gmu Sig A z μ (Sum.inl j) (Sum.inl j'))
  -- the forms of `Ls` are good
  have hLs_good : ∀ c ∈ Ls, columnMoment_good K b N c := by
    intro c hc
    simp only [Ls, List.mem_flatten, List.mem_ofFn] at hc
    obtain ⟨L, ⟨r, rfl⟩, hcL⟩ := hc
    simp only [List.mem_map] at hcL
    obtain ⟨c0, hc0, rfl⟩ := hcL
    obtain ⟨h1, h2⟩ := columnMoment_forms_good hG hK0 i (ns r) (ws r) (σs r) c0 hc0
    have hn : ∀ j, ‖conjIf (cs r) (c0 j)‖ = ‖c0 j‖ := fun j => by
      cases cs r <;> simp [conjIf]
    exact ⟨fun j => by rw [hn]; exact h1 j, by simp only [hn]; exact h2⟩
  have hc' : ∀ l j, ‖c' l j‖ ≤ K := by
    intro l j
    have := (hLs_good _ (List.get_mem Ls (Fin.cast hlen.symm l))).1 j
    simp only [c', norm_mul]
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linarith
  have hc2' : ∀ l, ∑ j, ‖c' l j‖ ^ 2 ≤ N * b ^ 2 := by
    intro l
    have := (hLs_good _ (List.get_mem Ls (Fin.cast hlen.symm l))).2
    simp only [c', norm_mul, mul_pow]
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, ← Finset.mul_sum]
    linarith
  have hB' : ∀ t j j', ‖B' t j j'‖ ≤ K := by
    intro t j j'
    have := hG.ent_jk j j'
    simp only [B']
    cases ct t <;> simpa [conjIf] using this
  -- the integrand
  have hint : ∀ y : Fin M → ℝ,
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) =
        (2 : ℂ) ^ dX * ((∏ l, ∑ j, c' l j * (y j : ℂ)) *
          ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j') := by
    intro y
    have h1 : ∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
        fun c => linForm c y).prod) = (Ls.map fun c => linForm c y).prod := by
      simp only [Ls, List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn,
        Function.comp_def]
      exact Finset.prod_congr rfl fun r _ => columnMoment_conj_prod (cs r) _ y
    have h2 : (Ls.map fun c => linForm c y).prod =
        (2 : ℂ) ^ dX * ∏ l, ∑ j, c' l j * (y j : ℂ) := by
      rw [columnMoment_list_prod Ls hlen,
        show (2 : ℂ) ^ dX = ∏ _l : Fin dX, (2 : ℂ) by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [linForm, c', Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) =
        ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j' :=
      Finset.prod_congr rfl fun t _ => columnMoment_conj_Qmu (ct t) Sig A z μ y
    rw [h1, h2, h3, mul_assoc]
  have hcp := hKf dX M N ρ c' B' K b hN hM hK hβb hb1 hmean hρ hc' hB' hc2'
  -- `d_X ≤ 2p + 6`
  have hdXle : dX ≤ 2 * p + 6 := by
    calc dX = ∑ r, tagDeg (ns r) (ws r) (σs r) := rfl
      _ ≤ ∑ r, 2 * (ns r + 1) := Finset.sum_le_sum fun r _ => columnMoment_tagDeg_le _ _ _
      _ = 2 * p + 6 := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hns, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]; ring
  have hKle : 2 ^ dX * Kf dX ≤ ∑ d ∈ Finset.range (2 * p + 7), 2 ^ d * Kf d :=
    Finset.single_le_sum (f := fun d => 2 ^ d * Kf d)
      (fun d _ => mul_nonneg (by positivity) (hKf0 d)) (Finset.mem_range.2 (by omega))
  -- the power of `b`
  set tO : ℝ := if Odd dX then β * b ^ (dX - if 3 ≤ dX then 1 else 0) else b ^ dX with htO
  set tV : ℝ := if dVof σs = 0 then β * b ^ (dX - if 3 ≤ dX then 1 else 0) else b ^ dX
    with htV
  have htO0 : 0 ≤ tO := by
    rw [htO]; by_cases hd : Odd dX
    · simp only [hd, ↓reduceIte]; exact mul_nonneg hβ0 (pow_nonneg hb0 _)
    · simp only [hd, ↓reduceIte]; exact pow_nonneg hb0 _
  have htOV : tO ≤ tV := by
    rw [htO, htV]
    by_cases hv : dVof σs = 0
    · have hodd : Odd dX := dX_odd ns ws σs hns hnz hv
      simp only [hv, hodd, ↓reduceIte, le_refl]
    · simp only [hv, ↓reduceIte]
      by_cases hd : Odd dX
      · simp only [hd, ↓reduceIte]
        by_cases h3 : 3 ≤ dX
        · simp only [h3, ↓reduceIte]
          calc β * b ^ (dX - 1) ≤ b * b ^ (dX - 1) :=
                mul_le_mul_of_nonneg_right hβb (pow_nonneg hb0 _)
            _ = b ^ dX := by
                rw [← pow_succ']; congr 1; omega
        · simp only [h3, ↓reduceIte, Nat.sub_zero]
          calc β * b ^ dX ≤ 1 * b ^ dX := mul_le_mul_of_nonneg_right hβ1 (pow_nonneg hb0 _)
            _ = b ^ dX := one_mul _
      · simp only [hd, ↓reduceIte, le_refl]
  calc ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)
          ∂(Measure.pi ρ)‖
      = 2 ^ dX * ‖∫ y, (∏ l, ∑ j, c' l j * (y j : ℂ)) *
          ∏ t, ∑ j, ∑ j', (y j : ℂ) * B' t j j' * y j' ∂(Measure.pi ρ)‖ := by
        simp_rw [hint]
        rw [integral_const_mul, norm_mul, norm_pow, RCLike.norm_ofNat]
    _ ≤ 2 ^ dX * (Kf dX * K ^ (dX + k) * tO) :=
        mul_le_mul_of_nonneg_left hcp (by positivity)
    _ = (2 ^ dX * Kf dX) * K ^ (dX + k) * tO := by ring
    _ ≤ (∑ d ∈ Finset.range (2 * p + 7), 2 ^ d * Kf d) * K ^ (dX + k) * tV :=
        mul_le_mul (mul_le_mul_of_nonneg_right hKle (pow_nonneg hK0 _)) htOV htO0
          (mul_nonneg (Finset.sum_nonneg fun d _ => mul_nonneg (by positivity) (hKf0 d))
            (pow_nonneg hK0 _))

/-- The two-point entry law `ξ ∈ {2, −1/2}` with weights `(1/5, 4/5)`: mean `0`, variance `1`,
third moment `3/2 ≠ 0`, so `allModels` strictly contains `zeroThird`. -/
example : (1 / 5 : ℝ) * 2 + 4 / 5 * (-1 / 2) = 0 ∧ (1 / 5 : ℝ) * 2 ^ 2 + 4 / 5 * (-1 / 2) ^ 2 = 1 ∧
    (1 / 5 : ℝ) * 2 ^ 3 + 4 / 5 * (-1 / 2) ^ 3 = 3 / 2 := by
  norm_num

/-! ### Compiled instances -/

section Checks

/-- The tagged word `𝐢𝛍𝐢𝛍𝐢𝛍` with `σ = (0, 1, 1, 1)` has `d_X = 3` and `d_v = 0`. -/
example : dXof (fun _ : Fin 1 => 3) (fun _ _ => true) (fun _ => ![0, 1, 1, 1]) = 3 ∧
    dVof (ns := fun _ : Fin 1 => 3) (fun _ => ![0, 1, 1, 1]) = 0 := by decide

end Checks

end Anisotropic

#print axioms Anisotropic.colLaw
#print axioms Anisotropic.integral_colSplit
#print axioms Anisotropic.colPoly_bound
#print axioms Anisotropic.lem87
