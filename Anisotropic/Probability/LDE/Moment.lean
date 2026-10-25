import Anisotropic.Probability.LDE.Basic
import Anisotropic.Probability.LDE.GraphBound

/-!
# Moment bounds for linear and off-diagonal quadratic forms

The `2p`-th moment bounds behind the large deviation estimates for linear and quadratic forms in
independent centred entries, which the paper cites in Sections 5, 6 and 8. For independent
centred real `y_i` with `E|y_i|^m ≤ C_m`:

* `E|∑ a_i y_i|^{2p} ≤ (2p)^{2p} · momHat C (2p)^p · (∑|a_i|²)^p`;
* `E|∑_{i≠j} y_i A_ij y_j|^{2p} ≤ (4p)^{4p} · momHat C (2p)^{2p} · (∑_{i≠j}|A_ij|²)^p`.

The power `|S|^{2p} = (S S̄)^p` is expanded over index tuples on a finite set of positions.
Independence factorises the expectation of each term into moments of the single variables; a
term in which some variable occurs exactly once vanishes. The remaining terms are grouped by the
fibre partition of the tuple (its kernel), and the sum over each group is bounded by the graph
bound for sums over labellings.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-! ## The graph bound on arbitrary finite vertex and edge types -/

/-- Counting the preimages of a vertex is invariant under relabelling vertices and edges. -/
private lemma moment_card_filter_equiv {V X : Type*} [Fintype X] [DecidableEq V] {n : ℕ}
    (eV : V ≃ Fin n) (eX : X ≃ Fin (Fintype.card X)) (g : X → V) (w : V) :
    (Finset.univ.filter (fun x : Fin (Fintype.card X) => eV (g (eX.symm x)) = eV w)).card =
      (Finset.univ.filter (fun x : X => g x = w)).card := by
  rw [Finset.card_filter, Finset.card_filter, ← eX.symm.sum_comp]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-- The graph bound with vertices, 2-edges and 1-edges indexed by arbitrary finite types. -/
private lemma moment_graph_sum_le {ι V E2 E1 : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    [Fintype E2] [Fintype E1] (src dst : E2 → V) (hloop : ∀ e, src e ≠ dst e)
    (B : E2 → ι → ι → ℝ) (hB : ∀ e i j, 0 ≤ B e i j)
    (at_ : E1 → V) (r : E1 → ι → ℝ) (hr : ∀ f i, 0 ≤ r f i)
    (hdeg : ∀ w, 2 ≤ (Finset.univ.filter (src · = w)).card +
      (Finset.univ.filter (dst · = w)).card + (Finset.univ.filter (at_ · = w)).card) :
    ∑ v : V → ι, (∏ e, B e (v (src e)) (v (dst e))) * ∏ f, r f (v (at_ f)) ≤
      (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) := by
  classical
  set eV := Fintype.equivFin V
  set eE := Fintype.equivFin E2
  set eF := Fintype.equivFin E1
  have h := graph_sum_le (ι := ι) (fun e => eV (src (eE.symm e))) (fun e => eV (dst (eE.symm e)))
    (fun e h => hloop (eE.symm e) (eV.injective h)) (fun e => B (eE.symm e)) (fun e => hB _)
    (fun f => eV (at_ (eF.symm f))) (fun f => r (eF.symm f)) (fun f => hr _) (fun w => by
      have := hdeg (eV.symm w)
      have h1 := moment_card_filter_equiv eV eE src (eV.symm w)
      have h2 := moment_card_filter_equiv eV eE dst (eV.symm w)
      have h3 := moment_card_filter_equiv eV eF at_ (eV.symm w)
      simp only [Equiv.apply_symm_apply] at h1 h2 h3
      rw [h1, h2, h3]
      exact this)
  have hl : ∑ v : V → ι, (∏ e, B e (v (src e)) (v (dst e))) * ∏ f, r f (v (at_ f)) =
      ∑ v : Fin (Fintype.card V) → ι, (∏ e, B (eE.symm e) (v (eV (src (eE.symm e))))
        (v (eV (dst (eE.symm e))))) * ∏ f, r (eF.symm f) (v (eV (at_ (eF.symm f)))) := by
    refine Fintype.sum_equiv (eV.arrowCongr (Equiv.refl ι)) _ _ fun v => ?_
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
      Equiv.symm_apply_apply]
    rw [← eE.symm.prod_comp, ← eF.symm.prod_comp]
  have hr' : (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) =
      (∏ e, Real.sqrt (∑ i, ∑ j, B (eE.symm e) i j ^ 2)) *
        ∏ f, Real.sqrt (∑ i, r (eF.symm f) i ^ 2) := by
    rw [eE.symm.prod_comp (fun e => Real.sqrt (∑ i, ∑ j, B e i j ^ 2)),
      eF.symm.prod_comp (fun f => Real.sqrt (∑ i, r f i ^ 2))]
  rw [hl, hr']
  exact h

/-! ## Kernels of index tuples -/

/-- A representative of the fibre of the tuple `z` through the position `k`. -/
private def momentKer {P ι : Type*} (z : P → ι) (k : P) : P :=
  Classical.choose (⟨k, rfl⟩ : ∃ l, z l = z k)

private lemma momentKer_spec {P ι : Type*} (z : P → ι) (k : P) : z (momentKer z k) = z k :=
  Classical.choose_spec (⟨k, rfl⟩ : ∃ l, z l = z k)

private lemma momentKer_eq_iff {P ι : Type*} (z : P → ι) (k l : P) :
    momentKer z k = momentKer z l ↔ z k = z l := by
  constructor
  · intro h
    have hk := momentKer_spec z k
    rw [h, momentKer_spec z l] at hk
    exact hk.symm
  · intro h
    have key : ∀ (v v' : ι) (hv : ∃ l, z l = v) (hv' : ∃ l, z l = v'), v = v' →
        Classical.choose hv = Classical.choose hv' := by
      rintro v v' hv hv' rfl
      rfl
    exact key _ _ _ _ h

private lemma momentKer_idem {P ι : Type*} (z : P → ι) (k : P) :
    momentKer z (momentKer z k) = momentKer z k :=
  (momentKer_eq_iff z _ _).2 (momentKer_spec z k)

/-- The number of positions at which the tuple `z` takes the value `v`. -/
private def momentMult {P ι : Type*} [Fintype P] [DecidableEq ι] (z : P → ι) (v : ι) : ℕ :=
  (Finset.univ.filter (fun l => z l = v)).card

/-- A product over positions is the product of the powers by multiplicities. -/
private lemma moment_prod_eq_prod_pow {P ι : Type*} [Fintype P] [Fintype ι] [DecidableEq ι]
    (z : P → ι) (x : ι → ℝ) : ∏ l, x (z l) = ∏ v, x v ^ momentMult z v := by
  rw [← Finset.prod_fiberwise Finset.univ z (fun l => x (z l))]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.1 hl).2]), Finset.prod_const]
  rfl

/-- The multiplicities of a tuple add up to the number of positions. -/
private lemma moment_sum_mult {P ι : Type*} [Fintype P] [Fintype ι] [DecidableEq ι]
    (z : P → ι) : ∑ v, momentMult z v = Fintype.card P := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := z) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rfl

section Moments

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Independence factorises the expectation of a product over positions. -/
private lemma moment_integral_prod {C : ℕ → ℝ} {ι P : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype P] {y : ι → Ω → ℝ} (hy : CentredMoments C y) (z : P → ι) :
    ∫ ω, ∏ l, y (z l) ω = ∏ v, ∫ ω, y v ω ^ momentMult z v := by
  have h : ∀ ω, ∏ l, y (z l) ω = ∏ v, y v ω ^ momentMult z v :=
    fun ω => moment_prod_eq_prod_pow z (fun v => y v ω)
  simp_rw [h]
  exact hy.indep.integral_fun_prod_comp (f := fun v t => t ^ momentMult z v)
    (fun v => (hy.measurable v).aemeasurable)
    (fun v => (continuous_pow _).aestronglyMeasurable)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- A term in which some variable occurs exactly once has expectation zero. -/
private lemma moment_integral_prod_eq_zero {C : ℕ → ℝ} {ι P : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype P] {y : ι → Ω → ℝ} (hy : CentredMoments C y) (z : P → ι)
    (h : ∃ v, momentMult z v = 1) : ∫ ω, ∏ l, y (z l) ω = 0 := by
  obtain ⟨v, hv⟩ := h
  rw [moment_integral_prod hy]
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  rw [hv]
  simp only [pow_one]
  exact hy.mean v

/-- `momHat C m` dominates `1` and `|C k|` for `k ≤ m`. -/
private lemma moment_one_le_momHat (C : ℕ → ℝ) (m : ℕ) : 1 ≤ momHat C m := by
  unfold momHat
  have : 0 ≤ ∑ k ∈ Finset.range (m + 1), |C k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

private lemma moment_abs_le_momHat (C : ℕ → ℝ) {m k : ℕ} (hk : k ≤ m) : |C k| ≤ momHat C m := by
  unfold momHat
  have : |C k| ≤ ∑ j ∈ Finset.range (m + 1), |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  linarith

/-- A term without singletons whose multiplicities are at most `m` has expectation at most
`momHat C m ^ q` in absolute value, when there are at most `2q` positions. -/
private lemma moment_abs_integral_prod_le {C : ℕ → ℝ} {ι P : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype P] {y : ι → Ω → ℝ} (hy : CentredMoments C y) (z : P → ι) (m q : ℕ)
    (hm : ∀ v, momentMult z v ≤ m) (hs : ∀ v, momentMult z v ≠ 1)
    (hq : Fintype.card P ≤ 2 * q) :
    |∫ ω, ∏ l, y (z l) ω| ≤ momHat C m ^ q := by
  classical
  have hM := moment_one_le_momHat C m
  rw [moment_integral_prod hy, Finset.abs_prod]
  calc ∏ v, |∫ ω, y v ω ^ momentMult z v|
      ≤ ∏ v, (if momentMult z v = 0 then (1 : ℝ) else momHat C m) := by
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun v _ => ?_
        split_ifs with h0
        · simp [h0]
        · calc |∫ ω, y v ω ^ momentMult z v| ≤ ∫ ω, |y v ω ^ momentMult z v| :=
                abs_integral_le_integral_abs
            _ = ∫ ω, |y v ω| ^ momentMult z v := by simp_rw [abs_pow]
            _ ≤ C (momentMult z v) := hy.moment _ v
            _ ≤ |C (momentMult z v)| := le_abs_self _
            _ ≤ momHat C m := moment_abs_le_momHat C (hm v)
    _ = momHat C m ^ (Finset.univ.filter (fun v => ¬ momentMult z v = 0)).card := by
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    _ ≤ momHat C m ^ q := by
        refine pow_le_pow_right₀ hM ?_
        have h2 : 2 * (Finset.univ.filter (fun v => ¬ momentMult z v = 0)).card ≤
            Fintype.card P := by
          rw [← moment_sum_mult z, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
          calc ∑ _v ∈ Finset.univ.filter (fun v => ¬ momentMult z v = 0), 2
              ≤ ∑ v ∈ Finset.univ.filter (fun v => ¬ momentMult z v = 0), momentMult z v :=
                Finset.sum_le_sum fun v hv => by
                  have := (Finset.mem_filter.1 hv).2
                  have := hs v
                  omega
            _ ≤ ∑ v, momentMult z v :=
                Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        omega

/-- Every product over positions of the variables is integrable. -/
private lemma moment_integrable_prod {C : ℕ → ℝ} {ι P : Type*} [Fintype P]
    {y : ι → Ω → ℝ} (hy : CentredMoments C y) (z : P → ι) :
    Integrable fun ω => ∏ l, y (z l) ω := by
  classical
  have hint : Integrable fun ω => 1 + ∑ l, |y (z l) ω| ^ Fintype.card P :=
    (integrable_const 1).add
      (integrable_finsetSum _ fun l _ => hy.integrable_moment (Fintype.card P) (z l))
  refine hint.mono' (Finset.measurable_prod _ fun l _ => hy.measurable (z l)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  have hS : 0 ≤ ∑ l, |y (z l) ω| ^ Fintype.card P :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _
  rcases isEmpty_or_nonempty P with hP | hP
  · simp
  · obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => |y (z l) ω|)
      Finset.univ_nonempty
    calc ∏ l, |y (z l) ω| ≤ ∏ _l : P, |y (z l₀) ω| :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ => hl₀ l (Finset.mem_univ l)
      _ = |y (z l₀) ω| ^ Fintype.card P := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ ∑ l, |y (z l) ω| ^ Fintype.card P :=
          Finset.single_le_sum (f := fun l => |y (z l) ω| ^ Fintype.card P)
            (fun _ _ => pow_nonneg (abs_nonneg _) _) (Finset.mem_univ l₀)
      _ ≤ 1 + ∑ l, |y (z l) ω| ^ Fintype.card P := by linarith

end Moments

/-! ## The sum over one kernel -/

/-- Counting the edges whose endpoint lies in a fibre of `φ`, fibre point by fibre point. -/
private lemma moment_card_filter_comp {X P V : Type*} [Fintype X] [Fintype P] [DecidableEq P]
    [DecidableEq V] (φ : P → V) (g : X → P) (w : V) :
    (Finset.univ.filter (fun x => φ (g x) = w)).card =
      ∑ l ∈ Finset.univ.filter (fun l => φ l = w),
        (Finset.univ.filter (fun x => g x = l)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ.filter (fun l => φ l = w))
    (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h]; exact (Finset.mem_filter.1 hl).2, h⟩

/-- The weights `∏_e B_e(z_{src e}, z_{dst e}) ∏_f r_f(z_{at f})` of the tuples without
singletons and with a given kernel `κ` add up to at most `∏_e ‖B_e‖_F ∏_f ‖r_f‖₂`, when every
`B_e` vanishes on the diagonal and every position is incident to an edge. -/
private lemma moment_kernel_sum_le {ι P E2 E1 : Type*} [Fintype ι] [DecidableEq ι] [Fintype P]
    [DecidableEq P] [Fintype E2] [Fintype E1] (src dst : E2 → P) (B : E2 → ι → ι → ℝ)
    (hB : ∀ e i j, 0 ≤ B e i j) (hBd : ∀ e i, B e i i = 0) (at_ : E1 → P) (r : E1 → ι → ℝ)
    (hr : ∀ f i, 0 ≤ r f i)
    (hinc : ∀ l, 1 ≤ (Finset.univ.filter (src · = l)).card +
      (Finset.univ.filter (dst · = l)).card + (Finset.univ.filter (at_ · = l)).card)
    (κ : P → P) :
    ∑ z ∈ (Finset.univ.filter (fun z : P → ι => ∀ v, momentMult z v ≠ 1)).filter
        (fun z => momentKer z = κ),
      (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f)) ≤
      (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) := by
  classical
  set S := (Finset.univ.filter (fun z : P → ι => ∀ v, momentMult z v ≠ 1)).filter
    (fun z => momentKer z = κ) with hS
  have hL : 0 ≤ (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  rcases S.eq_empty_or_nonempty with hne | ⟨z₀, hz₀⟩
  · rw [hne, Finset.sum_empty]
    exact hL
  have memS : ∀ z, z ∈ S ↔ (∀ v, momentMult z v ≠ 1) ∧ momentKer z = κ := by
    intro z
    simp [hS, Finset.mem_filter]
  obtain ⟨hns₀, hk₀⟩ := (memS z₀).1 hz₀
  -- every tuple of the group is constant on the fibres of `κ`
  have hzκ : ∀ z ∈ S, ∀ l, z (κ l) = z l := by
    intro z hz l
    rw [← ((memS z).1 hz).2]
    exact momentKer_spec z l
  have hκidem : ∀ l, κ (κ l) = κ l := by
    intro l
    rw [← hk₀]
    exact momentKer_idem z₀ l
  have hκiff : ∀ l l', κ l = κ l' ↔ z₀ l = z₀ l' := by
    intro l l'
    rw [← hk₀]
    exact momentKer_eq_iff z₀ l l'
  by_cases hloop : ∃ e, κ (src e) = κ (dst e)
  · obtain ⟨e, he⟩ := hloop
    have h0 : ∀ z ∈ S, (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f)) = 0 := by
      intro z hz
      have hzz : z (src e) = z (dst e) := by
        rw [← hzκ z hz (src e), ← hzκ z hz (dst e), he]
      rw [Finset.prod_eq_zero (Finset.mem_univ e) (by rw [hzz]; exact hBd e _), zero_mul]
    rw [Finset.sum_eq_zero h0]
    exact hL
  simp only [not_exists] at hloop
  -- the reduced graph on the representatives of the fibres of `κ`
  set V := {l : P // κ l = l}
  let φ : P → V := fun l => ⟨κ l, hκidem l⟩
  have hdeg : ∀ w : V, 2 ≤ (Finset.univ.filter (fun e => φ (src e) = w)).card +
      (Finset.univ.filter (fun e => φ (dst e) = w)).card +
      (Finset.univ.filter (fun f => φ (at_ f) = w)).card := by
    intro w
    rw [moment_card_filter_comp φ src w, moment_card_filter_comp φ dst w,
      moment_card_filter_comp φ at_ w, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hcardw : 2 ≤ (Finset.univ.filter (fun l => φ l = w)).card := by
      have hset : Finset.univ.filter (fun l => φ l = w) =
          Finset.univ.filter (fun l => z₀ l = z₀ w.1) := by
        refine Finset.filter_congr fun l _ => ?_
        rw [← hκiff, w.2, Subtype.ext_iff]
      rw [hset]
      have h1 : 1 ≤ momentMult z₀ (z₀ w.1) :=
        Finset.card_pos.2 ⟨w.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
      have h2 := hns₀ (z₀ w.1)
      unfold momentMult at h1 h2
      omega
    calc 2 ≤ (Finset.univ.filter (fun l => φ l = w)).card := hcardw
      _ = ∑ l ∈ Finset.univ.filter (fun l => φ l = w), 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ _ := Finset.sum_le_sum fun l _ => hinc l
  have hG := moment_graph_sum_le (ι := ι) (fun e => φ (src e)) (fun e => φ (dst e))
    (fun e h => hloop e (congrArg Subtype.val h)) B hB (fun f => φ (at_ f)) r hr hdeg
  -- each tuple of the group is determined by its values at the representatives
  let res : (P → ι) → (V → ι) := fun z w => z w.1
  have hW : ∀ z ∈ S, (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f)) =
      (∏ e, B e (res z (φ (src e))) (res z (φ (dst e)))) * ∏ f, r f (res z (φ (at_ f))) := by
    intro z hz
    simp only [res, φ, hzκ z hz]
  have hinj : Set.InjOn res S := by
    intro z hz z' hz' h
    funext l
    rw [← hzκ z hz l, ← hzκ z' hz' l]
    exact congrFun h (φ l)
  calc ∑ z ∈ S, (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f))
      = ∑ z ∈ S, (∏ e, B e (res z (φ (src e))) (res z (φ (dst e)))) *
          ∏ f, r f (res z (φ (at_ f))) := Finset.sum_congr rfl hW
    _ = ∑ v ∈ S.image res, (∏ e, B e (v (φ (src e))) (v (φ (dst e)))) *
          ∏ f, r f (v (φ (at_ f))) :=
        (Finset.sum_image (f := fun v : V → ι => (∏ e, B e (v (φ (src e))) (v (φ (dst e)))) *
          ∏ f, r f (v (φ (at_ f)))) hinj).symm
    _ ≤ ∑ v : V → ι, (∏ e, B e (v (φ (src e))) (v (φ (dst e)))) * ∏ f, r f (v (φ (at_ f))) :=
        Finset.sum_le_univ_sum_of_nonneg fun v =>
          mul_nonneg (Finset.prod_nonneg fun _ _ => hB _ _ _)
            (Finset.prod_nonneg fun _ _ => hr _ _)
    _ ≤ _ := hG

/-! ## The moment bound for an expanded form -/

section Expansion

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The moment bound for a real combination `∑_z c(z) ∏_l y_{z_l}` of products over positions,
with `|c(z)| ≤ ∏_e B_e(z_{src e}, z_{dst e}) ∏_f r_f(z_{at f})`: it is integrable, and its
expectation is at most `|P|^{|P|} · momHat C m ^ q · ∏_e ‖B_e‖_F ∏_f ‖r_f‖₂`, when every
multiplicity of a tuple of nonzero weight is at most `m` and there are at most `2q` positions. -/
private lemma moment_expansion_le {C : ℕ → ℝ} {ι P E2 E1 : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype P] [DecidableEq P] [Fintype E2] [Fintype E1] {y : ι → Ω → ℝ}
    (hy : CentredMoments C y) (src dst : E2 → P) (B : E2 → ι → ι → ℝ)
    (hB : ∀ e i j, 0 ≤ B e i j) (hBd : ∀ e i, B e i i = 0) (at_ : E1 → P) (r : E1 → ι → ℝ)
    (hr : ∀ f i, 0 ≤ r f i)
    (hinc : ∀ l, 1 ≤ (Finset.univ.filter (src · = l)).card +
      (Finset.univ.filter (dst · = l)).card + (Finset.univ.filter (at_ · = l)).card)
    (c : (P → ι) → ℝ)
    (hc : ∀ z, |c z| ≤ (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f)))
    (m q : ℕ)
    (hm : ∀ z, (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f)) ≠ 0 →
      ∀ v, momentMult z v ≤ m)
    (hq : Fintype.card P ≤ 2 * q) :
    Integrable (fun ω => ∑ z, c z * ∏ l, y (z l) ω) ∧
      ∫ ω, ∑ z, c z * ∏ l, y (z l) ω ≤
        (Fintype.card P : ℝ) ^ Fintype.card P * momHat C m ^ q *
          ((∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2)) := by
  classical
  set W : (P → ι) → ℝ := fun z => (∏ e, B e (z (src e)) (z (dst e))) * ∏ f, r f (z (at_ f))
    with hWdef
  set L := (∏ e, Real.sqrt (∑ i, ∑ j, B e i j ^ 2)) * ∏ f, Real.sqrt (∑ i, r f i ^ 2) with hLdef
  set M := momHat C m with hMdef
  have hM : 0 ≤ M := le_trans zero_le_one (moment_one_le_momHat C m)
  have hW0 : ∀ z, 0 ≤ W z := fun z =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => hB _ _ _) (Finset.prod_nonneg fun _ _ => hr _ _)
  have hint : ∀ z : P → ι, Integrable fun ω => c z * ∏ l, y (z l) ω :=
    fun z => (moment_integrable_prod hy z).const_mul (c z)
  refine ⟨integrable_finsetSum _ fun z _ => hint z, ?_⟩
  rw [integral_finsetSum _ fun z _ => hint z]
  -- the bound of a single term
  have hterm : ∀ z : P → ι, ∫ ω, c z * ∏ l, y (z l) ω ≤
      M ^ q * (if ∀ v, momentMult z v ≠ 1 then W z else 0) := by
    intro z
    rw [integral_const_mul]
    split_ifs with hs
    · by_cases hWz : W z = 0
      · have h1 : |c z| ≤ W z := hc z
        have : c z = 0 := abs_nonpos_iff.1 (by rw [hWz] at h1; exact h1)
        rw [this, zero_mul, hWz, mul_zero]
      · calc c z * ∫ ω, ∏ l, y (z l) ω ≤ |c z * ∫ ω, ∏ l, y (z l) ω| := le_abs_self _
          _ = |c z| * |∫ ω, ∏ l, y (z l) ω| := abs_mul _ _
          _ ≤ W z * M ^ q :=
              mul_le_mul (hc z) (moment_abs_integral_prod_le hy z m q (hm z hWz) hs hq)
                (abs_nonneg _) (hW0 z)
          _ = M ^ q * W z := mul_comm _ _
    · push Not at hs
      rw [moment_integral_prod_eq_zero hy z hs, mul_zero, mul_zero]
  calc ∑ z, ∫ ω, c z * ∏ l, y (z l) ω
      ≤ ∑ z, M ^ q * (if ∀ v, momentMult z v ≠ 1 then W z else 0) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = M ^ q * ∑ z ∈ Finset.univ.filter (fun z : P → ι => ∀ v, momentMult z v ≠ 1), W z := by
        rw [← Finset.mul_sum, Finset.sum_filter]
    _ = M ^ q * ∑ κ : P → P, ∑ z ∈ (Finset.univ.filter
          (fun z : P → ι => ∀ v, momentMult z v ≠ 1)).filter (fun z => momentKer z = κ), W z := by
        rw [Finset.sum_fiberwise]
    _ ≤ M ^ q * ∑ _κ : P → P, L :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun κ _ =>
          moment_kernel_sum_le src dst B hB hBd at_ r hr hinc κ) (pow_nonneg hM q)
    _ = (Fintype.card P : ℝ) ^ Fintype.card P * M ^ q * L := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        push_cast
        ring

end Expansion

/-! ## The linear and off-diagonal moment bounds -/

section LDEpins

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Linear `2p`-th moment bound: `E|∑ a_i y_i|^{2p} ≤ ldeLinConst C p · (∑|a_i|²)^p`. -/
theorem lde_lin_moment {C : ℕ → ℝ} {ι : Type*} [Fintype ι] {y : ι → Ω → ℝ}
    (hy : CentredMoments C y) (a : ι → ℂ) (p : ℕ) :
    Integrable (fun ω => ‖∑ i, a i * y i ω‖ ^ (2 * p)) ∧
      ∫ ω, ‖∑ i, a i * y i ω‖ ^ (2 * p) ≤ ldeLinConst C p * (∑ i, ‖a i‖ ^ 2) ^ p := by
  classical
  -- positions `Fin p × Bool`; the flag selects `a` or its conjugate
  let b : Bool → ι → ℂ := fun t i => if t then a i else (starRingEnd ℂ) (a i)
  let c : (Fin p × Bool → ι) → ℝ := fun z => (∏ l, b l.2 (z l)).re
  have hexp : ∀ ω, ‖∑ i, a i * y i ω‖ ^ (2 * p) =
      ∑ z : Fin p × Bool → ι, c z * ∏ l, y (z l) ω := by
    intro ω
    set S := ∑ i, a i * (y i ω : ℂ) with hS
    have hconj : (starRingEnd ℂ) S = ∑ i, (starRingEnd ℂ) (a i) * (y i ω : ℂ) := by
      rw [hS, map_sum]
      simp only [map_mul, Complex.conj_ofReal]
    have hC : ((‖S‖ ^ (2 * p) : ℝ) : ℂ) =
        ∑ z : Fin p × Bool → ι, (∏ l, b l.2 (z l)) * ((∏ l, y (z l) ω : ℝ) : ℂ) := by
      calc ((‖S‖ ^ (2 * p) : ℝ) : ℂ) = (S * (starRingEnd ℂ) S) ^ p := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
            push_cast
            ring
        _ = ∏ l : Fin p × Bool, ∑ i, b l.2 i * (y i ω : ℂ) := by
            rw [Fintype.prod_prod_type]
            simp only [Fintype.prod_bool, b, ite_true, Bool.false_eq_true, ite_false]
            rw [← hS, ← hconj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = ∑ z : Fin p × Bool → ι, ∏ l, b l.2 (z l) * (y (z l) ω : ℂ) := Fintype.prod_sum _
        _ = _ := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
    have hre := congrArg Complex.re hC
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.re_mul_ofReal]
  have key := moment_expansion_le (E2 := Empty) hy (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) id (fun _ i => ‖a i‖)
    (fun _ _ => norm_nonneg _) (fun l => by simp [Finset.filter_eq']) c
    (fun z => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, id]
      refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
      rw [norm_prod]
      refine Finset.prod_congr rfl fun l _ => ?_
      cases l.2 <;> simp [b])
    (2 * p) p
    (fun z _ v => by
      refine (Finset.card_filter_le _ _).trans ?_
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega)
    (by simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; omega)
  simp only [hexp]
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  have hs : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [mul_comm p 2, pow_mul (Real.sqrt _), Real.sq_sqrt hs, ldeLinConst]

/-- Off-diagonal `2p`-th moment bound:
`E|∑_{i≠j} y_i A_ij y_j|^{2p} ≤ ldeOffConst C p · (∑_{i≠j}|A_ij|²)^p`. -/
theorem lde_off_moment {C : ℕ → ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι] {y : ι → Ω → ℝ}
    (hy : CentredMoments C y) (A : ι → ι → ℂ) (p : ℕ) :
    Integrable (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i, y i ω * A i j * y j ω‖ ^ (2 * p)) ∧
      ∫ ω, ‖∑ i, ∑ j ∈ Finset.univ.erase i, y i ω * A i j * y j ω‖ ^ (2 * p) ≤
        ldeOffConst C p * (∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2) ^ p := by
  classical
  -- pairs `Fin p × Bool`, the flag selecting `A` or its conjugate; positions are the two ends
  -- `Sum.inl q`, `Sum.inr q` of the pair `q`
  let Ao : Bool → ι → ι → ℂ := fun t i j =>
    if i = j then 0 else if t then A i j else (starRingEnd ℂ) (A i j)
  let e : (Fin p × Bool ⊕ Fin p × Bool → ι) ≃ (Fin p × Bool → ι × ι) :=
    { toFun := fun z q => (z (Sum.inl q), z (Sum.inr q))
      invFun := fun w => Sum.elim (fun q => (w q).1) (fun q => (w q).2)
      left_inv := fun z => by
        funext l
        cases l <;> rfl
      right_inv := fun w => rfl }
  let c : (Fin p × Bool ⊕ Fin p × Bool → ι) → ℝ := fun z =>
    (∏ q, Ao q.2 (z (Sum.inl q)) (z (Sum.inr q))).re
  have hexp : ∀ ω, ‖∑ i, ∑ j ∈ Finset.univ.erase i, y i ω * A i j * y j ω‖ ^ (2 * p) =
      ∑ z : Fin p × Bool ⊕ Fin p × Bool → ι, c z * ∏ l, y (z l) ω := by
    intro ω
    set T := ∑ i, ∑ j ∈ Finset.univ.erase i, (y i ω : ℂ) * A i j * (y j ω : ℂ) with hT
    have hTt : ∀ t : Bool, (if t then T else (starRingEnd ℂ) T) =
        ∑ x : ι × ι, Ao t x.1 x.2 * ((y x.1 ω * y x.2 ω : ℝ) : ℂ) := by
      intro t
      rw [Fintype.sum_prod_type]
      have h1 : (if t then T else (starRingEnd ℂ) T) =
          ∑ i, ∑ j ∈ Finset.univ.erase i, Ao t i j * ((y i ω * y j ω : ℝ) : ℂ) := by
        cases t
        · simp only [hT, map_sum, map_mul, Complex.conj_ofReal, Bool.false_eq_true, ite_false]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
          have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
          simp only [Ao, hij, ite_false, Bool.false_eq_true]
          push_cast
          ring
        · simp only [hT, ite_true]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
          have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
          simp only [Ao, hij, ite_false, ite_true]
          push_cast
          ring
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_erase _ ?_
      simp [Ao]
    have hC : ((‖T‖ ^ (2 * p) : ℝ) : ℂ) =
        ∑ z : Fin p × Bool ⊕ Fin p × Bool → ι,
          (∏ q, Ao q.2 (z (Sum.inl q)) (z (Sum.inr q))) * ((∏ l, y (z l) ω : ℝ) : ℂ) := by
      calc ((‖T‖ ^ (2 * p) : ℝ) : ℂ) = (T * (starRingEnd ℂ) T) ^ p := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
            push_cast
            ring
        _ = ∏ q : Fin p × Bool, (if q.2 then T else (starRingEnd ℂ) T) := by
            rw [Fintype.prod_prod_type]
            simp only [Fintype.prod_bool, ite_true, Bool.false_eq_true, ite_false]
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = ∏ q : Fin p × Bool, ∑ x : ι × ι, Ao q.2 x.1 x.2 * ((y x.1 ω * y x.2 ω : ℝ) : ℂ) :=
            Finset.prod_congr rfl fun q _ => hTt q.2
        _ = ∑ w : Fin p × Bool → ι × ι,
              ∏ q, Ao q.2 (w q).1 (w q).2 * ((y (w q).1 ω * y (w q).2 ω : ℝ) : ℂ) :=
            Fintype.prod_sum _
        _ = ∑ z : Fin p × Bool ⊕ Fin p × Bool → ι,
              ∏ q, Ao q.2 (e z q).1 (e z q).2 * ((y (e z q).1 ω * y (e z q).2 ω : ℝ) : ℂ) :=
            (e.sum_comp (fun w => ∏ q, Ao q.2 (w q).1 (w q).2 *
              ((y (w q).1 ω * y (w q).2 ω : ℝ) : ℂ))).symm
        _ = _ := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Fintype.prod_sum_type, Complex.ofReal_mul, Complex.ofReal_prod,
              Complex.ofReal_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun q _ => ?_
            push_cast
            rfl
    have hre := congrArg Complex.re hC
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.re_mul_ofReal]
  have key := moment_expansion_le (E1 := Empty) hy (fun q : Fin p × Bool => Sum.inl q)
    (fun q => Sum.inr q) (fun _ i j => if i = j then 0 else ‖A i j‖)
    (fun _ i j => by split_ifs <;> simp) (fun _ i => by simp)
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun l => by cases l <;> simp [Finset.filter_eq']) c
    (fun z => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
      rw [norm_prod]
      refine Finset.prod_congr rfl fun q _ => ?_
      by_cases hij : z (Sum.inl q) = z (Sum.inr q)
      · simp [Ao, hij]
      · cases q.2 <;> simp [Ao, hij])
    (2 * p) (2 * p)
    (fun z hz v => by
      have hne : ∀ q, z (Sum.inl q) ≠ z (Sum.inr q) := by
        intro q hq
        refine hz ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq]), zero_mul]
      unfold momentMult
      rw [Finset.card_filter, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      calc ∑ q : Fin p × Bool, ((if z (Sum.inl q) = v then 1 else 0) +
            (if z (Sum.inr q) = v then 1 else 0))
          ≤ ∑ _q : Fin p × Bool, 1 := Finset.sum_le_sum fun q _ => by
            by_cases h1 : z (Sum.inl q) = v
            · have h2 : ¬ z (Sum.inr q) = v := fun h2 => hne q (h1.trans h2.symm)
              simp [h1, h2]
            · split_ifs <;> simp
        _ = 2 * p := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              Fintype.card_bool, smul_eq_mul, mul_one]
            ring)
    (by simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        omega)
  simp only [hexp]
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  have hsum : ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖) ^ 2 =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_erase (f := fun j => (if i = j then 0 else ‖A i j‖) ^ 2) (a := i)
      Finset.univ (by simp)]
    exact Finset.sum_congr rfl fun j hj => by simp [(Finset.ne_of_mem_erase hj).symm]
  have hs : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    hsum]
  rw [mul_comm p 2, pow_mul (Real.sqrt _), Real.sq_sqrt hs, ldeOffConst,
    show 2 * p + 2 * p = 4 * p by ring]

end LDEpins

/-! ## Instances (Rademacher model, `N = 2`, `p = 1`) -/

/-- The right-hand side of the linear instance equals `32`. -/
example : ldeLinConst (fun _ => 1) 1 * (∑ _i : Fin 2, ‖(1 : ℂ)‖ ^ 2) ^ 1 = 32 := by
  simp [ldeLinConst, momHat]
  norm_num

/-- The right-hand side of the off-diagonal instance equals `8192`. -/
example : ldeOffConst (fun _ => 1) 1 *
    (∑ i : Fin 2, ∑ j ∈ Finset.univ.erase i, ‖(if i = j then 0 else 1 : ℂ)‖ ^ 2) ^ 1 = 8192 := by
  simp [ldeOffConst, momHat, Fin.sum_univ_two]
  norm_num

end Anisotropic

#print axioms Anisotropic.lde_lin_moment
#print axioms Anisotropic.lde_off_moment
