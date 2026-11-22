module

public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.EdgeDefs
public import Anisotropic.Wigner.EdgeGap
public import Anisotropic.Wigner.EdgeSqrt
public import Anisotropic.Wigner.Main
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.SelfConsistentII

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The local edge domains at `L₊` (the cone and the comparison window), `Ψ^W` and the anisotropic law on them -/

/-- The edge cone at `L₊`: `z ∈ 𝐃^W(τ, N)` with `η ≥ N^{-2/3}`, `|E - L₊| ≤ c` and
`|E - L₊| ≤ K η`. -/
def edgeConeW (τ : ℝ) (N : ℕ) (a : Fin N → ℝ) (c K : ℝ) : Set ℂ :=
  {z | z ∈ domW τ N ∧ (N : ℝ) ^ (-2 / 3 : ℝ) ≤ z.im ∧ |z.re - LpW a| ≤ c ∧
    |z.re - LpW a| ≤ K * z.im}

/-- The comparison window at `L₊`: `z ∈ 𝐃^W(τ, N)` with `η ≥ N^{-2/3-9ε}` and
`|E - L₊| ≤ 3 N^{-2/3+ε}`. -/
def edgeWinW (τ : ℝ) (N : ℕ) (a : Fin N → ℝ) (ε : ℝ) : Set ℂ :=
  {z | z ∈ domW τ N ∧ etaE N ε ≤ z.im ∧ |z.re - LpW a| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)}

/-- The edge cone is a spectral domain (Definition 12.1). -/
theorem spectralDomainW_edgeConeW (τ : ℝ) (N : ℕ) (a : Fin N → ℝ) (c : ℝ) {K : ℝ}
    (hK : 0 ≤ K) : SpectralDomainW τ N (edgeConeW τ N a c K) := by
  refine ⟨fun z hz => hz.1, fun z hz w hw hre him => ⟨hw, hz.2.1.trans him, ?_, ?_⟩⟩
  · rw [hre]
    exact hz.2.2.1
  · rw [hre]
    exact hz.2.2.2.trans (mul_le_mul_of_nonneg_left him hK)

/-- The comparison window is a spectral domain (Definition 12.1). -/
theorem spectralDomainW_edgeWinW (τ : ℝ) (N : ℕ) (a : Fin N → ℝ) (ε : ℝ) :
    SpectralDomainW τ N (edgeWinW τ N a ε) := by
  refine ⟨fun z hz => hz.1, fun z hz w hw hre him => ⟨hw, hz.2.1.trans him, ?_⟩⟩
  rw [hre]
  exact hz.2.2

/-- `S(maxᵢ aᵢ + 1) ≤ 1`. -/
private lemma aux_sW_le_one {N : ℕ} (a : Fin N → ℝ) : sW a ((⨆ i, a i) + 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp [sW]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
  unfold sW
  have h : ∀ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ 1 := by
    intro i
    have := le_ciSup (Set.finite_range a).bddAbove i
    apply inv_le_one_of_one_le₀
    nlinarith
  calc (N : ℝ)⁻¹ * ∑ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = 1 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]; field_simp

/-- `S` is continuous at every point to the right of the spectrum. -/
private lemma aux_sW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : ∀ i, a i < x) :
    ContinuousAt (sW a) x := by
  unfold sW
  refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
  have hne : (a i - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hx i).ne)
  exact ((continuousAt_const.sub continuousAt_id).pow 2).inv₀ hne

/-- For `N ≥ 1`: `maxᵢ aᵢ + N⁻¹ ≤ x₊ ≤ maxᵢ aᵢ + 1` and `S(x₊) ≤ 1`. -/
private lemma aux_xp_bounds {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    (⨆ i, a i) + (N : ℝ)⁻¹ ≤ xpW a ∧ xpW a ≤ (⨆ i, a i) + 1 ∧ sW a (xpW a) ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  set T := {x | α < x ∧ sW a x ≤ 1} with hT
  have hbdd : BddBelow T := ⟨α, fun x hx => hx.1.le⟩
  have hmem : α + 1 ∈ T := ⟨by linarith, aux_sW_le_one a⟩
  have hxp : xpW a = sInf T := rfl
  have hup : xpW a ≤ α + 1 := hxp ▸ csInf_le hbdd hmem
  have hlow : ∀ x ∈ T, α + (N : ℝ)⁻¹ ≤ x := by
    intro x hx
    by_contra h
    push Not at h
    have hd : 0 < x - α := by linarith [hx.1]
    have hdN : x - α < (N : ℝ)⁻¹ := by linarith
    have h1 : ((a i₀ - x) ^ 2)⁻¹ ≤ ∑ i, ((a i - x) ^ 2)⁻¹ :=
      Finset.single_le_sum (f := fun i => ((a i - x) ^ 2)⁻¹) (fun i _ => by positivity)
        (Finset.mem_univ i₀)
    have h2 : a i₀ - x = -(x - α) := by rw [hi₀]; ring
    have h3 : (N : ℝ) ^ 2 < ((a i₀ - x) ^ 2)⁻¹ := by
      rw [h2, neg_sq]
      rw [lt_inv_comm₀ (by positivity) (by positivity)]
      calc (x - α) ^ 2 < ((N : ℝ)⁻¹) ^ 2 := by gcongr
        _ = ((N : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
    have h4 : (N : ℝ)⁻¹ * (N : ℝ) ^ 2 < sW a x := by
      unfold sW
      exact mul_lt_mul_of_pos_left (h3.trans_le h1) (by positivity)
    have h5 : (N : ℝ)⁻¹ * (N : ℝ) ^ 2 = N := by field_simp
    have := hx.2
    linarith
  have hge : α + (N : ℝ)⁻¹ ≤ xpW a := hxp ▸ le_csInf ⟨α + 1, hmem⟩ hlow
  have hinv : 0 < (N : ℝ)⁻¹ := by positivity
  have hgt : ∀ i, a i < xpW a := fun i => by linarith [hle i]
  refine ⟨hge, hup, ?_⟩
  have hc := aux_sW_continuousAt a hgt
  by_contra h
  push Not at h
  have hev : ∀ᶠ y in 𝓝 (xpW a), 1 < sW a y := hc.eventually (lt_mem_nhds h)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨y, hyT, hy⟩ := exists_lt_of_csInf_lt ⟨α + 1, hmem⟩
    (show sInf T < xpW a + δ by rw [← hxp]; linarith)
  have hy1 : xpW a ≤ y := hxp ▸ csInf_le hbdd hyT
  have : dist y (xpW a) < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  linarith [hball this, hyT.2]

/-- `|L₊| ≤ r + 2` when `|aᵢ| ≤ r` (`maxᵢ aᵢ < x₊ ≤ maxᵢ aᵢ + 1` and
`g(x₊) ≤ x₊ + S(x₊)^{1/2}`). -/
theorem abs_LpW_le {N : ℕ} (hN : 1 ≤ N) {a : Fin N → ℝ} {r : ℝ} (ha : ∀ i, |a i| ≤ r) :
    |LpW a| ≤ r + 2 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hge, hup, hS⟩ := aux_xp_bounds hN a
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  have hαi : α = a i₀ := hi₀.symm
  have hαr : α ≤ r := by rw [hαi]; exact (abs_le.1 (ha i₀)).2
  have hαl : -r ≤ α := by rw [hαi]; exact (abs_le.1 (ha i₀)).1
  have hinv : 0 < (N : ℝ)⁻¹ := by positivity
  have hneg : ∀ i, (a i - xpW a)⁻¹ < 0 := fun i =>
    inv_lt_zero.2 (by linarith [hle i])
  have hS' : (N : ℝ)⁻¹ * ∑ i, (a i - xpW a)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hinv.le (Finset.sum_nonpos fun i _ => (hneg i).le)
  have hsum : ∑ i, (-(a i - xpW a)⁻¹) ≤ ∑ i : Fin N, (1 + ((a i - xpW a) ^ 2)⁻¹) / 2 :=
    Finset.sum_le_sum fun i _ => by
      rw [← inv_pow]
      nlinarith [sq_nonneg ((a i - xpW a)⁻¹ + 1)]
  have hav : (N : ℝ)⁻¹ * ∑ i : Fin N, (1 + ((a i - xpW a) ^ 2)⁻¹) / 2 ≤ 1 := by
    have e : ∑ i : Fin N, (1 + ((a i - xpW a) ^ 2)⁻¹) / 2 =
        (N + ∑ i, ((a i - xpW a) ^ 2)⁻¹) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp
    have e2 : ∑ i, ((a i - xpW a) ^ 2)⁻¹ = N * sW a (xpW a) := by
      unfold sW; field_simp
    rw [e, e2]
    have : (N : ℝ)⁻¹ * ((N + N * sW a (xpW a)) / 2) = (1 + sW a (xpW a)) / 2 := by
      field_simp
    rw [this]; linarith
  have hup' : -((N : ℝ)⁻¹ * ∑ i, (a i - xpW a)⁻¹) ≤ 1 := by
    have : -((N : ℝ)⁻¹ * ∑ i, (a i - xpW a)⁻¹) = (N : ℝ)⁻¹ * ∑ i, (-(a i - xpW a)⁻¹) := by
      rw [Finset.sum_neg_distrib]; ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hsum hinv.le).trans hav
  have hL : LpW a = xpW a - (N : ℝ)⁻¹ * ∑ i, (a i - xpW a)⁻¹ := rfl
  rw [abs_le]
  constructor <;> linarith

/-- Near `L₊`, `Im m^W ≤ K √(B + η)` whenever `|E - L₊| ≤ B`. -/
private lemma aux_im_m_le {τ : ℝ} (hτ : 0 < τ) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) →
      ∀ z : ℂ, 0 < z.im → ‖z - (LpW a : ℂ)‖ ≤ c → ∀ B : ℝ, |z.re - LpW a| ≤ B →
        (mW a z).im ≤ K * √(B + z.im) := by
  obtain ⟨c, K, hc, hK, N₀, h⟩ := im_mW_sqrt_edge hτ
  refine ⟨c, K, hc, hK, max N₀ 1, le_max_right _ _, fun N hN a ha hSB z hz hzc B hB => ?_⟩
  obtain ⟨h1, h2⟩ := h N (le_of_max_le_left hN) a ha hSB z hz hzc
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  rcases le_total z.re (LpW a) with hle | hle
  · calc (mW a z).im ≤ K * √(LpW a - z.re + z.im) := (h1 hle).2
      _ ≤ K * √(B + z.im) := by
        gcongr
        linarith [(abs_le.1 hB).1]
  · calc (mW a z).im ≤ K * (z.im / √(z.re - LpW a + z.im)) := (h2 hle).2
      _ ≤ K * √(B + z.im) := by
        gcongr
        have hs : 0 < √(z.re - LpW a + z.im) := Real.sqrt_pos.2 (by linarith)
        rw [div_le_iff₀ hs]
        have e1 : √z.im * √z.im = z.im := Real.mul_self_sqrt hz.le
        have e2 : √z.im ≤ √(B + z.im) := Real.sqrt_le_sqrt (by linarith)
        have e3 : √z.im ≤ √(z.re - LpW a + z.im) := Real.sqrt_le_sqrt (by linarith)
        have e4 : 0 ≤ √z.im := Real.sqrt_nonneg _
        calc z.im = √z.im * √z.im := e1.symm
          _ ≤ √(B + z.im) * √(z.re - LpW a + z.im) := mul_le_mul e2 e3 e4 (Real.sqrt_nonneg _)

/-- `Im m^W ≤ 1`. -/
private lemma aux_im_m_le_one {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    (mW a z).im ≤ 1 :=
  (Complex.im_le_norm _).trans (norm_mW_lt_one hN a hz).le

/-- Algebra of `Ψ^W` on the edge cone: with `n p³ = 1` and `η ≥ p²`, `Im m ≤ C √η` gives
`Ψ ≤ (√C + 1) p`. -/
private lemma aux_cone_alg {n p η M C : ℝ} (hn : 0 < n) (hp : 0 < p) (hnp : n * p ^ 3 = 1)
    (hη : p ^ 2 ≤ η) (hC : 0 ≤ C) (hM : M ≤ C * √η) :
    √(M / (n * η)) + 1 / (n * η) ≤ (√C + 1) * p := by
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  set t := √η with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hη0
  have htt : t * t = η := Real.mul_self_sqrt hη0.le
  have hpt : p ≤ t := by
    rw [ht]
    exact Real.le_sqrt_of_sq_le hη
  have h1 : 1 / (n * η) ≤ p := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hn hp, mul_pos (mul_pos hn hp) hp]
  have h2 : M / (n * η) ≤ C * p ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have key : t ≤ p ^ 2 * (n * η) := by
      have e : p ^ 2 * (n * η) * p = η * (n * p ^ 3) := by ring
      have e2 : p ^ 2 * (n * η) * p = η := by rw [e, hnp, mul_one]
      have h3 : t * p ≤ p ^ 2 * (n * η) * p := by
        rw [e2, ← htt]
        nlinarith
      exact le_of_mul_le_mul_right h3 hp
    have : C * t ≤ C * (p ^ 2 * (n * η)) := mul_le_mul_of_nonneg_left key hC
    linarith
  calc √(M / (n * η)) + 1 / (n * η) ≤ √(C * p ^ 2) + p :=
        add_le_add (Real.sqrt_le_sqrt h2) h1
    _ = (√C + 1) * p := by
        rw [Real.sqrt_mul hC, Real.sqrt_sq hp.le]; ring

/-- Algebra of `Ψ^W` away from the edge: `η ≥ c'` and `Im m ≤ 1` give
`Ψ ≤ (c'^{-1/2} + c'^{-1}) p`. -/
private lemma aux_far_alg {n p η M c' : ℝ} (hn : 0 < n) (hp : 0 < p) (hp1 : p ≤ 1)
    (hnp : n * p ^ 3 = 1) (hc' : 0 < c') (hη : c' ≤ η) (hM : M ≤ 1) :
    √(M / (n * η)) + 1 / (n * η) ≤ (1 / √c' + 1 / c') * p := by
  have hη0 : 0 < η := lt_of_lt_of_le hc' hη
  have hq : 1 / (n * η) ≤ p ^ 3 / c' := by
    rw [div_le_div_iff₀ (by positivity) hc']
    have : p ^ 3 * (n * η) = η := by
      have : p ^ 3 * (n * η) = η * (n * p ^ 3) := by ring
      rw [this, hnp, mul_one]
    rw [this]; linarith
  have hM' : M / (n * η) ≤ p ^ 3 / c' := by
    calc M / (n * η) ≤ 1 / (n * η) := by gcongr
      _ ≤ _ := hq
  have hp3 : p ^ 3 / c' ≤ p / c' := by
    apply div_le_div_of_nonneg_right _ hc'.le
    nlinarith [pow_pos hp 2]
  have hp3' : p ^ 3 / c' ≤ p ^ 2 / c' := by
    apply div_le_div_of_nonneg_right _ hc'.le
    nlinarith [pow_pos hp 2]
  have hsq : √(M / (n * η)) ≤ p / √c' := by
    calc √(M / (n * η)) ≤ √(p ^ 2 / c') := Real.sqrt_le_sqrt (hM'.trans hp3')
      _ = p / √c' := by rw [Real.sqrt_div (by positivity), Real.sqrt_sq hp.le]
  calc √(M / (n * η)) + 1 / (n * η) ≤ p / √c' + p / c' := add_le_add hsq (hq.trans hp3)
    _ = (1 / √c' + 1 / c') * p := by ring

/-- `(n^x)^k = n^{xk}` for real `n ≥ 0`. -/
private lemma aux_rpow_pow {n : ℝ} (hn : 0 ≤ n) (x : ℝ) (k : ℕ) :
    (n ^ x) ^ k = n ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]

/-- For `n ≥ 1`: `p = n^{-1/3}` satisfies `0 < p ≤ 1`, `n p³ = 1` and `p² = n^{-2/3}`. -/
private lemma aux_p_facts {n : ℝ} (hn : 1 ≤ n) :
    0 < n ^ (-1 / 3 : ℝ) ∧ n ^ (-1 / 3 : ℝ) ≤ 1 ∧ n * (n ^ (-1 / 3 : ℝ)) ^ 3 = 1 ∧
      (n ^ (-1 / 3 : ℝ)) ^ 2 = n ^ (-2 / 3 : ℝ) := by
  have hn0 : 0 < n := by linarith
  refine ⟨Real.rpow_pos_of_pos hn0 _, Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num), ?_, ?_⟩
  · rw [aux_rpow_pow hn0.le]
    have : (-1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    field_simp
  · rw [aux_rpow_pow hn0.le]
    norm_num

/-- Algebra of `Ψ^W` on the comparison window, with `p = n^{-1/3}`, `s = n^{ε/2}`: for
`η ≥ p²/s¹⁸` and `Im m ≤ K_s (2 p s + √η)`, `Ψ ≤ (√(3K_s) + 1) s¹⁸ p`. -/
private lemma aux_win_alg {n p s η M Ks : ℝ} (hn : 0 < n) (hp : 0 < p) (hs : 1 ≤ s)
    (hKs : 0 ≤ Ks) (hnp : n * p ^ 3 = 1) (hη : p ^ 2 / s ^ 18 ≤ η)
    (hM : M ≤ Ks * (2 * p * s + √η)) :
    √(M / (n * η)) + 1 / (n * η) ≤ (√(3 * Ks) + 1) * (s ^ 18 * p) := by
  have hs0 : 0 < s := by linarith
  have hs18 : 0 < s ^ 18 := by positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  set t := √η with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hη0
  have htt : t * t = η := Real.mul_self_sqrt hη0.le
  -- `p ≤ s⁹ t`
  have hpt : p ≤ s ^ 9 * t := by
    have h1 : p ^ 2 ≤ (s ^ 9 * t) ^ 2 := by
      have : (s ^ 9 * t) ^ 2 = s ^ 18 * η := by rw [mul_pow, ← htt]; ring
      rw [this]
      rwa [div_le_iff₀ hs18, mul_comm] at hη
    exact le_of_sq_le_sq h1 (by positivity)
  have hs9 : 1 ≤ s ^ 9 := one_le_pow₀ hs
  have hs10 : s ^ 10 ≤ s ^ 18 := pow_le_pow_right₀ hs (by norm_num)
  have hs19 : s ^ 19 ≤ s ^ 20 := pow_le_pow_right₀ hs (by norm_num)
  have hs9' : s ^ 9 ≤ s ^ 20 := pow_le_pow_right₀ hs (by norm_num)
  -- `p (2ps + t) ≤ 3 s²⁰ t²`
  have h1 : p * (2 * p * s + t) ≤ 3 * s ^ 20 * (t * t) := by
    have a1 : p * p ≤ s ^ 18 * (t * t) := by
      have := mul_le_mul hpt hpt hp.le (by positivity)
      calc p * p ≤ (s ^ 9 * t) * (s ^ 9 * t) := this
        _ = s ^ 18 * (t * t) := by ring
    have a2 : p * t ≤ s ^ 9 * (t * t) := by
      have := mul_le_mul_of_nonneg_right hpt ht0.le
      calc p * t ≤ s ^ 9 * t * t := this
        _ = s ^ 9 * (t * t) := by ring
    have a3 : 2 * (p * p) * s ≤ 2 * s ^ 19 * (t * t) := by
      calc 2 * (p * p) * s ≤ 2 * (s ^ 18 * (t * t)) * s := by gcongr
        _ = 2 * s ^ 19 * (t * t) := by ring
    have a4 : s ^ 19 * (t * t) ≤ s ^ 20 * (t * t) := by gcongr
    have a5 : s ^ 9 * (t * t) ≤ s ^ 20 * (t * t) := by gcongr
    nlinarith
  -- `2ps + t ≤ 3 s²⁰ p² n t²`
  have h2 : 2 * p * s + t ≤ 3 * s ^ 20 * (p ^ 2 * n * (t * t)) := by
    have e : 3 * s ^ 20 * (p ^ 2 * n * (t * t)) * p = 3 * s ^ 20 * (t * t) := by
      have : 3 * s ^ 20 * (p ^ 2 * n * (t * t)) * p = 3 * s ^ 20 * (t * t) * (n * p ^ 3) := by ring
      rw [this, hnp, mul_one]
    have : (2 * p * s + t) * p ≤ 3 * s ^ 20 * (p ^ 2 * n * (t * t)) * p := by
      rw [e]; linarith
    exact le_of_mul_le_mul_right this hp
  have h3 : M / (n * η) ≤ 3 * Ks * (s ^ 10 * p) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : Ks * (2 * p * s + t) ≤ Ks * (3 * s ^ 20 * (p ^ 2 * n * (t * t))) :=
      mul_le_mul_of_nonneg_left h2 hKs
    calc M ≤ Ks * (2 * p * s + t) := hM
      _ ≤ Ks * (3 * s ^ 20 * (p ^ 2 * n * (t * t))) := this
      _ = 3 * Ks * (s ^ 10 * p) ^ 2 * (n * η) := by rw [← htt]; ring
  have h4 : √(M / (n * η)) ≤ √(3 * Ks) * (s ^ 10 * p) := by
    calc √(M / (n * η)) ≤ √(3 * Ks * (s ^ 10 * p) ^ 2) := Real.sqrt_le_sqrt h3
      _ = √(3 * Ks) * (s ^ 10 * p) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h5 : 1 / (n * η) ≤ s ^ 18 * p := by
    have : p ^ 2 / s ^ 18 ≤ η := hη
    rw [div_le_iff₀ (by positivity)]
    have e : s ^ 18 * p * (n * (p ^ 2 / s ^ 18)) = 1 := by
      field_simp
      nlinarith [hnp]
    have : s ^ 18 * p * (n * (p ^ 2 / s ^ 18)) ≤ s ^ 18 * p * (n * η) := by gcongr
    linarith
  calc √(M / (n * η)) + 1 / (n * η) ≤ √(3 * Ks) * (s ^ 10 * p) + s ^ 18 * p :=
        add_le_add h4 h5
    _ ≤ √(3 * Ks) * (s ^ 18 * p) + s ^ 18 * p := by
        gcongr
    _ = (√(3 * Ks) + 1) * (s ^ 18 * p) := by ring

/-- `Ψ^W ≤ C N^{-1/3}` on the edge cone, for `N ≥ N₀`. -/
private lemma aux_psi_cone {τ : ℝ} (hτ : 0 < τ) {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) → ∀ c : ℝ,
      ∀ z ∈ edgeConeW τ N a c K, PsiW a z ≤ C * (N : ℝ) ^ (-1 / 3 : ℝ) := by
  obtain ⟨cs, Ks, hcs, hKs, N₀, hN₀, h⟩ := aux_im_m_le hτ
  set C₁ := Ks * √(K + 1) with hC₁
  set c' := cs / (K + 1) with hc'
  have hc'0 : 0 < c' := by positivity
  refine ⟨max (√C₁ + 1) (1 / √c' + 1 / c'), le_max_of_le_left (by positivity), N₀, hN₀,
    fun N hN a ha hSB c z hz => ?_⟩
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : 0 < (N : ℝ) := by linarith
  obtain ⟨hp, hp1, hnp, hp2⟩ := aux_p_facts hn1
  obtain ⟨hzD, hη, hc, hKz⟩ := hz
  have hzim : 0 < z.im := hzD.1
  unfold PsiW
  by_cases hnear : ‖z - (LpW a : ℂ)‖ ≤ cs
  · have him := h N hN a ha hSB z hzim hnear (K * z.im) hKz
    have hM : (mW a z).im ≤ C₁ * √z.im := by
      calc (mW a z).im ≤ Ks * √(K * z.im + z.im) := him
        _ = C₁ * √z.im := by
          rw [show K * z.im + z.im = (K + 1) * z.im by ring, Real.sqrt_mul (by linarith)]
          ring
    have := aux_cone_alg hn hp hnp (by rw [hp2]; exact hη) (by positivity) hM
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · push Not at hnear
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z - (LpW a : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
      abs_of_pos hzim] at hnorm
    have hfar : c' ≤ z.im := by
      rw [hc', div_le_iff₀ (by linarith)]
      nlinarith
    have := aux_far_alg hn hp hp1 hnp hc'0 hfar (aux_im_m_le_one hN1 a hzim)
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)

/-- (b) of Theorem 12.2 on the edge cone, for every `c_Ψ < 1/12`: `Im m^W ≤ K' √((K + 1)η)` near
`L₊`, `|m^W| ≤ τ⁻¹` away from it, and `η ≥ N^{-2/3}`. -/
theorem psiSmallW_edgeConeW {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {K cΨ : ℝ} (hK : 0 < K)
    (hcΨ : cΨ < 1 / 12) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ τ⁻¹ - 2) →
      StandingBoundW τ a (domW τ N) → PsiSmallW cΨ a (edgeConeW τ N a c K) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := aux_psi_cone hτ hK
  have hδ : 0 < 1 / 12 - cΨ := by linarith
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 12 - cΨ)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hlim.eventually_ge_atTop C)
  refine ⟨max N₀ N₁, fun N hN a ha hSB z hz => ?_⟩
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN₀.trans (le_of_max_le_left hN)
  have hn : 0 < (N : ℝ) := by linarith
  have h1 := h N (le_of_max_le_left hN) a ha hSB c z hz
  have h2 := hN₁ N (le_of_max_le_right hN)
  calc PsiW a z ≤ C * (N : ℝ) ^ (-1 / 3 : ℝ) := h1
    _ ≤ (N : ℝ) ^ (1 / 12 - cΨ) * (N : ℝ) ^ (-1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (-1 / 4 - cΨ) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring

/-- `Ψ^W ≤ C N^{-1/3+9ε}` on the comparison window, for `N ≥ N₀`. -/
private lemma aux_psi_win {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) →
      ∀ z ∈ edgeWinW τ N a ε, PsiW a z ≤ C * (N : ℝ) ^ (-1 / 3 + 9 * ε : ℝ) := by
  obtain ⟨cs, Ks, hcs, hKs, N₀, hN₀, h⟩ := aux_im_m_le hτ
  have hlim : Tendsto (fun N : ℕ => 3 * (N : ℝ) ^ (-(2 / 3 - ε) : ℝ)) atTop (𝓝 (3 * 0)) :=
    ((tendsto_rpow_neg_atTop (show 0 < 2 / 3 - ε by linarith)).comp
      tendsto_natCast_atTop_atTop).const_mul 3
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (show 3 * (0 : ℝ) < cs / 2 by linarith)))
  set c' := cs / 2 with hc'
  have hc'0 : 0 < c' := by positivity
  refine ⟨max (√(3 * Ks) + 1) (1 / √c' + 1 / c'), le_max_of_le_left (by positivity),
    max N₀ N₁, le_max_of_le_left hN₀, fun N hN a ha hSB z hz => ?_⟩
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hN1' : N₁ ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := hN₀.trans hN0
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : 0 < (N : ℝ) := by linarith
  obtain ⟨hp, hp1, hnp, hp2⟩ := aux_p_facts hn1
  set p := (N : ℝ) ^ (-1 / 3 : ℝ) with hpdef
  set s := (N : ℝ) ^ (ε / 2) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hn1 (by linarith)
  have hs18 : s ^ 18 = (N : ℝ) ^ (9 * ε) := by
    rw [hsdef, aux_rpow_pow hn.le]; congr 1; norm_num; ring
  have hs2 : s ^ 2 = (N : ℝ) ^ ε := by
    rw [hsdef, aux_rpow_pow hn.le]; congr 1; norm_num
  have hb : 3 * (N : ℝ) ^ (-2 / 3 + ε) = 3 * (p ^ 2 * s ^ 2) := by
    rw [hp2, hs2, ← Real.rpow_add hn]
  have hη0 : etaE N ε = p ^ 2 / s ^ 18 := by
    unfold etaE
    rw [hp2, hs18, ← Real.rpow_sub hn]
  have hT : (N : ℝ) ^ (-1 / 3 + 9 * ε : ℝ) = s ^ 18 * p := by
    rw [hs18, hpdef, ← Real.rpow_add hn]
    congr 1
    ring
  obtain ⟨hzD, hη, hz3⟩ := hz
  have hzim : 0 < z.im := hzD.1
  unfold PsiW
  rw [hT]
  by_cases hnear : ‖z - (LpW a : ℂ)‖ ≤ cs
  · have him := h N hN0 a ha hSB z hzim hnear _ hz3
    have hsq : √(3 * (N : ℝ) ^ (-2 / 3 + ε) + z.im) ≤ 2 * p * s + √z.im := by
      rw [hb]
      have e1 : √z.im * √z.im = z.im := Real.mul_self_sqrt hzim.le
      have e2 : 0 ≤ √z.im := Real.sqrt_nonneg _
      calc √(3 * (p ^ 2 * s ^ 2) + z.im) ≤ √((2 * p * s + √z.im) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have hps : 0 < p * s := mul_pos hp (by linarith)
            nlinarith [hps, mul_nonneg hps.le e2]
        _ = 2 * p * s + √z.im := Real.sqrt_sq (by positivity)
    have hM : (mW a z).im ≤ Ks * (2 * p * s + √z.im) :=
      him.trans (mul_le_mul_of_nonneg_left hsq hKs.le)
    have := aux_win_alg hn hp hs1 hKs.le hnp (by rw [← hη0]; exact hη) hM
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))
  · push Not at hnear
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z - (LpW a : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
      abs_of_pos hzim] at hnorm
    have hbc : 3 * (N : ℝ) ^ (-2 / 3 + ε) ≤ c' := by
      have := hN₁ N hN1'
      have e : (-(2 / 3 - ε) : ℝ) = -2 / 3 + ε := by ring
      rw [e] at this
      exact this.le
    have hfar : c' ≤ z.im := by
      linarith
    have := aux_far_alg hn hp hp1 hnp hc'0 hfar (aux_im_m_le_one hN1 a hzim)
    have hs18' : 1 ≤ s ^ 18 := one_le_pow₀ hs1
    calc _ ≤ (1 / √c' + 1 / c') * p := this
      _ ≤ max (√(3 * Ks) + 1) (1 / √c' + 1 / c') * p :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le
      _ ≤ max (√(3 * Ks) + 1) (1 / √c' + 1 / c') * (s ^ 18 * p) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_of_le_left (by positivity))
          nlinarith

/-- (b) of Theorem 12.2 on the comparison window, with `c₀ = (1/12 - 9ε)/2`:
`Ψ^W ≤ 2 N^{-1/3+9ε}` there (the reading `Ψ ≤ N^{-1/3+c}` of §12.5 with `c = 9ε`). -/
theorem psiSmallW_edgeWinW {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ τ⁻¹ - 2) →
      StandingBoundW τ a (domW τ N) →
      PsiSmallW ((1 / 12 - 9 * ε) / 2) a (edgeWinW τ N a ε) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := aux_psi_win hτ hε hε1
  have hδ : 0 < (1 / 12 - 9 * ε) / 2 := by linarith
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 / 12 - 9 * ε) / 2)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hlim.eventually_ge_atTop C)
  refine ⟨max N₀ N₁, fun N hN a ha hSB z hz => ?_⟩
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN₀.trans (le_of_max_le_left hN)
  have hn : 0 < (N : ℝ) := by linarith
  have h1 := h N (le_of_max_le_left hN) a ha hSB z hz
  have h2 := hN₁ N (le_of_max_le_right hN)
  calc PsiW a z ≤ C * (N : ℝ) ^ (-1 / 3 + 9 * ε : ℝ) := h1
    _ ≤ (N : ℝ) ^ ((1 / 12 - 9 * ε) / 2) * (N : ℝ) ^ (-1 / 3 + 9 * ε : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (-1 / 4 - (1 / 12 - 9 * ε) / 2) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring

/-- Theorem 12.2 (i) on the comparison window, for every `W` of the class: the entrywise law for
`(W^Gauss, D, 𝐃^W(τ, N))` gives the anisotropic law for `(W, A)` there (hypothesis (b) with
`c₀ = (1/12 - 9ε)/2`). -/
theorem anisoLawW_edgeWinW (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AnisotropicLawWAt N ε' D A W (edgeWinW τ N (specOf A) ε) := by
  have hc : 0 < (1 / 12 - 9 * ε) / 2 := by linarith
  obtain ⟨ε₁, D₁, hε₁, N₁, h1⟩ := general_wig_aniso_class τ ((1 / 12 - 9 * ε) / 2) C ε' D hτ hc hε'
  obtain ⟨N₂, h2⟩ := psiSmallW_edgeWinW hτ hε hε1
  refine ⟨ε₁, D₁, hε₁, max N₁ N₂, fun N hN Ω _ _ A W hA hnA hW hSB hE => ?_⟩
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ - 2 := fun i => by
    have := abs_specOf_le_norm hA i
    linarith
  have hnA' : ‖A‖ ≤ τ⁻¹ := by linarith
  exact h1 N (le_of_max_le_left hN) A W _ hA hnA' hW (spectralDomainW_edgeWinW τ N _ ε)
    (fun z hz => hSB z hz.1) (Or.inr (h2 N (le_of_max_le_right hN) _ ha hSB))
    (fun z hz => hE z hz.1)

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`, with `U Uᵀ = 1`, `Uᵀ U = 1`
and `A = U diag(λ) Uᵀ` for the eigenvalue vector `specOf A`. -/
private lemma aux_eig_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      A = U * diagonal (specOf A) * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [specOf_eq hA]
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- For `A = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w ≠ 0`, `(A − w)⁻¹` is the rotated
diagonal `(λₖ − w)⁻¹`. -/
private lemma aux_resolvent_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx A = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hAU]
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

/-- Conjugation by the complexification of a real orthogonal matrix preserves the operator norm. -/
private lemma aux_norm_conj {N : ℕ} {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (hUU' : Uᵀ * U = 1) (D : Matrix (Fin N) (Fin N) ℂ) :
    ‖(cplx U) * D * (cplx U)ᵀ‖ = ‖D‖ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hstar : star (cplx U) = (cplx U)ᵀ := by
    ext i j
    simp [cplx, Matrix.star_apply]
  have hmem : cplx U ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
    rw [Unitary.mem_iff, hstar]
    exact ⟨hP', hP⟩
  set V : unitary (Matrix (Fin N) (Fin N) ℂ) := ⟨cplx U, hmem⟩ with hV
  have e : (cplx U) * D * (cplx U)ᵀ =
      (V : Matrix (Fin N) (Fin N) ℂ) * D * ((star V : unitary (Matrix (Fin N) (Fin N) ℂ)) :
        Matrix (Fin N) (Fin N) ℂ) := by
    rw [Unitary.coe_star]
    simp [hV, hstar]
  rw [e, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

/-- `‖Π^W(z') − Π^W(z)‖ ≤ τ⁻² (|m^W(z') − m^W(z)| + |z' − z|)` under the standing bound at
`z` and `z'`. -/
private lemma aux_piW_sub_norm {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {z z' : ℂ}
    (hz : ∀ k, τ ≤ ‖-(mW (specOf A) z) + (specOf A k : ℂ) - z‖)
    (hz' : ∀ k, τ ≤ ‖-(mW (specOf A) z') + (specOf A k : ℂ) - z'‖) :
    ‖piW A z' - piW A z‖ ≤
      τ⁻¹ ^ 2 * (‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖) := by
  obtain ⟨U, hUU, hUU', hAU⟩ := aux_eig_decomp hA
  set x : ℂ → Fin N → ℂ := fun w k => (specOf A k : ℂ) - (mW (specOf A) w + w) with hx
  have hxb : ∀ w, (∀ k, τ ≤ ‖-(mW (specOf A) w) + (specOf A k : ℂ) - w‖) →
      ∀ k, τ ≤ ‖x w k‖ := by
    intro w hw k
    have h := hw k
    have e : -(mW (specOf A) w) + (specOf A k : ℂ) - w = x w k := by simp only [hx]; ring
    rwa [e] at h
  have hne : ∀ w, (∀ k, τ ≤ ‖-(mW (specOf A) w) + (specOf A k : ℂ) - w‖) → ∀ k, x w k ≠ 0 :=
    fun w hw k h0 => by
      have := hxb w hw k
      rw [h0, norm_zero] at this
      linarith
  have hpi : ∀ w, (∀ k, τ ≤ ‖-(mW (specOf A) w) + (specOf A k : ℂ) - w‖) →
      piW A w = (cplx U) * diagonal (fun k => (x w k)⁻¹) * (cplx U)ᵀ := fun w hw =>
    aux_resolvent_eq hUU hUU' hAU (hne w hw)
  have hdiff : piW A z' - piW A z =
      (cplx U) * diagonal (fun k => (x z' k)⁻¹ - (x z k)⁻¹) * (cplx U)ᵀ := by
    rw [hpi z' hz', hpi z hz, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  rw [hdiff, aux_norm_conj hUU hUU', Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have h1 := hxb z hz k
  have h2 := hxb z' hz' k
  have hn1 := hne z hz k
  have hn2 := hne z' hz' k
  rw [inv_sub_inv hn2 hn1, norm_div, norm_mul]
  have hnum : ‖x z k - x z' k‖ ≤ ‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖ := by
    have : x z k - x z' k = (mW (specOf A) z' - mW (specOf A) z) + (z' - z) := by
      simp only [hx]; ring
    rw [this]
    exact norm_add_le _ _
  rw [div_le_iff₀ (by positivity)]
  have hτ2 : τ⁻¹ ^ 2 * (τ * τ) = 1 := by field_simp
  have hmul : τ * τ ≤ ‖x z' k‖ * ‖x z k‖ := mul_le_mul h2 h1 hτ.le (by positivity)
  have hQ : 0 ≤ ‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖ := by positivity
  calc ‖x z k - x z' k‖ ≤ ‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖ := hnum
    _ = τ⁻¹ ^ 2 * (τ * τ) * (‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖) := by
        rw [hτ2, one_mul]
    _ = τ⁻¹ ^ 2 * (‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖) * (τ * τ) := by ring
    _ ≤ τ⁻¹ ^ 2 * (‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖) *
          (‖x z' k‖ * ‖x z k‖) := by gcongr

/-- Lipschitz bound for `m^W` along a horizontal segment at height `η`, from `|m^W'| ≤ Im m^W/η`:
if `Im m^W ≤ M` on the segment then `|m^W(z') − m^W(z)| ≤ (M/η) |z' − z|`. -/
private lemma aux_mW_sub_le {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z z' : ℂ} {η M : ℝ}
    (hη : 0 < η) (hz : z.im = η) (hz' : z'.im = η)
    (hM : ∀ w ∈ segment ℝ z z', (mW a w).im ≤ M) :
    ‖mW a z' - mW a z‖ ≤ M / η * ‖z' - z‖ := by
  have him : ∀ w ∈ segment ℝ z z', w.im = η := by
    intro w hw
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hz, hz']
    rw [← add_mul, hαβ, one_mul]
  have hder : ∀ w ∈ segment ℝ z z', ∃ m', HasDerivAt (mW a) m' w ∧ ‖m'‖ ≤ M / η := by
    intro w hw
    have hwim : 0 < w.im := by rw [him w hw]; exact hη
    obtain ⟨m', hm', hb⟩ := hasDerivAt_mW hN a hwim
    refine ⟨m', hm', hb.trans ?_⟩
    rw [him w hw]
    exact div_le_div_of_nonneg_right (hM w hw) hη.le
  refine Convex.norm_image_sub_le_of_norm_deriv_le (s := segment ℝ z z') (C := M / η)
    (fun w hw => ?_) (fun w hw => ?_) (convex_segment z z') (left_mem_segment ℝ z z')
    (right_mem_segment ℝ z z')
  · obtain ⟨m', hm', -⟩ := hder w hw
    exact hm'.differentiableAt
  · obtain ⟨m', hm', hb⟩ := hder w hw
    rw [hm'.deriv]
    exact hb

/-- The deterministic increment on the comparison window: for `z = E + iη`, `z' = E' + iη`,
`η = N^{-2/3-9ε}`, `|E - L₊|, |E' - L₊| ≤ 3 N^{-2/3+ε}`:
`‖Π^W(z') - Π^W(z)‖ ≤ K N^{-1/3+21ε/2}` (`|m^W'| ≤ Im m^W/η`, `Im m^W ≤ K √(κ + η)`, and
`‖Π^W‖ ≤ τ⁻¹`). -/
theorem piW_edgeWin_sub {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Matrix (Fin N) (Fin N) ℝ, A.IsHermitian →
      ‖A‖ ≤ τ⁻¹ - 3 → StandingBoundW τ (specOf A) (domW τ N) → ∀ E E' : ℝ,
      |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      |E' - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ‖piW A (E' + etaE N ε * Complex.I) - piW A (E + etaE N ε * Complex.I)‖ ≤
        K * (N : ℝ) ^ (-1 / 3 + 21 * ε / 2) := by
  obtain ⟨cs, Ks, hcs, hKs, N₀, hN₀, h⟩ := aux_im_m_le hτ
  have hlim : Tendsto (fun N : ℕ => 4 * (N : ℝ) ^ (-(2 / 3 - ε) : ℝ)) atTop (𝓝 (4 * 0)) :=
    ((tendsto_rpow_neg_atTop (show 0 < 2 / 3 - ε by linarith)).comp
      tendsto_natCast_atTop_atTop).const_mul 4
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (show 4 * (0 : ℝ) < min cs 1 by
      rw [mul_zero]; exact lt_min hcs one_pos)))
  refine ⟨τ⁻¹ ^ 2 * (12 * Ks + 6), max N₀ N₁, fun N hN A hA hnA hSB E E' hE hE' => ?_⟩
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hN1' : N₁ ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := hN₀.trans hN0
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : 0 < (N : ℝ) := by linarith
  obtain ⟨hp, hp1, hnp, hp2⟩ := aux_p_facts hn1
  set p := (N : ℝ) ^ (-1 / 3 : ℝ) with hpdef
  set s := (N : ℝ) ^ (ε / 2) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hn1 (by linarith)
  have hs0 : 0 < s := by linarith
  have hs18 : s ^ 18 = (N : ℝ) ^ (9 * ε) := by
    rw [hsdef, aux_rpow_pow hn.le]; congr 1; norm_num; ring
  have hs2 : s ^ 2 = (N : ℝ) ^ ε := by
    rw [hsdef, aux_rpow_pow hn.le]; congr 1; norm_num
  have hs21 : s ^ 21 = (N : ℝ) ^ (21 * ε / 2) := by
    rw [hsdef, aux_rpow_pow hn.le]; congr 1; norm_num; ring
  have hx : (N : ℝ) ^ (-2 / 3 + ε) = p ^ 2 * s ^ 2 := by
    rw [hp2, hs2, ← Real.rpow_add hn]
  have hη0 : etaE N ε = p ^ 2 / s ^ 18 := by
    unfold etaE
    rw [hp2, hs18, ← Real.rpow_sub hn]
  have hT : (N : ℝ) ^ (-1 / 3 + 21 * ε / 2 : ℝ) = p * s ^ 21 := by
    rw [hs21, hpdef, ← Real.rpow_add hn]
  have hxsmall : 4 * (p ^ 2 * s ^ 2) < min cs 1 := by
    have := hN₁ N hN1'
    have e : (-(2 / 3 - ε) : ℝ) = -2 / 3 + ε := by ring
    rw [e, hx] at this
    exact this
  have hxc : 4 * (p ^ 2 * s ^ 2) < cs := lt_of_lt_of_le hxsmall (min_le_left _ _)
  have hx1 : 4 * (p ^ 2 * s ^ 2) < 1 := lt_of_lt_of_le hxsmall (min_le_right _ _)
  set η₀ := etaE N ε with hη0def
  have hη0pos : 0 < η₀ := by rw [hη0]; positivity
  have hη0x : η₀ ≤ p ^ 2 * s ^ 2 := by
    rw [hη0]
    have h18 : 1 ≤ s ^ 18 := one_le_pow₀ hs1
    have h2 : 1 ≤ s ^ 2 := one_le_pow₀ hs1
    calc p ^ 2 / s ^ 18 ≤ p ^ 2 := div_le_self (by positivity) h18
      _ ≤ p ^ 2 * s ^ 2 := le_mul_of_one_le_right (by positivity) h2
  rw [hx] at hE hE'
  rw [hT]
  -- spectrum and `L₊`
  have hspec : ∀ i, |specOf A i| ≤ τ⁻¹ - 3 := fun i => (abs_specOf_le_norm hA i).trans hnA
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ - 2 := fun i => by linarith [hspec i]
  have hL := abs_LpW_le hN1 hspec
  have hτinv : 4 ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτ]
    norm_num
    linarith
  -- the two points of the window
  set z : ℂ := (E : ℂ) + (η₀ : ℂ) * Complex.I with hz
  set z' : ℂ := (E' : ℂ) + (η₀ : ℂ) * Complex.I with hz'
  have hzre : z.re = E := by simp [hz]
  have hzim : z.im = η₀ := by simp [hz]
  have hz're : z'.re = E' := by simp [hz']
  have hz'im : z'.im = η₀ := by simp [hz']
  have hmemD : ∀ F : ℝ, |F - LpW (specOf A)| ≤ p ^ 2 * s ^ 2 * 3 →
      ((F : ℂ) + (η₀ : ℂ) * Complex.I) ∈ domW τ N := by
    intro F hF
    have hre : ((F : ℂ) + (η₀ : ℂ) * Complex.I).re = F := by simp
    have him : ((F : ℂ) + (η₀ : ℂ) * Complex.I).im = η₀ := by simp
    have hη1 : η₀ ≤ 1 := by
      rw [hη0def]; unfold etaE
      exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    have hb1 : p ^ 2 * s ^ 2 * 3 ≤ 1 := by linarith
    refine ⟨by rw [him]; exact hη0pos, ?_, ?_, ?_⟩
    · rw [hre]
      have h1 : |F| ≤ |F - LpW (specOf A)| + |LpW (specOf A)| := by
        calc |F| = |(F - LpW (specOf A)) + LpW (specOf A)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    · rw [him, hη0def]
      unfold etaE
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · rw [him]
      linarith
  have hzD : z ∈ domW τ N := hmemD E (by linarith)
  have hz'D : z' ∈ domW τ N := hmemD E' (by linarith)
  -- operator-norm bound of the increment
  have hmain := aux_piW_sub_norm hτ hA (hSB z hzD) (hSB z' hz'D)
  -- `|z' - z| ≤ 2b`
  have hzz : ‖z' - z‖ ≤ 6 * (p ^ 2 * s ^ 2) := by
    have : z' - z = ((E' - E : ℝ) : ℂ) := by simp only [hz, hz']; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    calc |E' - E| = |(E' - LpW (specOf A)) - (E - LpW (specOf A))| := by ring_nf
      _ ≤ |E' - LpW (specOf A)| + |E - LpW (specOf A)| := abs_sub _ _
      _ ≤ 6 * (p ^ 2 * s ^ 2) := by linarith
  -- `Im m^W` on the segment
  have hseg : ∀ w ∈ segment ℝ z z', (mW (specOf A) w).im ≤ Ks * (2 * p * s) := by
    intro w hw
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    have hwim : (α • z + β • z').im = η₀ := by
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hzim, hz'im]
      rw [← add_mul, hαβ, one_mul]
    have hwre : (α • z + β • z').re = α * E + β * E' := by
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hzre, hz're]
    have hwL : |(α • z + β • z').re - LpW (specOf A)| ≤ 3 * (p ^ 2 * s ^ 2) := by
      rw [hwre]
      have e : α * E + β * E' - LpW (specOf A) =
          α * (E - LpW (specOf A)) + β * (E' - LpW (specOf A)) := by
        linear_combination (LpW (specOf A)) * hαβ
      rw [e]
      calc |α * (E - LpW (specOf A)) + β * (E' - LpW (specOf A))|
          ≤ |α * (E - LpW (specOf A))| + |β * (E' - LpW (specOf A))| := abs_add_le _ _
        _ = α * |E - LpW (specOf A)| + β * |E' - LpW (specOf A)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
        _ ≤ α * (3 * (p ^ 2 * s ^ 2)) + β * (3 * (p ^ 2 * s ^ 2)) := by gcongr
        _ = 3 * (p ^ 2 * s ^ 2) := by rw [← add_mul, hαβ, one_mul]
    have hwpos : 0 < (α • z + β • z').im := by rw [hwim]; exact hη0pos
    have hnorm := Complex.norm_le_abs_re_add_abs_im ((α • z + β • z') - (LpW (specOf A) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
      abs_of_pos hwpos] at hnorm
    have hcs' : ‖(α • z + β • z') - (LpW (specOf A) : ℂ)‖ ≤ cs := by
      rw [hwim] at hnorm
      linarith
    have him := h N hN0 (specOf A) ha hSB _ hwpos hcs' _ hwL
    rw [hwim] at him
    refine him.trans (mul_le_mul_of_nonneg_left ?_ hKs.le)
    have e1 : 0 ≤ 2 * p * s := by positivity
    calc √(3 * (p ^ 2 * s ^ 2) + η₀) ≤ √((2 * p * s) ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc 3 * (p ^ 2 * s ^ 2) + η₀ ≤ 3 * (p ^ 2 * s ^ 2) + p ^ 2 * s ^ 2 := by linarith
            _ = (2 * p * s) ^ 2 := by ring
      _ = 2 * p * s := Real.sqrt_sq e1
  have hlip := aux_mW_sub_le hN1 (specOf A) hη0pos hzim hz'im hseg
  -- combine
  have hq : Ks * (2 * p * s) / η₀ * ‖z' - z‖ ≤ 12 * Ks * (p * s ^ 21) := by
    have hnn : 0 ≤ Ks * (2 * p * s) / η₀ := by positivity
    calc Ks * (2 * p * s) / η₀ * ‖z' - z‖ ≤ Ks * (2 * p * s) / η₀ * (6 * (p ^ 2 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left hzz hnn
      _ = 12 * Ks * (p * s ^ 21) := by
          rw [hη0]
          field_simp
          ring
  have hsmall : 6 * (p ^ 2 * s ^ 2) ≤ 6 * (p * s ^ 21) := by
    have h1 : p ^ 2 ≤ p := pow_le_of_le_one hp.le hp1 (by norm_num)
    have h2 : s ^ 2 ≤ s ^ 21 := pow_le_pow_right₀ hs1 (by norm_num)
    have : p ^ 2 * s ^ 2 ≤ p * s ^ 21 := mul_le_mul h1 h2 (by positivity) hp.le
    linarith
  have hfin : ‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖ ≤ (12 * Ks + 6) * (p * s ^ 21) := by
    linarith [hlip, hq, hzz, hsmall]
  calc ‖piW A z' - piW A z‖
      ≤ τ⁻¹ ^ 2 * (‖mW (specOf A) z' - mW (specOf A) z‖ + ‖z' - z‖) := hmain
    _ ≤ τ⁻¹ ^ 2 * ((12 * Ks + 6) * (p * s ^ 21)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = τ⁻¹ ^ 2 * (12 * Ks + 6) * (p * s ^ 21) := by ring

/-- The edge cone at `τ = 1/4`, `K = 1` is a spectral domain along `a = spec(aEx N)`. -/
example (N : ℕ) (c : ℝ) : SpectralDomainW (1 / 4) N (edgeConeW (1 / 4) N (specOf (aEx N)) c 1) :=
  spectralDomainW_edgeConeW _ _ _ _ (by norm_num)

/-- The comparison window at `τ = 1/4` is a spectral domain along `a = spec(aEx N)`. -/
example (N : ℕ) (ε : ℝ) : SpectralDomainW (1 / 4) N (edgeWinW (1 / 4) N (specOf (aEx N)) ε) :=
  spectralDomainW_edgeWinW _ _ _ _

#print axioms Anisotropic.edgeConeW
#print axioms Anisotropic.edgeWinW
#print axioms Anisotropic.spectralDomainW_edgeConeW
#print axioms Anisotropic.spectralDomainW_edgeWinW
#print axioms Anisotropic.abs_LpW_le
#print axioms Anisotropic.psiSmallW_edgeConeW
#print axioms Anisotropic.psiSmallW_edgeWinW
#print axioms Anisotropic.anisoLawW_edgeWinW
#print axioms Anisotropic.piW_edgeWin_sub

end Anisotropic
