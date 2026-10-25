import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.Stability.EdgeTaylor
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Rigidity.Counting
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Gap
import Anisotropic.Rigidity.GaussCount

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 3.12 (`rigidity`), Theorems 3.14 (iii) (`rigidity_edge`) and 3.15 (iii) (`rigidity_bulk`) under (T_diag) -/

/-! ## The square-root inversion near an edge (real arithmetic) -/

/-- `max(1, 2c₂)`. -/
private def rmM (c₂ : ℝ) : ℝ := max 1 (2 * c₂)

/-- The spacing constant `L = 4 max(1, 2c₂)/c₁`. -/
private def rmL (c₁ c₂ : ℝ) : ℝ := 4 * rmM c₂ / c₁

/-- The threshold `K = 2 L max(1, 2c₂)²` between the edge and the spacing regimes. -/
private def rmK (c₁ c₂ : ℝ) : ℝ := 2 * rmL c₁ c₂ * rmM c₂ ^ 2

/-- If the density on `[v₁, v₂] ⊆ [0, t]` is at least `c₁√v₁` times the step, the mass between
the edge and distance `v` is at least `N c₁ √v v / 4`. -/
private lemma rm_mass_low {N c₁ t v : ℝ} {Φ : ℝ → ℝ} (hN : 0 < N) (hc₁ : 0 < c₁)
    (hΦ0 : Φ 0 = 0)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hv : 0 < v) (hvt : v ≤ t) : N * c₁ * √v * v / 4 ≤ Φ v := by
  have ha := hlo (v / 2) v (by positivity) (by linarith) hvt
  have hb := hlo 0 (v / 2) le_rfl (by positivity) (by linarith)
  rw [hΦ0, Real.sqrt_zero, mul_zero, zero_mul] at hb
  have hsq : √v / 2 ≤ √(v / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h := Real.sq_sqrt hv.le
    have e : (√v / 2) ^ 2 = (√v) ^ 2 / 4 := by ring
    rw [e, h]
    linarith
  have hc : N * c₁ * (√v / 2) * (v - v / 2) ≤ N * c₁ * √(v / 2) * (v - v / 2) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have he : N * c₁ * (√v / 2) * (v - v / 2) = N * c₁ * √v * v / 4 := by ring
  linarith

/-- `x ≤ E β` follows from `8 x³ i N² ≤ E³` when `β³ i N² = 1`. -/
private lemma rm_cube {x E β N : ℝ} {i : ℕ} (hβ : 0 < β) (hE : 0 ≤ E)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (h : 8 * x ^ 3 * i * N ^ 2 ≤ E ^ 3) : 2 * x ≤ E * β := by
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  calc (2 * x) ^ 3 = 8 * x ^ 3 * (β ^ 3 * i * N ^ 2) := by rw [hβi]; ring
    _ = β ^ 3 * (8 * x ^ 3 * i * N ^ 2) := by ring
    _ ≤ β ^ 3 * E ^ 3 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (E * β) ^ 3 := by ring

/-- The edge regime `i < K s` of the inversion: `|μ − u| ≤ u + y² ≤ E β`. -/
private lemma rm_core_small {N s y E β c₁ K t u μ : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hc₁ : 0 < c₁) (hK : 0 < K) (hβ : 0 < β)
    (hE : 0 ≤ E) (hβi : β ^ 3 * i * N ^ 2 = 1)
    (hu : 0 < u) (hut : u ≤ t) (hYt : y ^ 2 ≤ t)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, (i : ℝ) ≤ m v → μ ≤ v) (hexcl : -y ^ 2 ≤ μ) (hreg : (i : ℝ) < K * s)
    (hA2 : (K + 1) * s + 1 ≤ N * c₁ * y ^ 3 / 4)
    (hA3 : 128 * K ^ 3 * s ^ 3 ≤ c₁ ^ 2 * E ^ 3)
    (hA4 : 8 * K * s * y ^ 6 * N ^ 2 ≤ E ^ 3) :
    |μ - u| ≤ E * β := by
  have hY := rm_mass_low hN hc₁ hΦ0 hlo (v := y ^ 2) (by positivity) hYt
  rw [Real.sqrt_sq hy.le] at hY
  have hmY : (i : ℝ) ≤ m (y ^ 2) := by
    have := (abs_le.1 (hcount (y ^ 2) (by positivity) hYt)).1
    have e : N * c₁ * y * y ^ 2 / 4 = N * c₁ * y ^ 3 / 4 := by ring
    linarith
  have hμY : μ ≤ y ^ 2 := h1 _ hmY
  set r := √u with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hu
  have hru : r ^ 2 = u := Real.sq_sqrt hu.le
  have hur : N * c₁ * r * u / 4 ≤ i - 1 / 2 := by
    rw [← hΦu]; exact rm_mass_low hN hc₁ hΦ0 hlo hu hut
  have hA : N * c₁ * r ^ 3 ≤ 4 * K * s := by
    have e : N * c₁ * r * u = N * c₁ * r ^ 3 := by rw [← hru]; ring
    linarith
  have hB : (N * c₁ * r ^ 3) ^ 2 ≤ (4 * K * s) ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
  have hu3 : 8 * u ^ 3 * i * N ^ 2 ≤ E ^ 3 := by
    have hC : 8 * u ^ 3 * i * N ^ 2 * c₁ ^ 2 ≤ E ^ 3 * c₁ ^ 2 := by
      have e : 8 * u ^ 3 * i * N ^ 2 * c₁ ^ 2 = 8 * (N * c₁ * r ^ 3) ^ 2 * i := by
        rw [← hru]; ring
      rw [e]
      calc 8 * (N * c₁ * r ^ 3) ^ 2 * i ≤ 8 * (4 * K * s) ^ 2 * (K * s) := by
            have := hreg.le
            gcongr
        _ = 128 * K ^ 3 * s ^ 3 := by ring
        _ ≤ c₁ ^ 2 * E ^ 3 := hA3
        _ = E ^ 3 * c₁ ^ 2 := by ring
    exact le_of_mul_le_mul_right hC (by positivity)
  have hY3 : 8 * (y ^ 2) ^ 3 * i * N ^ 2 ≤ E ^ 3 := by
    calc 8 * (y ^ 2) ^ 3 * i * N ^ 2 ≤ 8 * (y ^ 2) ^ 3 * (K * s) * N ^ 2 := by
          have := hreg.le
          gcongr
      _ = 8 * K * s * y ^ 6 * N ^ 2 := by ring
      _ ≤ E ^ 3 := hA4
  have h3 := rm_cube hβ hE hβi hu3
  have h4 := rm_cube hβ hE hβi hY3
  have hy2 : 0 ≤ y ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The spacing regime `i ≥ K s` of the inversion: `|μ − u| ≤ L s β ≤ E β`. -/
private lemma rm_core_big {N s β c₁ c₂ M L t u μ E : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 1 ≤ s) (hc₁ : 0 < c₁) (hβ : 0 < β) (hM1 : 1 ≤ M) (hM2 : 2 * c₂ ≤ M)
    (hL : L * c₁ = 4 * M) (hL0 : 0 < L)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (hi : (1 : ℝ) ≤ i)
    (hu : 0 < u) (hut : u ≤ t / 2)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hhi : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → Φ v₂ - Φ v₁ ≤ N * c₂ * √v₂ * (v₂ - v₁))
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, (i : ℝ) ≤ m v → μ ≤ v) (h2 : ∀ v, μ < v → (i : ℝ) ≤ m v)
    (hreg : 2 * L * M ^ 2 * s ≤ i) (hA5 : L * s ≤ E) :
    |μ - u| ≤ E * β := by
  have hM0 : 0 < M := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  set r := √u with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hu
  have hru : r ^ 2 = u := Real.sq_sqrt hu.le
  set w := 1 / (N * β) with hw
  have hw0 : 0 < w := by positivity
  have hNβw : N * β * w = 1 := by rw [hw]; field_simp
  have hiw : (i : ℝ) = N * w ^ 3 := by
    have e1 : (i : ℝ) = 1 / (β ^ 3 * N ^ 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [e1, hw]
    field_simp
  have hhu := hhi 0 u le_rfl hu.le (by linarith)
  rw [hΦ0, hΦu, ← hr, sub_zero, sub_zero] at hhu
  have hw3 : w ^ 3 ≤ M * r ^ 3 := by
    have e : N * c₂ * r * u = N * (c₂ * r ^ 3) := by rw [← hru]; ring
    have h5 : N * w ^ 3 ≤ N * (2 * c₂ * r ^ 3) := by
      rw [← hiw]
      have : N * (2 * c₂ * r ^ 3) = 2 * (N * (c₂ * r ^ 3)) := by ring
      linarith
    have h6 : w ^ 3 ≤ 2 * c₂ * r ^ 3 := le_of_mul_le_mul_left h5 hN
    have h7 : 2 * c₂ * r ^ 3 ≤ M * r ^ 3 := mul_le_mul_of_nonneg_right hM2 (by positivity)
    linarith
  have hwr : w ≤ M * r := by
    by_contra hc
    have hc' : M * r < w := lt_of_not_ge hc
    have h5 : (M * r) ^ 3 < w ^ 3 := pow_lt_pow_left₀ hc' (by positivity) (by norm_num)
    have hM3 : M ≤ M ^ 3 := by
      have : 1 ≤ M ^ 2 := one_le_pow₀ hM1
      calc M = M * 1 := by ring
        _ ≤ M * M ^ 2 := mul_le_mul_of_nonneg_left this hM0.le
        _ = M ^ 3 := by ring
    have h6 : M * r ^ 3 ≤ (M * r) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hM3 (by positivity : (0 : ℝ) ≤ r ^ 3)
      calc M * r ^ 3 ≤ M ^ 3 * r ^ 3 := this
        _ = (M * r) ^ 3 := by ring
    linarith
  set δ := L * s * β with hδ
  have hδ0 : 0 < δ := by positivity
  have hδu : 2 * δ ≤ u := by
    have h5 : 2 * L * M ^ 2 * s * β ≤ w ^ 2 := by
      have h6 : 2 * L * M ^ 2 * s * β ≤ i * β := mul_le_mul_of_nonneg_right hreg hβ.le
      have e : (i : ℝ) * β = w ^ 2 := by
        rw [hiw]
        have : N * w ^ 3 * β = w ^ 2 * (N * β * w) := by ring
        rw [this, hNβw, mul_one]
      linarith
    have h6 : w ^ 2 ≤ M ^ 2 * u := by
      rw [← hru]
      have := pow_le_pow_left₀ hw0.le hwr 2
      calc w ^ 2 ≤ (M * r) ^ 2 := this
        _ = M ^ 2 * r ^ 2 := by ring
    have h7 : M ^ 2 * (2 * δ) ≤ M ^ 2 * u := by
      have : M ^ 2 * (2 * δ) = 2 * L * M ^ 2 * s * β := by rw [hδ]; ring
      linarith
    exact le_of_mul_le_mul_left h7 (by positivity)
  have hbig : 4 * s ≤ N * c₁ * r * δ := by
    have h5 : 1 ≤ M * (N * β * r) := by
      have : N * β * w ≤ N * β * (M * r) := mul_le_mul_of_nonneg_left hwr (by positivity)
      have e : N * β * (M * r) = M * (N * β * r) := by ring
      linarith
    have e : N * c₁ * r * δ = (L * c₁) * s * (N * β * r) := by rw [hδ]; ring
    rw [e, hL]
    have : 4 * s * 1 ≤ 4 * s * (M * (N * β * r)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    calc 4 * s = 4 * s * 1 := by ring
      _ ≤ 4 * s * (M * (N * β * r)) := this
      _ = 4 * M * s * (N * β * r) := by ring
  have hup : u - δ ≤ μ := by
    by_contra hc
    have hc' : μ < u - δ := lt_of_not_ge hc
    have hm := h2 _ hc'
    have hv0 : 0 ≤ u - δ := by linarith
    have hmass' := hlo (u - δ) u hv0 (by linarith) (by linarith)
    have hsq : r / 2 ≤ √(u - δ) := by
      rw [Real.le_sqrt (by positivity) hv0]
      have e : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
      rw [e, hru]
      linarith
    have hc2 := (abs_le.1 (hcount (u - δ) hv0 (by linarith))).2
    have h5 : N * c₁ * (r / 2) * δ ≤ N * c₁ * √(u - δ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ0.le
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : u - (u - δ) = δ := by ring
    rw [e] at hmass'
    have e2 : N * c₁ * (r / 2) * δ = (N * c₁ * r * δ) / 2 := by ring
    linarith
  have hlow : μ ≤ u + δ := by
    apply h1
    have hmass' := hlo u (u + δ) hu.le (by linarith) (by linarith)
    rw [← hr] at hmass'
    have e : u + δ - u = δ := by ring
    rw [e] at hmass'
    have hc2 := (abs_le.1 (hcount (u + δ) (by linarith) (by linarith))).1
    linarith
  have hδE : δ ≤ E * β := by
    rw [hδ]; exact mul_le_mul_of_nonneg_right hA5 hβ.le
  rw [abs_le]
  constructor <;> linarith

/-- The inversion near a square-root edge, in the distance `v` from the edge: `Φ(v)` is the
classical mass between the edge and distance `v` (density between `c₁√v` and `c₂√v`), `m(v)`
the empirical one, `u` the distance of `γ` (with `Φ(u) = i − 1/2`), `μ` that of the
eigenvalue. If `|m − Φ| ≤ s` on `[0, t]` and `μ ≥ −y²`, then `|μ − u| ≤ E β`, where
`β³ i N² = 1`. -/
private lemma rm_edge_core {N s y E β c₁ c₂ t u μ : ℝ} {i : ℕ} {Φ m : ℝ → ℝ}
    (hN : 0 < N) (hs : 1 ≤ s) (hy : 0 < y) (hc₁ : 0 < c₁) (hβ : 0 < β)
    (hβi : β ^ 3 * i * N ^ 2 = 1) (hi : 1 ≤ i)
    (hu : 0 < u) (hut : u ≤ t / 2) (hYt : y ^ 2 ≤ t)
    (hΦ0 : Φ 0 = 0) (hΦu : Φ u = i - 1 / 2)
    (hlo : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c₁ * √v₁ * (v₂ - v₁) ≤ Φ v₂ - Φ v₁)
    (hhi : ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → Φ v₂ - Φ v₁ ≤ N * c₂ * √v₂ * (v₂ - v₁))
    (hcount : ∀ v, 0 ≤ v → v ≤ t → |m v - Φ v| ≤ s)
    (h1 : ∀ v, (i : ℝ) ≤ m v → μ ≤ v) (h2 : ∀ v, μ < v → (i : ℝ) ≤ m v)
    (hexcl : -y ^ 2 ≤ μ)
    (hA2 : (rmK c₁ c₂ + 1) * s + 1 ≤ N * c₁ * y ^ 3 / 4)
    (hA3 : 128 * rmK c₁ c₂ ^ 3 * s ^ 3 ≤ c₁ ^ 2 * E ^ 3)
    (hA4 : 8 * rmK c₁ c₂ * s * y ^ 6 * N ^ 2 ≤ E ^ 3)
    (hA5 : rmL c₁ c₂ * s ≤ E) :
    |μ - u| ≤ E * β := by
  have hM1 : 1 ≤ rmM c₂ := le_max_left _ _
  have hM2 : 2 * c₂ ≤ rmM c₂ := le_max_right _ _
  have hM0 : 0 < rmM c₂ := by linarith
  have hL : rmL c₁ c₂ * c₁ = 4 * rmM c₂ := by unfold rmL; field_simp
  have hL0 : 0 < rmL c₁ c₂ := by unfold rmL; positivity
  have hK0 : 0 < rmK c₁ c₂ := by unfold rmK; positivity
  have hE0 : 0 ≤ E := le_trans (by positivity) hA5
  have hi0 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  by_cases hreg : (i : ℝ) < rmK c₁ c₂ * s
  · exact rm_core_small hN (by linarith) hy hc₁ hK0 hβ hE0 hβi hu (by linarith) hYt hΦ0 hΦu hlo
      hcount h1 hexcl hreg hA2 hA3 hA4
  · exact rm_core_big hN hs hc₁ hβ hM1 hM2 hL hL0 hβi hi0 hu hut hΦ0 hΦu hlo hhi hcount h1 h2
      (le_of_not_gt hreg) hA5

/-! ## The measure `ϱ`, the classical count `n`, the edges and `supp ϱ` -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma rm_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
  refine ⟨hN, Nat.pos_of_ne_zero hM, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
    have : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at this
    simp at this
  have hgap := h.Sigma_gap
  have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul, hall]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
    simp [Set.indicator_of_mem h0]
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [happ, hM', ENNReal.toReal_one] at hgap
  linarith

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma rm_anti {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, -, hS⟩ := rm_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (by omega) (by omega)).trans (ih (by omega))

/-- `0 ≤ a_k` for `1 ≤ k ≤ 2p`. -/
private lemma rm_edge_nonneg {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ 2 * numBands N σ) : 0 ≤ edgeVal N σ k := by
  obtain ⟨hN, -, hS⟩ := rm_facts h
  exact (edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hk
    hkp).1

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rm_varrho_apply (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma rm_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) =
      varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- If `ρ ≥ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≥ N c₀ (y − x)`. -/
private lemma rm_nClass_sub_ge {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, c₀ ≤ rhoDens N σ u) :
    N * c₀ * (y - x) ≤ nClass N σ x - nClass N σ y := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rm_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hge : ENNReal.ofReal (c₀ * (y - x)) ≤ varrho N σ (Set.Ico x y) := by
    rw [rm_varrho_apply σ measurableSet_Ico hsub]
    calc ENNReal.ofReal (c₀ * (y - x))
        = ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
      _ ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
  have h1 : c₀ * (y - x) ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * c₀ * (y - x) = N * (c₀ * (y - x)) := by ring
    _ ≤ N * (varrho N σ (Set.Ico x y)).toReal := mul_le_mul_of_nonneg_left h1 hN0

/-- If `ρ ≤ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≤ N c₀ (y − x)`. -/
private lemma rm_nClass_sub_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, rhoDens N σ u ≤ c₀) :
    nClass N σ x - nClass N σ y ≤ N * c₀ * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rm_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hle : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (c₀ * (y - x)) := by
    rw [rm_varrho_apply σ measurableSet_Ico hsub]
    calc ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u)
        ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
      _ = ENNReal.ofReal (c₀ * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ c₀ * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal ≤ N * (c₀ * (y - x)) :=
        mul_le_mul_of_nonneg_left h1 hN0
    _ = N * c₀ * (y - x) := by ring

/-- A positive point of `supp ϱ` lies in a band `[a_{2k}, a_{2k−1}]`, `1 ≤ k ≤ p`. -/
private lemma rm_supp {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) (hy0 : 0 < y) :
    ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ edgeVal N σ (2 * k) ≤ y ∧ y ≤ edgeVal N σ (2 * k - 1) := by
  obtain ⟨hN, -, hS⟩ := rm_facts h
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ h.nonneg hN hS hy0).1 hy
  exact ⟨k, hk1, hk2, hyk.1, hyk.2⟩

/-- `a_1 ∈ supp ϱ` when `a_1 > 0`. -/
private lemma rm_supp_ne {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (h1 : 0 < edgeVal N σ 1) : (varrho N σ).support.Nonempty := by
  obtain ⟨hN, -, hS⟩ := rm_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  refine ⟨edgeVal N σ 1, (mem_support_varrho_iff N σ h.nonneg hN hS h1).2 ⟨1, le_rfl, hp, ?_⟩⟩
  have := rm_anti h (i := 1) (j := 2) le_rfl (by norm_num) (by omega)
  exact ⟨by simpa using this, by simp⟩

/-- A point `x ≥ r` at distance `≥ r` from every band is at distance `≥ r` from `supp ϱ`. -/
private lemma rm_dist {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {x r : ℝ}
    (hr : 0 ≤ r) (hx : r ≤ x) (ha1 : 0 < edgeVal N σ 1)
    (h : ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x) :
    r ≤ Metric.infDist x (varrho N σ).support := by
  have hne := rm_supp_ne hda ha1
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [Real.dist_eq]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨l, hl1, hl2, hyl1, hyl2⟩ := rm_supp hda hy hy0
  rcases h l hl1 hl2 with h' | h'
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- A point in the gap above the band `k` (at distance `≥ r` from `a_{2k−1}` and, for `k ≥ 2`,
from `a_{2k−2}`) is at distance `≥ r` from every band. -/
private lemma rm_bands_above {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x r : ℝ} (h1 : edgeVal N σ (2 * k - 1) + r ≤ x)
    (h2 : 2 ≤ k → x + r ≤ edgeVal N σ (2 * k - 2)) :
    ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x := by
  intro l hl1 hl2
  rcases le_or_gt k l with hkl | hkl
  · right
    have := rm_anti hda (i := 2 * k - 1) (j := 2 * l - 1) (by omega) (by omega) (by omega)
    linarith
  · left
    have := rm_anti hda (i := 2 * l) (j := 2 * k - 2) (by omega) (by omega) (by omega)
    linarith [h2 (by omega)]

/-- A point in the gap below the band `k` (at distance `≥ r` from `a_{2k}` and, for `k < p`,
from `a_{2k+1}`) is at distance `≥ r` from every band. -/
private lemma rm_bands_below {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x r : ℝ} (h1 : x + r ≤ edgeVal N σ (2 * k))
    (h2 : k < numBands N σ → edgeVal N σ (2 * k + 1) + r ≤ x) :
    ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x := by
  intro l hl1 hl2
  rcases le_or_gt l k with hkl | hkl
  · left
    have := rm_anti hda (i := 2 * l) (j := 2 * k) (by omega) (by omega) (by omega)
    linarith
  · right
    have := rm_anti hda (i := 2 * k + 1) (j := 2 * l - 1) (by omega) (by omega) (by omega)
    linarith [h2 (by omega)]

/-- `d_k ≤ M ∧ N` for `1 ≤ k ≤ p`, and `d_p = M ∧ N`. -/
private lemma rm_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    cumCount N σ k ≤ min M N ∧ cumCount N σ (numBands N σ) = min M N := by
  obtain ⟨hN, hM, hS⟩ := rm_facts hda
  have hp := (card_innerCrit N σ hda.nonneg hN hS).2
  have hsum := (Ni_sum N σ hσ hN hM).2
  have hnn : ∀ l ∈ Finset.Icc 1 (numBands N σ), l ∉ Finset.Icc 1 k →
      0 ≤ bandCount N σ l := fun l _ _ => by unfold bandCount; positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => bandCount N σ l)
    (Finset.Icc_subset_Icc le_rfl hkp) hnn
  obtain ⟨hc1, -, -⟩ := cumCount_spec hda hk hkp
  obtain ⟨hcp, -, -⟩ := cumCount_spec hda hp le_rfl
  rw [hsum] at hle hcp
  rw [← hc1] at hle
  constructor
  · have : (cumCount N σ k : ℝ) ≤ ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hle
    exact_mod_cast this
  · have : (cumCount N σ (numBands N σ) : ℝ) = ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hcp
    exact_mod_cast this

/-- `Q_N` is symmetric. -/
private lemma rm_herm {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := isHermitian_conjTranspose_mul_mul Xm hS.isHermitian
  simpa [QN, conjTranspose_eq_transpose_of_trivial] using this

/-! ## Eigenvalues and the counting function -/

/-- If `n_A(x) > 0`, some eigenvalue is `≥ x`. -/
private lemma rm_count_pos {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} {x : ℝ}
    (h : 0 < eigCount A x) : ∃ l, x ≤ specOf A l := by
  unfold eigCount at h
  obtain ⟨l, hl⟩ := Finset.card_pos.1 h
  exact ⟨l, (Finset.mem_filter.1 hl).2⟩

/-- If `n_A(x₂) < n_A(x₁)`, some eigenvalue lies in `[x₁, x₂)`. -/
private lemma rm_count_gap {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} {x₁ x₂ : ℝ}
    (h : eigCount A x₂ < eigCount A x₁) : ∃ l, x₁ ≤ specOf A l ∧ specOf A l < x₂ := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  have : eigCount A x₁ ≤ eigCount A x₂ := by
    unfold eigCount
    exact Finset.card_le_card fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hc l hl
  omega

/-- No eigenvalue `≥ x₀`: then `λ_j < x₀`. -/
private lemma rm_above1 {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {j : ℕ}
    (hj : 1 ≤ j) (hjK : j ≤ K) {x₀ : ℝ} (hnone : ∀ l, x₀ ≤ specOf A l → False) :
    sortedEig A j < x₀ := by
  by_contra hc
  have := (sortedEig_ge_iff hA hj hjK x₀).1 (not_lt.1 hc)
  obtain ⟨l, hl⟩ := rm_count_pos (A := A) (x := x₀) (by omega)
  exact hnone l hl

/-- `n_A(P) < j` and no eigenvalue in `[x₀, P)`: then `λ_j < x₀`. -/
private lemma rm_above2 {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {j : ℕ}
    (hj : 1 ≤ j) (hjK : j ≤ K) {x₀ P : ℝ} (hP : eigCount A P < j)
    (hnone : ∀ l, x₀ ≤ specOf A l → specOf A l < P → False) : sortedEig A j < x₀ := by
  by_contra hc
  have := (sortedEig_ge_iff hA hj hjK x₀).1 (not_lt.1 hc)
  obtain ⟨l, h1, h2⟩ := rm_count_gap (A := A) (x₁ := x₀) (x₂ := P) (by omega)
  exact hnone l h1 h2

/-- `n_A(P) ≥ j` and no eigenvalue in `[P, x₀)`: then `λ_j ≥ x₀`. -/
private lemma rm_below {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {j : ℕ}
    (hj : 1 ≤ j) (hjK : j ≤ K) {x₀ P : ℝ} (hP : j ≤ eigCount A P)
    (hnone : ∀ l, P ≤ specOf A l → specOf A l < x₀ → False) : x₀ ≤ sortedEig A j := by
  by_contra hc
  have h1 : ¬ j ≤ eigCount A x₀ := fun h => hc ((sortedEig_ge_iff hA hj hjK x₀).2 h)
  obtain ⟨l, h2, h3⟩ := rm_count_gap (A := A) (x₁ := P) (x₂ := x₀) (by omega)
  exact hnone l h2 h3

/-! ## The inversion at a regular edge and in the bulk -/

/-- The lower constant `1/(π √C₂(τ))` of the square-root density. -/
private def rmC1 (τ : ℝ) : ℝ := 1 / (Real.pi * √(edgeC2 τ))

/-- The upper constant `2/(π √c₂(τ))` of the square-root density. -/
private def rmC2 (τ : ℝ) : ℝ := 2 / (Real.pi * √(edgec2 τ))

private lemma rm_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeC2 τ ∧ 0 < edgec2 τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  refine ⟨by unfold edgeC2 edgeCx; positivity, by unfold edgec2 edgeCx; positivity⟩

private lemma rm_C1_pos {τ : ℝ} (hτ : 0 < τ) : 0 < rmC1 τ := by
  have := (rm_C_pos hτ).1; unfold rmC1; positivity

/-- `c₁ √d ≤ ρ ≤ c₂ √d` on the band side of a regular edge, `d` the distance to the edge
(proof of Lemma A.4). -/
private lemma rm_rho_edge {τ : ℝ} {σ : Fin M → ℝ} {l : ℕ} (hda : DensityAssumptions τ N σ)
    (hl : RegularEdge τ N σ l) {x : ℝ} (hx : |x - edgeVal N σ l| ≤ edgeTau0 τ)
    (hside : (-1 : ℝ) ^ (l + 1) * (x - edgeVal N σ l) ≤ 0) :
    rmC1 τ * √|x - edgeVal N σ l| ≤ rhoDens N σ x ∧
      rhoDens N σ x ≤ rmC2 τ * √|x - edgeVal N σ l| := by
  obtain ⟨h1, h2⟩ := (rhoDens_edge hda hl hx).1 hside
  obtain ⟨hC2, hc2⟩ := rm_C_pos hda.pos
  rw [Real.sqrt_div' _ hC2.le] at h1
  rw [Real.sqrt_div' _ hc2.le] at h2
  have hπ := Real.pi_pos
  have hsC := Real.sqrt_pos.2 hC2
  have hsc := Real.sqrt_pos.2 hc2
  set d := √|x - edgeVal N σ l|
  constructor
  · have e : rmC1 τ * d = d / √(edgeC2 τ) / Real.pi := by unfold rmC1; field_simp
    rw [e, div_le_iff₀ hπ]
    linarith
  · have e : rmC2 τ * d = 2 * (d / √(edgec2 τ)) / Real.pi := by unfold rmC2; field_simp
    rw [e, le_div_iff₀ hπ]
    linarith

/-- `β = i^{−1/3} N^{−2/3}` satisfies `β > 0` and `β³ i N² = 1`. -/
private lemma rm_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ)) ∧
      (a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ))) ^ 3 * a * b ^ 2 = 1 := by
  refine ⟨by positivity, ?_⟩
  have e1 : (a ^ (-(1 / 3 : ℝ))) ^ 3 = a⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
    exact Real.rpow_neg_one a
  have e2 : (b ^ (-(2 / 3 : ℝ))) ^ 3 = (b ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num
  rw [mul_pow, e1, e2]
  field_simp

/-- The mass bounds below an upper edge `a`: if `c √(a − x) ≤ ρ(x)` on `[a − t, a]`, then
`n(a − v₂) − n(a − v₁) ≥ N c √v₁ (v₂ − v₁)` for `0 ≤ v₁ ≤ v₂ ≤ t`. -/
private lemma rm_lo_up {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (hat : t < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a - t ≤ x → x ≤ a → c * √(a - x) ≤ rhoDens N σ x) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c * √v₁ * (v₂ - v₁) ≤
      (nClass N σ (a - v₂) - nClass N σ a) - (nClass N σ (a - v₁) - nClass N σ a) := by
  intro v₁ v₂ h0 h12 h2t
  have := rm_nClass_sub_ge (N := N) hσ hN (x := a - v₂) (y := a - v₁) (c₀ := c * √v₁)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.2])) hc)
        (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
  have e : a - v₁ - (a - v₂) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The upper mass bound below an upper edge `a` (density `≤ c √(a − x)`). -/
private lemma rm_hi_up {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (hat : t < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a - t ≤ x → x ≤ a → rhoDens N σ x ≤ c * √(a - x)) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t →
      (nClass N σ (a - v₂) - nClass N σ a) - (nClass N σ (a - v₁) - nClass N σ a) ≤
        N * c * √v₂ * (v₂ - v₁) := by
  intro v₁ v₂ h0 h12 h2t
  have := rm_nClass_sub_le (N := N) hσ hN (x := a - v₂) (y := a - v₁) (c₀ := c * √v₂)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.1])) hc)
  have e : a - v₁ - (a - v₂) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The mass bounds above a lower edge `a` (density `≥ c √(x − a)` on `[a, a + t]`). -/
private lemma rm_lo_dn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a ≤ x → x ≤ a + t → c * √(x - a) ≤ rhoDens N σ x) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t → N * c * √v₁ * (v₂ - v₁) ≤
      (nClass N σ a - nClass N σ (a + v₂)) - (nClass N σ a - nClass N σ (a + v₁)) := by
  intro v₁ v₂ h0 h12 h2t
  have := rm_nClass_sub_ge (N := N) hσ hN (x := a + v₁) (y := a + v₂) (c₀ := c * √v₁)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.1])) hc)
        (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
  have e : a + v₂ - (a + v₁) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- The upper mass bound above a lower edge `a` (density `≤ c √(x − a)`). -/
private lemma rm_hi_dn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a t c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c)
    (hρ : ∀ x, a ≤ x → x ≤ a + t → rhoDens N σ x ≤ c * √(x - a)) :
    ∀ v₁ v₂, 0 ≤ v₁ → v₁ ≤ v₂ → v₂ ≤ t →
      (nClass N σ a - nClass N σ (a + v₂)) - (nClass N σ a - nClass N σ (a + v₁)) ≤
        N * c * √v₂ * (v₂ - v₁) := by
  intro v₁ v₂ h0 h12 h2t
  have := rm_nClass_sub_le (N := N) hσ hN (x := a + v₁) (y := a + v₂) (c₀ := c * √v₂)
    (by linarith) (by linarith) (by positivity) fun x hx =>
      le_trans (hρ x (by linarith [hx.1]) (by linarith [hx.2]))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.2])) hc)
  have e : a + v₂ - (a + v₁) = v₂ - v₁ := by ring
  rw [e] at this
  linarith

/-- Rigidity at the upper edge `a_{2k−1}` of the band `k` (regular at `τᵣ`): if
`γ_{k,i} ≥ a_{2k−1} − t/2`, the count is within `s` on `[a_{2k−1} ± t]` and
`λ_{k,i} ≤ a_{2k−1} + y²`, then `|λ_{k,i} − γ_{k,i}| ≤ E i^{−1/3} N^{−2/3}`. -/
private lemma rm_edge_upper {τr t s y E : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τr N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {k i : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hreg : RegularEdge τr N σ (2 * k - 1))
    (ht0 : t ≤ edgeTau0 τr) (htτ : t ≤ τr / 2) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat N σ k)
    (hγ : edgeVal N σ (2 * k - 1) - t / 2 ≤ gammaBand N σ k i)
    (hcount : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k - 1) - t) (edgeVal N σ (2 * k - 1) + t),
      |(eigCount A E : ℝ) - nClass N σ E| ≤ s)
    (hexcl : sortedEig A (cumCount N σ (k - 1) + i) ≤ edgeVal N σ (2 * k - 1) + y ^ 2)
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ t)
    (hA2 : (rmK (rmC1 τr) (rmC2 τr) + 1) * s + 1 ≤ N * rmC1 τr * y ^ 3 / 4)
    (hA3 : 128 * rmK (rmC1 τr) (rmC2 τr) ^ 3 * s ^ 3 ≤ rmC1 τr ^ 2 * E ^ 3)
    (hA4 : 8 * rmK (rmC1 τr) (rmC2 τr) * s * y ^ 6 * N ^ 2 ≤ E ^ 3)
    (hA5 : rmL (rmC1 τr) (rmC2 τr) * s ≤ E) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
      E * (i : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨hN0, -, -⟩ := rm_facts hda
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτr := hda.pos
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hdk := (rm_cum hda hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjMN : cumCount N σ (k - 1) + i ≤ min M N := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := hjMN.trans (min_le_right _ _)
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 hjMN
  have hmem := gammaBand_mem hda hσ hk hkp hi hiN
  have hna := (nClass_edgeVal hda hk hkp).1
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  rw [hγdef] at hmem hγ ⊢
  set j := cumCount N σ (k - 1) + i with hj
  set γ := gammaLoc N σ j with hγd
  set a := edgeVal N σ (2 * k - 1) with ha
  set lam := sortedEig A j with hlam
  set d := cumCount N σ (k - 1) with hd
  have haτ : τr ≤ a := hreg.2.2.1
  have ht : 0 ≤ t := le_trans (by positivity) hYt
  have hρ : ∀ x, a - t ≤ x → x ≤ a →
      rmC1 τr * √(a - x) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rmC2 τr * √(a - x) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τr := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k - 1 + 1) * (x - a) ≤ 0 := by
      rw [show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num; linarith
    have := rm_rho_edge hda hreg hx hside
    rwa [abs_of_nonpos (by linarith), neg_sub] at this
  have hc1 := rm_C1_pos hτr
  have hc2 : 0 < rmC2 τr := by unfold rmC2; have := (rm_C_pos hτr).2; positivity
  obtain ⟨hβ, hβi⟩ := rm_beta (a := (i : ℝ)) (b := (N : ℝ)) (by exact_mod_cast hi) hNr
  have hjr : (j : ℝ) = d + i := by rw [hj]; push_cast; ring
  have key := rm_edge_core (N := (N : ℝ)) (i := i) (t := t)
    (Φ := fun v => nClass N σ (a - v) - nClass N σ a)
    (m := fun v => (eigCount A (a - v) : ℝ) - nClass N σ a)
    (u := a - γ) (μ := a - lam) hNr hs hy hc1 hβ hβi hi
    (by linarith [hmem.2]) (by linarith) hYt (by simp)
    (by simp only [sub_sub_cancel]; rw [hnγ, hna, hjr]; ring)
    (rm_lo_up hda.nonneg hN0 (by linarith) hc1.le fun x h1 h2 => (hρ x h1 h2).1)
    (rm_hi_up hda.nonneg hN0 (by linarith) hc2.le fun x h1 h2 => (hρ x h1 h2).2)
    (fun v h0 hv => by
      have := hcount (a - v) ⟨by linarith, by linarith⟩
      rwa [show (eigCount A (a - v) : ℝ) - nClass N σ a - (nClass N σ (a - v) - nClass N σ a) =
        (eigCount A (a - v) : ℝ) - nClass N σ (a - v) by ring])
    (fun v hv => by
      have h3 : j ≤ eigCount A (a - v) := by
        have : (j : ℝ) ≤ eigCount A (a - v) := by rw [hjr]; linarith
        exact_mod_cast this
      have := (sortedEig_ge_iff hA hj1 hjN (a - v)).2 h3
      linarith)
    (fun v hv => by
      have h3 := (sortedEig_ge_iff hA hj1 hjN (a - v)).1 (by linarith)
      have : (j : ℝ) ≤ eigCount A (a - v) := by exact_mod_cast h3
      rw [hjr] at this
      linarith)
    (by linarith) hA2 hA3 hA4 hA5
  rw [show a - lam - (a - γ) = -(lam - γ) by ring, abs_neg] at key
  rw [mul_assoc]
  exact key

/-- Rigidity at the lower edge `a_{2k}` of the band `k` (regular at `τᵣ`): if
`γ_{k,i} ≤ a_{2k} + t/2`, the count is within `s` on `[a_{2k} ± t]` and
`λ_{k,i} ≥ a_{2k} − y²`, then `|λ_{k,i} − γ_{k,i}| ≤ E (N_k + 1 − i)^{−1/3} N^{−2/3}`. -/
private lemma rm_edge_lower {τr t s y E : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τr N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {k i : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hreg : RegularEdge τr N σ (2 * k))
    (ht0 : t ≤ edgeTau0 τr) (hi : 1 ≤ i) (hiN : i ≤ bandNat N σ k)
    (hγ : gammaBand N σ k i ≤ edgeVal N σ (2 * k) + t / 2)
    (hcount : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) - t) (edgeVal N σ (2 * k) + t),
      |(eigCount A E : ℝ) - nClass N σ E| ≤ s)
    (hexcl : edgeVal N σ (2 * k) - y ^ 2 ≤ sortedEig A (cumCount N σ (k - 1) + i))
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ t)
    (hA2 : (rmK (rmC1 τr) (rmC2 τr) + 1) * s + 1 ≤ N * rmC1 τr * y ^ 3 / 4)
    (hA3 : 128 * rmK (rmC1 τr) (rmC2 τr) ^ 3 * s ^ 3 ≤ rmC1 τr ^ 2 * E ^ 3)
    (hA4 : 8 * rmK (rmC1 τr) (rmC2 τr) * s * y ^ 6 * N ^ 2 ≤ E ^ 3)
    (hA5 : rmL (rmC1 τr) (rmC2 τr) * s ≤ E) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
      E * ((bandNat N σ k + 1 - i : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨hN0, -, -⟩ := rm_facts hda
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτr := hda.pos
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hdk := (rm_cum hda hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjMN : cumCount N σ (k - 1) + i ≤ min M N := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := hjMN.trans (min_le_right _ _)
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 hjMN
  have hmem := gammaBand_mem hda hσ hk hkp hi hiN
  have haτ : τr ≤ edgeVal N σ (2 * k) := hreg.2.2.1
  have hna := (nClass_edgeVal hda hk hkp).2 (by linarith)
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  rw [hγdef] at hmem hγ ⊢
  set j := cumCount N σ (k - 1) + i with hj
  set γ := gammaLoc N σ j with hγd
  set a := edgeVal N σ (2 * k) with ha
  set lam := sortedEig A j with hlam
  set d := cumCount N σ (k - 1) with hd
  set i' := bandNat N σ k + 1 - i with hi'
  have hi'1 : 1 ≤ i' := by omega
  have hi'r : (i' : ℝ) = bandNat N σ k + 1 - i := by
    rw [hi', Nat.cast_sub (by omega)]; push_cast; ring
  have hdkr : (cumCount N σ k : ℝ) = d + bandNat N σ k := by rw [← hcs]; push_cast; ring
  have ht : 0 ≤ t := le_trans (by positivity) hYt
  have hρ : ∀ x, a ≤ x → x ≤ a + t →
      rmC1 τr * √(x - a) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rmC2 τr * √(x - a) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τr := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k + 1) * (x - a) ≤ 0 := by
      rw [pow_succ, pow_mul]; norm_num; linarith
    have := rm_rho_edge hda hreg hx hside
    rwa [abs_of_nonneg (by linarith)] at this
  have hc1 := rm_C1_pos hτr
  have hc2 : 0 < rmC2 τr := by unfold rmC2; have := (rm_C_pos hτr).2; positivity
  obtain ⟨hβ, hβi⟩ := rm_beta (a := (i' : ℝ)) (b := (N : ℝ)) (by exact_mod_cast hi'1) hNr
  have hjr : (j : ℝ) = d + i := by rw [hj]; push_cast; ring
  have key := rm_edge_core (N := (N : ℝ)) (i := i') (t := t)
    (Φ := fun v => nClass N σ a - nClass N σ (a + v))
    (m := fun v => nClass N σ a - (eigCount A (a + v) : ℝ))
    (u := γ - a) (μ := lam - a) hNr hs hy hc1 hβ hβi hi'1
    (by linarith [hmem.1]) (by linarith) hYt (by simp)
    (by simp only [add_sub_cancel]; rw [hnγ, hna, hdkr, hjr, hi'r]; ring)
    (rm_lo_dn hda.nonneg hN0 (by linarith) hc1.le fun x h1 h2 => (hρ x h1 h2).1)
    (rm_hi_dn hda.nonneg hN0 (by linarith) hc2.le fun x h1 h2 => (hρ x h1 h2).2)
    (fun v h0 hv => by
      have := hcount (a + v) ⟨by linarith, by linarith⟩
      rw [show nClass N σ a - (eigCount A (a + v) : ℝ) - (nClass N σ a - nClass N σ (a + v)) =
        -((eigCount A (a + v) : ℝ) - nClass N σ (a + v)) by ring, abs_neg]
      exact this)
    (fun v hv => by
      rw [hna, hdkr, hi'r] at hv
      have h3 : eigCount A (a + v) < j := by
        have : (eigCount A (a + v) : ℝ) < j := by rw [hjr]; linarith
        exact_mod_cast this
      have h4 : lam < a + v := by
        by_contra hc
        have := (sortedEig_ge_iff hA hj1 hjN (a + v)).1 (not_lt.1 hc)
        omega
      linarith)
    (fun v hv => by
      have h3 : ¬ j ≤ eigCount A (a + v) := fun h =>
        absurd ((sortedEig_ge_iff hA hj1 hjN (a + v)).2 h) (by linarith)
      have h4 : eigCount A (a + v) + 1 ≤ j := by omega
      have h5 : (eigCount A (a + v) : ℝ) + 1 ≤ j := by exact_mod_cast h4
      rw [hna, hdkr, hi'r]
      rw [hjr] at h5
      linarith)
    (by linarith) hA2 hA3 hA4 hA5
  rw [show lam - a - (γ - a) = lam - γ by ring] at key
  rw [mul_assoc]
  exact key

/-- Rigidity in the bulk: if `n(γ) = j − 1/2`, `ρ ≥ c₀` on `[γ − r, γ + r] ⊆ (0, ∞)`,
`N c₀ r ≥ s + 1` and the count is within `s` at `γ ± r`, then `|λ_j − γ| ≤ r`. -/
private lemma rm_bulk_core {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    {γ r c₀ s : ℝ} (hn : nClass N σ γ = (j : ℝ) - 1 / 2) (hr : 0 < r) (hγr : 0 < γ - r)
    (hc₀ : 0 ≤ c₀) (hρ : ∀ x ∈ Set.Icc (γ - r) (γ + r), c₀ ≤ rhoDens N σ x)
    (hNr : s + 1 ≤ N * c₀ * r)
    (hcl : |(eigCount A (γ - r) : ℝ) - nClass N σ (γ - r)| ≤ s)
    (hcr : |(eigCount A (γ + r) : ℝ) - nClass N σ (γ + r)| ≤ s) :
    |sortedEig A j - γ| ≤ r := by
  have hdl := rm_nClass_sub_ge hσ hN (x := γ - r) (y := γ) hγr (by linarith) hc₀
    (fun u hu => hρ u ⟨hu.1, by linarith [hu.2]⟩)
  have hdr := rm_nClass_sub_ge hσ hN (x := γ) (y := γ + r) (by linarith) (by linarith) hc₀
    (fun u hu => hρ u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  rw [show γ - (γ - r) = r by ring] at hdl
  rw [show γ + r - γ = r by ring] at hdr
  rw [abs_le] at hcl hcr
  have hlow : (j : ℝ) < eigCount A (γ - r) := by linarith [hcl.1]
  have hlowN : j < eigCount A (γ - r) := by exact_mod_cast hlow
  have hup : (eigCount A (γ + r) : ℝ) < j := by linarith [hcr.2]
  have hupN : eigCount A (γ + r) < j := by exact_mod_cast hup
  have h1 : γ - r ≤ sortedEig A j := (sortedEig_ge_iff hA hj1 hjN (γ - r)).2 hlowN.le
  have h2 : sortedEig A j < γ + r := by
    by_contra h
    have := (sortedEig_ge_iff hA hj1 hjN (γ + r)).1 (not_lt.mp h)
    omega
  rw [abs_le]
  constructor <;> linarith

/-- `N^ε i₀^{−1/3} N^{−2/3} ≤ N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}` when
`1 ≤ i ∧ (N_k + 1 − i) ≤ i₀`. -/
private lemma rm_rig_le {Nk i i₀ : ℕ} {ε : ℝ} (h1 : 1 ≤ min i (Nk + 1 - i))
    (h2 : min i (Nk + 1 - i) ≤ i₀) :
    (N : ℝ) ^ ε * (i₀ : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hm : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have := Real.rpow_le_rpow_of_nonpos hm
    (by exact_mod_cast h2 : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ (i₀ : ℝ))
    (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) h3

/-- `N^ε N⁻¹ ≤ N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}` when `1 ≤ i ∧ (N_k + 1 − i) ≤ N`. -/
private lemma rm_rig_bulk {Nk i : ℕ} {ε : ℝ} (h1 : 1 ≤ min i (Nk + 1 - i))
    (h2 : min i (Nk + 1 - i) ≤ N) :
    (N : ℝ) ^ ε * (N : ℝ)⁻¹ ≤ rigBound N Nk i ε := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine le_trans (le_of_eq ?_) (rm_rig_le (N := N) h1 h2)
  rw [mul_assoc, ← Real.rpow_add hN, show -(1 / 3 : ℝ) + -(2 / 3) = -1 by norm_num,
    Real.rpow_neg_one]

/-! ## Exponents and events -/

/-- `C N^a ≤ N^b` for `a < b` and `N` large. -/
private lemma rm_ev (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((h1.eventually_ge_atTop C).and (Filter.eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h2, h3⟩ := hN₀ N hN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN]; ring_nf

private lemma rm_rpow_pow {x : ℝ} (hx : 0 < x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]

/-- The exponent rows of the edge inversion at `s = N^{ε₁}`, `y = N^{−1/3+ε₁/2}`, `E = N^ε`,
for `N` large. -/
private lemma rm_num {c₁ c₂ t ε ε₁ : ℝ} (hc₁ : 0 < c₁) (ht : 0 < t) (hε₁ : 0 < ε₁)
    (hε₁ε : 2 * ε₁ ≤ ε) (hε₁2 : ε₁ < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ (N : ℝ) ^ ε₁ ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 = (N : ℝ) ^ (-2 / 3 + ε₁) ∧
      ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 ≤ t ∧
      (rmK c₁ c₂ + 1) * (N : ℝ) ^ ε₁ + 1 ≤
        N * c₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 / 4 ∧
      128 * rmK c₁ c₂ ^ 3 * ((N : ℝ) ^ ε₁) ^ 3 ≤ c₁ ^ 2 * ((N : ℝ) ^ ε) ^ 3 ∧
      8 * rmK c₁ c₂ * (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2 ≤
        ((N : ℝ) ^ ε) ^ 3 ∧
      rmL c₁ c₂ * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε := by
  have hK0 : 0 ≤ rmK c₁ c₂ := by
    unfold rmK rmL; have : 1 ≤ rmM c₂ := le_max_left _ _
    have : 0 < rmM c₂ := by linarith
    positivity
  obtain ⟨N₁, e1⟩ := rm_ev (1 / t) (a := -2 / 3 + ε₁) (b := 0) (by linarith)
  obtain ⟨N₂, e2⟩ := rm_ev (4 * (rmK c₁ c₂ + 2) / c₁) (a := ε₁) (b := 3 * ε₁ / 2) (by linarith)
  obtain ⟨N₃, e3⟩ := rm_ev (128 * rmK c₁ c₂ ^ 3 / c₁ ^ 2) (a := 3 * ε₁) (b := 3 * ε)
    (by linarith)
  obtain ⟨N₄, e4⟩ := rm_ev (8 * rmK c₁ c₂) (a := 4 * ε₁) (b := 3 * ε) (by linarith)
  obtain ⟨N₅, e5⟩ := rm_ev (rmL c₁ c₂) (a := ε₁) (b := ε) (by linarith)
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hN))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have f1 := e1 N (le_of_max_le_left (le_of_max_le_left hN))
  have f2 := e2 N (le_of_max_le_right (le_of_max_le_left hN))
  have f3 := e3 N (le_of_max_le_left (le_of_max_le_left (le_of_max_le_right hN)))
  have f4 := e4 N (le_of_max_le_right (le_of_max_le_left (le_of_max_le_right hN)))
  have f5 := e5 N (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hN)))
  have hs1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1r hε₁.le
  have hy2 : ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 2 = (N : ℝ) ^ (-2 / 3 + ε₁) := by
    rw [rm_rpow_pow hNr]; congr 1; push_cast; ring
  have hy3 : (N : ℝ) * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 = (N : ℝ) ^ (3 * ε₁ / 2) := by
    rw [rm_rpow_pow hNr]
    conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNr]; congr 1; push_cast; ring
  have hy6 : (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2 =
      (N : ℝ) ^ (4 * ε₁) := by
    rw [rm_rpow_pow hNr, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hNr,
      ← Real.rpow_add hNr]
    congr 1; push_cast; ring
  have hs3 : ((N : ℝ) ^ ε₁) ^ 3 = (N : ℝ) ^ (3 * ε₁) := by
    rw [rm_rpow_pow hNr]; congr 1; push_cast; ring
  have hE3 : ((N : ℝ) ^ ε) ^ 3 = (N : ℝ) ^ (3 * ε) := by
    rw [rm_rpow_pow hNr]; congr 1; push_cast; ring
  refine ⟨hs1, hy2, ?_, ?_, ?_, ?_, f5⟩
  · rw [hy2]
    rw [Real.rpow_zero] at f1
    have := mul_le_mul_of_nonneg_left f1 ht.le
    rw [← mul_assoc, mul_one_div_cancel ht.ne', one_mul, mul_one] at this
    exact this
  · have h5 : N * c₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 3 / 4 =
        c₁ / 4 * (N : ℝ) ^ (3 * ε₁ / 2) := by rw [← hy3]; ring
    rw [h5]
    have h6 : c₁ / 4 * (4 * (rmK c₁ c₂ + 2) / c₁ * (N : ℝ) ^ ε₁) =
        (rmK c₁ c₂ + 2) * (N : ℝ) ^ ε₁ := by field_simp
    have h7 := mul_le_mul_of_nonneg_left f2 (by positivity : (0 : ℝ) ≤ c₁ / 4)
    rw [h6] at h7
    nlinarith
  · rw [hs3, hE3]
    have h7 := mul_le_mul_of_nonneg_left f3 (by positivity : (0 : ℝ) ≤ c₁ ^ 2)
    have h6 : c₁ ^ 2 * (128 * rmK c₁ c₂ ^ 3 / c₁ ^ 2 * (N : ℝ) ^ (3 * ε₁)) =
        128 * rmK c₁ c₂ ^ 3 * (N : ℝ) ^ (3 * ε₁) := by field_simp
    rw [h6] at h7
    exact h7
  · have e : 8 * rmK c₁ c₂ * (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 *
        (N : ℝ) ^ 2 = 8 * rmK c₁ c₂ * ((N : ℝ) ^ ε₁ *
          ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) ^ 6 * (N : ℝ) ^ 2) := by ring
    rw [e, hy6, hE3]
    exact f4

/-- The exponent rows of the bulk inversion: `2 N^{ε₁} ≤ c₀ N^ε` and
`(N^{ε₁} + 1)/(c₀ N) ≤ w`, for `N` large. -/
private lemma rm_num_bulk {c₀ w ε ε₁ : ℝ} (hc₀ : 0 < c₀) (hw : 0 < w) (hε₁ : 0 < ε₁)
    (hε₁ε : ε₁ < ε) (hε₁1 : ε₁ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((N : ℝ) ^ ε₁ + 1) / (c₀ * N) ≤ w ∧
      ((N : ℝ) ^ ε₁ + 1) / (c₀ * N) ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
  obtain ⟨N₁, e1⟩ := rm_ev (2 / c₀) (a := ε₁) (b := ε) hε₁ε
  obtain ⟨N₂, e2⟩ := rm_ev (2 / (c₀ * w)) (a := ε₁) (b := 1) hε₁1
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have f1 := e1 N (le_of_max_le_left (le_of_max_le_left hN))
  have f2 := e2 N (le_of_max_le_right (le_of_max_le_left hN))
  rw [Real.rpow_one] at f2
  have hs1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1r hε₁.le
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have h6 : c₀ * w / 2 * (2 / (c₀ * w) * (N : ℝ) ^ ε₁) = (N : ℝ) ^ ε₁ := by field_simp
    have h7 := mul_le_mul_of_nonneg_left f2 (by positivity : (0 : ℝ) ≤ c₀ * w / 2)
    rw [h6] at h7
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have h6 : c₀ / 2 * (2 / c₀ * (N : ℝ) ^ ε₁) = (N : ℝ) ^ ε₁ := by field_simp
    have h7 := mul_le_mul_of_nonneg_left f1 (by positivity : (0 : ℝ) ≤ c₀ / 2)
    rw [h6] at h7
    have e : (N : ℝ) ^ ε * (N : ℝ)⁻¹ * (c₀ * N) = c₀ * (N : ℝ) ^ ε := by
      field_simp
    rw [e]
    nlinarith

private lemma rm_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : HighProbAt N D A) (hAB : A ⊆ B) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 hAB)).trans h

private lemma rm_hp_univ {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} :
    HighProbAt N D (Set.univ : Set Ω) := by
  unfold HighProbAt
  simp

/-- Two events of probability `≥ 1 − N^{−D−1}` intersect in an event of probability
`≥ 1 − N^{−D}`, for `N ≥ 2`. -/
private lemma rm_hp_inter {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (hN : 2 ≤ N) (hA : HighProbAt N (D + 1) A) (hB : HighProbAt N (D + 1) B) :
    HighProbAt N D (A ∩ B) := by
  unfold HighProbAt at *
  rw [Set.compl_inter]
  refine (measure_union_le _ _).trans ((add_le_add hA hB).trans ?_)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hpos, Real.rpow_neg_one]
  rw [e]
  have h0 : 0 ≤ (N : ℝ) ^ (-D) := by positivity
  have h1 : (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN'
  nlinarith

/-- The eigenvalues `σ` of `Σ` are positive under Assumption 2.1. -/
private lemma rm_sigma_pos {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) : ∀ i, 0 < specOf Sig i := fun i => by
  rw [specOf_eq hm.sigma.posDef.isHermitian]
  exact hm.sigma.posDef.eigenvalues_pos i

/-- Theorem 3.15 (iii) (`thm:bulk`) at fixed `N`, under (T_diag): in a regular bulk component
with one regular edge, `|λ_{k,i} − γ_{k,i}| ≤ N^ε N⁻¹` on `[a_{2k} + τ', a_{2k−1} − τ']`. -/
theorem rigidity_bulk (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularBulk c N (specOf Sig) k →
      (RegularEdge τ N (specOf Sig) (2 * k) ∨ RegularEdge τ N (specOf Sig) (2 * k - 1)) →
      HighProbAt N D {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k →
        gammaBand N (specOf Sig) k i ∈
          Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ') (edgeVal N (specOf Sig) (2 * k - 1) - τ') →
        |lamBand Sig (X ω) k i - gammaBand N (specOf Sig) k i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹} := by
  by_cases hc0 : 0 < c (τ' / 2)
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k _ hb _ => absurd ((hb.2.2 (τ' / 2) (by linarith)).1) hc0⟩
  set ε₁ := min ε 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by have := lt_min hε one_pos; rw [hε₁]; linarith
  have hε₁ε : ε₁ < ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  have hε₁1 : ε₁ < 1 := by have := min_le_right ε 1; rw [hε₁]; linarith
  obtain ⟨N₁, h₁⟩ := count_bulk τ (τ' / 2) c C ε₁ D hτ (by linarith) hε₁0
  obtain ⟨N₂, h₂⟩ := rm_num_bulk hc0 (by linarith : 0 < τ' / 2) hε₁0 hε₁ε hε₁1
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M Sig X k hm hb hedge => ?_⟩
  obtain ⟨hr1, hr2⟩ := h₂ N (le_of_max_le_right hN)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := rm_sigma_pos hm
  obtain ⟨hN0, -, -⟩ := rm_facts hda
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨hk1, hkp, hbk⟩ := hb
  refine rm_hp_mono (h₁ N (le_of_max_le_left hN) M Sig X k hm ⟨hk1, hkp, hbk⟩ hedge)
    fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro i hi hiN hγ
  set σ := specOf Sig with hσdef
  set r := ((N : ℝ) ^ ε₁ + 1) / (c (τ' / 2) * N) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk1 hkp
  have hdk := (rm_cum hda hσ hk1 hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjMN : cumCount N σ (k - 1) + i ≤ min M N := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := hjMN.trans (min_le_right _ _)
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda hσ hj1 hjMN
  have ha0 := rm_edge_nonneg hda (k := 2 * k) (by omega) (by omega)
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  have hlam : lamBand Sig (X ω) k i = sortedEig (QN Sig (X ω)) (cumCount N σ (k - 1) + i) :=
    rfl
  rw [hlam]
  rw [hγdef] at hγ ⊢
  have hwin : ∀ x, gammaLoc N σ (cumCount N σ (k - 1) + i) - r ≤ x →
      x ≤ gammaLoc N σ (cumCount N σ (k - 1) + i) + r →
      x ∈ Set.Icc (edgeVal N σ (2 * k) + τ' / 2) (edgeVal N σ (2 * k - 1) - τ' / 2) :=
    fun x h1 h2 => ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hcore := rm_bulk_core hda.nonneg hN0 (rm_herm hm.sigma.posDef (X ω)) hj1 hjN hnγ hr0
    (by linarith [hγ.1]) hc0.le (fun x hx => (hbk (τ' / 2) (by linarith)).2 x
      (hwin x hx.1 hx.2))
    (le_of_eq (by rw [hr]; field_simp))
    (hω _ (hwin _ le_rfl (by linarith))) (hω _ (hwin _ (by linarith) le_rfl))
  exact hcore.trans hr2

/-! ## Theorem 3.14 (iii) -/

/-- `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma rm_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  rw [heq]
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  nlinarith

/-- `a_{2k−2} ≥ a_{2k−1} + τ` when the edge `2k − 1` is regular at `τ`, `k ≥ 2`. -/
private lemma rm_sep_up {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 2 ≤ k) (hreg : RegularEdge τ N σ (2 * k - 1)) :
    edgeVal N σ (2 * k - 1) + τ ≤ edgeVal N σ (2 * k - 2) := by
  have hkp := hreg.2.1
  have h1 := hreg.2.2.2.1 (2 * k - 2) (by omega) (by omega) (by omega)
  have h2 := rm_anti hda (i := 2 * k - 2) (j := 2 * k - 1) (by omega) (by omega) hkp
  rw [abs_of_nonpos (by linarith)] at h1
  linarith

/-- `a_{2k+1} + τ ≤ a_{2k}` when the edge `2k` is regular at `τ`, `k < p`. -/
private lemma rm_sep_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) (hreg : RegularEdge τ N σ (2 * k)) :
    edgeVal N σ (2 * k + 1) + τ ≤ edgeVal N σ (2 * k) := by
  have h1 := hreg.2.2.2.1 (2 * k + 1) (by omega) (by omega) (by omega)
  have h2 := rm_anti hda (i := 2 * k) (j := 2 * k + 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonneg (by linarith)] at h1
  linarith

/-- `gapMid_{k−1} = (a_{2k−2} + a_{2k−1})/2` for `k ≥ 1`. -/
private lemma rm_gapMid_pred {σ : Fin M → ℝ} {k : ℕ} (hk : 1 ≤ k) :
    gapMid N σ (k - 1) = (edgeVal N σ (2 * k - 2) + edgeVal N σ (2 * k - 1)) / 2 := by
  unfold gapMid
  rw [show 2 * (k - 1) = 2 * k - 2 by omega, show 2 * k - 2 + 1 = 2 * k - 1 by omega]

/-- Above a regular edge `a_{2k−1}` (regular at `τ`): no eigenvalue in
`[a_{2k−1} + y², gapMid_{k−1})` (in `[a_1 + y², ∞)` for `k = 1`), given the gap lemma on
`[a_{2k−1} ± τ/2]` at scale `y²` and at distance `τ/4` above `τ/2`. -/
private lemma rm_noeig_up {τ y2 : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    {K : ℕ} {lam : Fin K → ℝ} {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (hreg : RegularEdge τ N σ (2 * k - 1)) (hy0 : 0 < y2) (hy : y2 ≤ τ / 2)
    (hgap : ∀ l, lam l ∈ Set.Icc (edgeVal N σ (2 * k - 1) - τ / 2)
      (edgeVal N σ (2 * k - 1) + τ / 2) → Metric.infDist (lam l) (varrho N σ).support < y2)
    (hout : ∀ l, τ / 2 ≤ lam l → Metric.infDist (lam l) (varrho N σ).support < τ / 4) :
    ∀ l, edgeVal N σ (2 * k - 1) + y2 ≤ lam l → (2 ≤ k → lam l < gapMid N σ (k - 1)) →
      False := by
  intro l h1 h2
  have hτ := hda.pos
  have haτ : τ ≤ edgeVal N σ (2 * k - 1) := hreg.2.2.1
  have ha1 : 0 < edgeVal N σ 1 :=
    lt_of_lt_of_le (by linarith) (rm_anti hda (i := 1) (j := 2 * k - 1) le_rfl (by omega)
      (by omega))
  have hsep : 2 ≤ k → edgeVal N σ (2 * k - 1) + τ ≤ edgeVal N σ (2 * k - 2) :=
    fun h => rm_sep_up hda h hreg
  rcases le_or_gt (lam l) (edgeVal N σ (2 * k - 1) + τ / 2) with hx | hx
  · have hd := hgap l ⟨by linarith, hx⟩
    have := rm_dist hda (x := lam l) (r := y2) hy0.le (by linarith) ha1
      (rm_bands_above hda hk hkp h1 fun h => by linarith [hsep h])
    linarith
  · have hd := hout l (by linarith)
    have := rm_dist hda (x := lam l) (r := τ / 2) (by linarith) (by linarith) ha1
      (rm_bands_above hda hk hkp (by linarith) fun h => by
        have := h2 h
        rw [rm_gapMid_pred hk] at this
        linarith [hsep h])
    linarith

/-- Below a regular edge `a_{2k}` (regular at `τ`): no eigenvalue in `[P, a_{2k} − y²)`, for a
point `P ≥ a_{2k}/2` with `P ≥ a_{2k+1} + τ/2` when `k < p`. -/
private lemma rm_noeig_dn {τ y2 P : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    {K : ℕ} {lam : Fin K → ℝ} {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (hreg : RegularEdge τ N σ (2 * k)) (hy0 : 0 < y2) (hy : y2 ≤ τ / 2)
    (hP1 : edgeVal N σ (2 * k) / 2 ≤ P)
    (hP2 : k < numBands N σ → edgeVal N σ (2 * k + 1) + τ / 2 ≤ P)
    (hgap : ∀ l, lam l ∈ Set.Icc (edgeVal N σ (2 * k) - τ / 2)
      (edgeVal N σ (2 * k) + τ / 2) → Metric.infDist (lam l) (varrho N σ).support < y2)
    (hout : ∀ l, τ / 2 ≤ lam l → Metric.infDist (lam l) (varrho N σ).support < τ / 4) :
    ∀ l, P ≤ lam l → lam l < edgeVal N σ (2 * k) - y2 → False := by
  intro l h1 h2
  have hτ := hda.pos
  have haτ : τ ≤ edgeVal N σ (2 * k) := hreg.2.2.1
  have ha1 : 0 < edgeVal N σ 1 :=
    lt_of_lt_of_le (by linarith) (rm_anti hda (i := 1) (j := 2 * k) (by omega) (by omega)
      (by omega))
  have hsep : k < numBands N σ → edgeVal N σ (2 * k + 1) + τ ≤ edgeVal N σ (2 * k) :=
    fun h => rm_sep_dn hda hk h hreg
  rcases le_or_gt (edgeVal N σ (2 * k) - τ / 2) (lam l) with hx | hx
  · have hd := hgap l ⟨hx, by linarith⟩
    have := rm_dist hda (x := lam l) (r := y2) hy0.le (by linarith) ha1
      (rm_bands_below hda hk hkp (by linarith) fun h => by linarith [hsep h])
    linarith
  · have hd := hout l (by linarith)
    have := rm_dist hda (x := lam l) (r := τ / 2) (by linarith) (by linarith) ha1
      (rm_bands_below hda hk hkp (by linarith) fun h => by linarith [hP2 h])
    linarith

/-- Theorem 3.14 (iii) at the upper edge `a_{2k−1}` of the band `k`, on one sample: the count
on `[a_{2k−1} ± τ'(τ)]`, the gap lemmas and the exact count at `gapMid_{k−1}` give (rigidity)
on `[a_{2k−1} ± τ'(τ)/2]`. -/
private lemma rm_edge_odd_det {τ ε s y : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (hτ1 : τ ≤ 1) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hreg : RegularEdge τ N σ (2 * k - 1))
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau' τ)
    (hA2 : (rmK (rmC1 τ) (rmC2 τ) + 1) * s + 1 ≤ N * rmC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rmK (rmC1 τ) (rmC2 τ) ^ 3 * s ^ 3 ≤ rmC1 τ ^ 2 * ((N : ℝ) ^ ε) ^ 3)
    (hA4 : 8 * rmK (rmC1 τ) (rmC2 τ) * s * y ^ 6 * N ^ 2 ≤ ((N : ℝ) ^ ε) ^ 3)
    (hA5 : rmL (rmC1 τ) (rmC2 τ) * s ≤ (N : ℝ) ^ ε)
    (hcount : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k - 1) - edgeTau' τ)
      (edgeVal N σ (2 * k - 1) + edgeTau' τ), |(eigCount A E : ℝ) - nClass N σ E| ≤ s)
    (hgap : ∀ l, specOf A l ∈ Set.Icc (edgeVal N σ (2 * k - 1) - τ / 2)
      (edgeVal N σ (2 * k - 1) + τ / 2) →
        Metric.infDist (specOf A l) (varrho N σ).support < y ^ 2)
    (hout : ∀ l, τ / 2 ≤ specOf A l →
      Metric.infDist (specOf A l) (varrho N σ).support < τ / 4)
    (hexact : 2 ≤ k → eigCount A (gapMid N σ (k - 1)) = cumCount N σ (k - 1)) :
    ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
      gammaBand N σ k i ∈ Set.Icc (edgeVal N σ (2 * k - 1) - edgeTau' τ / 2)
        (edgeVal N σ (2 * k - 1) + edgeTau' τ / 2) →
      |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
        rigBound N (bandNat N σ k) i ε := by
  intro i hi hiN hγ
  have hτ := hda.pos
  have htτ := rm_edgeTau'_le hτ hτ1
  have ht0 : edgeTau' τ ≤ edgeTau0 τ := by
    have := edgeTau'_pos hτ; unfold edgeTau' at *; linarith
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hdk := (rm_cum hda hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := by have := min_le_right M N; omega
  have hy2 : y ^ 2 ≤ τ / 2 := hYt.trans htτ
  have hnone := rm_noeig_up hda hk hkp hreg (by positivity) hy2 hgap hout
  have hexcl : sortedEig A (cumCount N σ (k - 1) + i) ≤ edgeVal N σ (2 * k - 1) + y ^ 2 := by
    rcases lt_or_ge k 2 with hk2 | hk2
    · exact (rm_above1 hA hj1 hjN fun l hl => hnone l hl fun h => absurd h (by omega)).le
    · exact (rm_above2 hA hj1 hjN (P := gapMid N σ (k - 1)) (by rw [hexact hk2]; omega)
        fun l h1 h2 => hnone l h1 fun _ => h2).le
  have hb := rm_edge_upper hda hσ hA hk hkp hreg ht0 htτ hi hiN hγ.1 hcount hexcl hs hy hYt
    hA2 hA3 hA4 hA5
  exact hb.trans (rm_rig_le (le_min hi (by omega)) (min_le_left _ _))

/-- Theorem 3.14 (iii) at the lower edge `a_{2k}` of the band `k`, on one sample: the count on
`[a_{2k} ± τ'(τ)]`, the gap lemmas and an exact count `n_N(P) ≥ d_k` below the edge give
(rigidity) on `[a_{2k} ± τ'(τ)/2]`. -/
private lemma rm_edge_even_det {τ ε s y P : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (hτ1 : τ ≤ 1) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hreg : RegularEdge τ N σ (2 * k))
    (hs : 1 ≤ s) (hy : 0 < y) (hYt : y ^ 2 ≤ edgeTau' τ)
    (hA2 : (rmK (rmC1 τ) (rmC2 τ) + 1) * s + 1 ≤ N * rmC1 τ * y ^ 3 / 4)
    (hA3 : 128 * rmK (rmC1 τ) (rmC2 τ) ^ 3 * s ^ 3 ≤ rmC1 τ ^ 2 * ((N : ℝ) ^ ε) ^ 3)
    (hA4 : 8 * rmK (rmC1 τ) (rmC2 τ) * s * y ^ 6 * N ^ 2 ≤ ((N : ℝ) ^ ε) ^ 3)
    (hA5 : rmL (rmC1 τ) (rmC2 τ) * s ≤ (N : ℝ) ^ ε)
    (hcount : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) - edgeTau' τ)
      (edgeVal N σ (2 * k) + edgeTau' τ), |(eigCount A E : ℝ) - nClass N σ E| ≤ s)
    (hgap : ∀ l, specOf A l ∈ Set.Icc (edgeVal N σ (2 * k) - τ / 2)
      (edgeVal N σ (2 * k) + τ / 2) →
        Metric.infDist (specOf A l) (varrho N σ).support < y ^ 2)
    (hout : ∀ l, τ / 2 ≤ specOf A l →
      Metric.infDist (specOf A l) (varrho N σ).support < τ / 4)
    (hP1 : edgeVal N σ (2 * k) / 2 ≤ P)
    (hP2 : k < numBands N σ → edgeVal N σ (2 * k + 1) + τ / 2 ≤ P)
    (hexact : cumCount N σ k ≤ eigCount A P) :
    ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
      gammaBand N σ k i ∈ Set.Icc (edgeVal N σ (2 * k) - edgeTau' τ / 2)
        (edgeVal N σ (2 * k) + edgeTau' τ / 2) →
      |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
        rigBound N (bandNat N σ k) i ε := by
  intro i hi hiN hγ
  have hτ := hda.pos
  have htτ := rm_edgeTau'_le hτ hτ1
  have ht0 : edgeTau' τ ≤ edgeTau0 τ := by
    have := edgeTau'_pos hτ; unfold edgeTau' at *; linarith
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hdk := (rm_cum hda hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := by have := min_le_right M N; omega
  have hy2 : y ^ 2 ≤ τ / 2 := hYt.trans htτ
  have hnone := rm_noeig_dn hda hk hkp hreg (by positivity) hy2 hP1 hP2 hgap hout
  have hexcl : edgeVal N σ (2 * k) - y ^ 2 ≤ sortedEig A (cumCount N σ (k - 1) + i) :=
    rm_below hA hj1 hjN (P := P) (by omega) hnone
  have hb := rm_edge_lower hda hσ hA hk hkp hreg ht0 hi hiN hγ.2 hcount hexcl hs hy hYt
    hA2 hA3 hA4 hA5
  exact hb.trans (rm_rig_le (le_min hi (by omega)) (min_le_right _ _))

/-- Theorem 3.14 (iii) (`thm:edge`) at fixed `N`, under (T_diag): rigidity near a regular edge
`k`, with `τ' = edgeTau' τ / 2` and `k̂ = ⌊(k+1)/2⌋`. -/
theorem rigidity_edge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      HighProbAt N D {ω | ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) ((k + 1) / 2) →
        gammaBand N (specOf Sig) ((k + 1) / 2) i ∈
          Set.Icc (edgeVal N (specOf Sig) k - edgeTau' τ / 2)
            (edgeVal N (specOf Sig) k + edgeTau' τ / 2) →
        |lamBand Sig (X ω) ((k + 1) / 2) i - gammaBand N (specOf Sig) ((k + 1) / 2) i| ≤
          rigBound N (bandNat N (specOf Sig) ((k + 1) / 2)) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k hm _ => absurd hm.tau_le_one hτ1⟩
  set ε₁ := min ε 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by have := lt_min hε one_pos; rw [hε₁]; linarith
  have hε₁ε : 2 * ε₁ ≤ ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  have hε₁2 : ε₁ < 2 / 3 := by have := min_le_right ε 1; rw [hε₁]; linarith
  obtain ⟨N₁, h₁⟩ := count_edge τ C ε₁ (D + 1 + 1) hτ hε₁0
  obtain ⟨N₂, h₂⟩ := gap_window τ C ε₁ (D + 1 + 1) (τ / 2) hτ hε₁0 hε₁2 (by linarith)
  obtain ⟨N₃, h₃⟩ := gap_outside τ C (τ / 4) (τ / 2) (D + 1 + 1) hτ (by linarith) (by linarith)
  obtain ⟨N₄, h₄⟩ := prop_counting τ C τ (D + 1 + 1) hτ hτ
  obtain ⟨N₅, h₅⟩ := bottom_count τ C τ (D + 1 + 1) hτ hτ
  obtain ⟨N₆, h₆⟩ := rm_num (c₁ := rmC1 τ) (c₂ := rmC2 τ) (rm_C1_pos hτ) (edgeTau'_pos hτ)
    hε₁0 hε₁ε hε₁2
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ (max N₆ 2)),
    fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hNa : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hNb : max N₅ (max N₆ 2) ≤ N := le_of_max_le_right hN
  have hN2 : 2 ≤ N := le_of_max_le_right (le_of_max_le_right hNb)
  obtain ⟨hs1, hyeq, hYt, hA2, hA3, hA4, hA5⟩ :=
    h₆ N (le_of_max_le_left (le_of_max_le_right hNb))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2) := by positivity
  set σ := specOf Sig with hσdef
  have hda : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := rm_sigma_pos hm
  have hk1 : 1 ≤ k := hk.1
  have hk2 : k ≤ 2 * numBands N σ := hk.2.1
  have hak : τ ≤ edgeVal N σ k := hk.2.2.1
  have hEc := h₁ N (le_of_max_le_left (le_of_max_le_left hNa)) M Sig X k
    hm hk
  have hEg := h₂ N (le_of_max_le_right (le_of_max_le_left hNa)) M Sig X
    (Set.Icc (edgeVal N σ k - τ / 2) (edgeVal N σ k + τ / 2)) hm
    (fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1])
    (fun l hl1 hl2 hl => by
      rcases eq_or_ne l k with rfl | hlk
      · exact regularEdge_mono hk (by linarith)
      · exfalso
        have hne : (Set.Icc (edgeVal N σ k - τ / 2) (edgeVal N σ k + τ / 2)).Nonempty :=
          ⟨edgeVal N σ k, by constructor <;> linarith⟩
        obtain ⟨z, hz, hdz⟩ := (Metric.infDist_lt_iff hne).1
          (lt_of_le_of_lt hl (by linarith : τ / 4 < τ / 2))
        have hsep := hk.2.2.2.1 l hl1 hl2 hlk
        rw [Real.dist_eq] at hdz
        have h1 := abs_sub_le (edgeVal N σ k) z (edgeVal N σ l)
        rw [abs_sub_comm (edgeVal N σ k) z] at h1
        have h2 : |z - edgeVal N σ k| ≤ τ / 2 := abs_le.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
        rw [abs_sub_comm z (edgeVal N σ l)] at h1
        linarith)
  have hEo := h₃ N (le_of_max_le_left (le_of_max_le_right hNa)) M Sig X hm
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · -- the lower edge `a_{2m}` of the band `m`
    have hm1 : 1 ≤ m := by omega
    have hmp : m ≤ numBands N σ := by omega
    rw [show (2 * m + 1) / 2 = m by omega]
    obtain ⟨P, Ex, hEx, hP1, hP2, hPx⟩ : ∃ P : ℝ, ∃ Ex : Set Ω, HighProbAt N (D + 1 + 1) Ex ∧
        edgeVal N σ (2 * m) / 2 ≤ P ∧
        (m < numBands N σ → edgeVal N σ (2 * m + 1) + τ / 2 ≤ P) ∧
        ∀ ω ∈ Ex, cumCount N σ m ≤ eigCount (QN Sig (X ω)) P := by
      rcases lt_or_eq_of_le hmp with hlt | heq
      · have hsep := rm_sep_dn hda hm1 hlt hk
        have hb0 := rm_edge_nonneg hda (k := 2 * m + 1) (by omega) (by omega)
        refine ⟨gapMid N σ m, _, h₄ N (le_of_max_le_right (le_of_max_le_right hNa)) M Sig X m
          hm hm1 hlt hak (by linarith), ?_, fun _ => ?_, fun ω hω => le_of_eq hω.symm⟩
        · unfold gapMid; linarith
        · unfold gapMid; linarith
      · subst heq
        refine ⟨edgeVal N σ (2 * numBands N σ) / 2, _, h₅ N (le_of_max_le_left hNb) M Sig X hm hak,
          le_rfl, fun h => absurd h (lt_irrefl _), fun ω hω => ?_⟩
        rw [(rm_cum hda hσ hm1 le_rfl).2]
        exact le_of_eq hω.symm
    refine rm_hp_mono (rm_hp_inter hN2 (rm_hp_inter hN2 hEc hEg) (rm_hp_inter hN2 hEo hEx)) ?_
    rintro ω ⟨⟨hc, hg⟩, ho, hx⟩
    simp only [Set.mem_ofPred_eq] at hc hg ho ⊢
    exact rm_edge_even_det hda hσ hτ1 (rm_herm hm.sigma.posDef (X ω)) hm1 hmp hk hs1 hy hYt
      hA2 hA3 hA4 hA5 hc (fun l hl => by rw [hyeq]; exact hg l hl) ho hP1 hP2 (hPx ω hx)
  · -- the upper edge `a_{2m+1}` of the band `m + 1`
    have hmp : m + 1 ≤ numBands N σ := by omega
    have e1 : 2 * m + 1 = 2 * (m + 1) - 1 := by omega
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    obtain ⟨Ex, hEx, hPx⟩ : ∃ Ex : Set Ω, HighProbAt N (D + 1 + 1) Ex ∧
        ∀ ω ∈ Ex, 2 ≤ m + 1 → eigCount (QN Sig (X ω)) (gapMid N σ (m + 1 - 1)) =
          cumCount N σ (m + 1 - 1) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exact ⟨Set.univ, rm_hp_univ, fun ω _ h => absurd h (by omega)⟩
      · have hreg : RegularEdge τ N σ (2 * (m + 1) - 1) := by rw [← e1]; exact hk
        have hsep := rm_sep_up hda (k := m + 1) (by omega) hreg
        rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
          show 2 * (m + 1) - 2 = 2 * m by omega] at hsep
        refine ⟨_, h₄ N (le_of_max_le_right (le_of_max_le_right hNa)) M Sig X m hm h0
          (show m < numBands N σ by omega) (by linarith) (by linarith), fun ω hω _ => ?_⟩
        rw [show m + 1 - 1 = m by omega]
        exact hω
    refine rm_hp_mono (rm_hp_inter hN2 (rm_hp_inter hN2 hEc hEg) (rm_hp_inter hN2 hEo hEx)) ?_
    rintro ω ⟨⟨hc, hg⟩, ho, hx⟩
    simp only [Set.mem_ofPred_eq] at hc hg ho ⊢
    rw [e1] at hk hc hg ⊢
    exact rm_edge_odd_det hda hσ hτ1 (rm_herm hm.sigma.posDef (X ω)) (by omega) hmp hk hs1 hy
      hYt hA2 hA3 hA4 hA5 hc (fun l hl => by rw [hyeq]; exact hg l hl) ho (hPx ω hx)

/-! ## Theorem 3.12 -/

/-- Above the upper edge `a_{2k−1} ≥ τ`: no eigenvalue in
`[a_{2k−1} + y², gapMid_{k−1})` (in `[a_1 + y², ∞)` for `k = 1`), given the gap lemma on
`edgeWin τ` at scale `y²`. -/
private lemma rm_noeig_up_win {τ y2 : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions (τ / 2) N σ)
    {K : ℕ} {lam : Fin K → ℝ} {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (haτ : τ ≤ edgeVal N σ (2 * k - 1))
    (hy0 : 0 < y2) (hy : y2 ≤ τ / 8)
    (hwin : ∀ l, lam l ∈ edgeWin τ N σ → Metric.infDist (lam l) (varrho N σ).support < y2) :
    ∀ l, edgeVal N σ (2 * k - 1) + y2 ≤ lam l → (2 ≤ k → lam l < gapMid N σ (k - 1)) →
      False := by
  intro l h1 h2
  have hτ : 0 < τ := by have := hda.pos; linarith
  have ha1 : 0 < edgeVal N σ 1 :=
    lt_of_lt_of_le (by linarith) (rm_anti hda (i := 1) (j := 2 * k - 1) le_rfl (by omega)
      (by omega))
  have hd := hwin l (Or.inl (show 3 * τ / 4 ≤ lam l by linarith))
  have := rm_dist hda (x := lam l) (r := y2) hy0.le (by linarith) ha1
    (rm_bands_above hda hk hkp h1 fun h => by
      have h3 := h2 h
      rw [rm_gapMid_pred hk] at h3
      linarith)
  linarith

/-- Below the lower edge `a_{2k} ≥ τ/2` (regular at `τ/2`): no eigenvalue in `[P, a_{2k} − y²)`
for `P ≥ a_{2k}/2` with `P ≥ a_{2k+1} + τ/4` when `k < p`, given the gap lemma on `edgeWin τ`
at scale `y²` and at distance `τ/16` above `τ/4`. -/
private lemma rm_noeig_dn_win {τ y2 P : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions (τ / 2) N σ)
    {K : ℕ} {lam : Fin K → ℝ} {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (hreg : RegularEdge (τ / 2) N σ (2 * k)) (hy0 : 0 < y2) (hy : y2 ≤ τ / 8)
    (hP1 : edgeVal N σ (2 * k) / 2 ≤ P)
    (hP2 : k < numBands N σ → edgeVal N σ (2 * k + 1) + τ / 4 ≤ P)
    (hwin : ∀ l, lam l ∈ edgeWin τ N σ → Metric.infDist (lam l) (varrho N σ).support < y2)
    (hout : ∀ l, τ / 4 ≤ lam l → Metric.infDist (lam l) (varrho N σ).support < τ / 16) :
    ∀ l, P ≤ lam l → lam l < edgeVal N σ (2 * k) - y2 → False := by
  intro l h1 h2
  have hτ : 0 < τ := by have := hda.pos; linarith
  have haτ : τ / 2 ≤ edgeVal N σ (2 * k) := hreg.2.2.1
  have ha1 : 0 < edgeVal N σ 1 :=
    lt_of_lt_of_le (by linarith) (rm_anti hda (i := 1) (j := 2 * k) (by omega) (by omega)
      (by omega))
  rcases le_or_gt (edgeVal N σ (2 * k) - τ / 8) (lam l) with hx | hx
  · have hd := hwin l (Or.inr ⟨2 * k, by omega, by omega, haτ,
      abs_le.2 ⟨by linarith, by linarith⟩⟩)
    have := rm_dist hda (x := lam l) (r := y2) hy0.le (by linarith) ha1
      (rm_bands_below hda hk hkp (by linarith) fun h => by linarith [rm_sep_dn hda hk h hreg])
    linarith
  · have hd := hout l (by linarith)
    have := rm_dist hda (x := lam l) (r := τ / 8) (by linarith) (by linarith) ha1
      (rm_bands_below hda hk hkp (by linarith) fun h => by linarith [hP2 h])
    linarith

/-- The data of Theorem 3.12 on one sample: the count on `edgeWin τ`, the gap lemmas, the exact
counts in the gaps with `a_{2k} ≥ τ/2` and at `a_{2p}/2`, and the exponent rows. -/
private structure RmData (τ ε s y : ℝ) (σ : Fin M → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop where
  hs : 1 ≤ s
  hy : 0 < y
  hYt : y ^ 2 ≤ min (τ / 8) (edgeTau0 (τ / 2))
  hA2 : (rmK (rmC1 (τ / 2)) (rmC2 (τ / 2)) + 1) * s + 1 ≤ N * rmC1 (τ / 2) * y ^ 3 / 4
  hA3 : 128 * rmK (rmC1 (τ / 2)) (rmC2 (τ / 2)) ^ 3 * s ^ 3 ≤
    rmC1 (τ / 2) ^ 2 * ((N : ℝ) ^ ε) ^ 3
  hA4 : 8 * rmK (rmC1 (τ / 2)) (rmC2 (τ / 2)) * s * y ^ 6 * N ^ 2 ≤ ((N : ℝ) ^ ε) ^ 3
  hA5 : rmL (rmC1 (τ / 2)) (rmC2 (τ / 2)) * s ≤ (N : ℝ) ^ ε
  hcount : ∀ E ∈ edgeWin τ N σ, |(eigCount A E : ℝ) - nClass N σ E| ≤ s
  hwin : ∀ l, specOf A l ∈ edgeWin τ N σ →
    Metric.infDist (specOf A l) (varrho N σ).support < y ^ 2
  hout : ∀ l, τ / 4 ≤ specOf A l → Metric.infDist (specOf A l) (varrho N σ).support < τ / 16
  hgaps : ∀ k, 1 ≤ k → k < numBands N σ → τ / 2 ≤ edgeVal N σ (2 * k) →
    τ / 2 ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1) →
      eigCount A (gapMid N σ k) = cumCount N σ k
  hbot : τ / 2 ≤ edgeVal N σ (2 * numBands N σ) →
    eigCount A (edgeVal N σ (2 * numBands N σ) / 2) = min M N

/-- Theorem 3.12 within `t/2` of the upper edge `a_{2k−1}`, `t = min(τ/8, τ₀(τ/2))`. -/
private lemma rm_rig_up {τ ε s y : ℝ} {σ : Fin M → ℝ} (hda2 : DensityAssumptions (τ / 2) N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hd : RmData τ ε s y σ A)
    (hedge : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    {k i : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hi : 1 ≤ i) (hiN : i ≤ bandNat N σ k)
    (hγτ : τ ≤ gammaBand N σ k i)
    (hγ : edgeVal N σ (2 * k - 1) - min (τ / 8) (edgeTau0 (τ / 2)) / 2 ≤ gammaBand N σ k i) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
      rigBound N (bandNat N σ k) i ε := by
  have hτ : 0 < τ := by have := hda2.pos; linarith
  set t := min (τ / 8) (edgeTau0 (τ / 2)) with ht
  have ht1 : t ≤ τ / 8 := min_le_left _ _
  have ht2 : t ≤ edgeTau0 (τ / 2) := min_le_right _ _
  have hmem := gammaBand_mem hda2 hσ hk hkp hi hiN
  have haτ : τ ≤ edgeVal N σ (2 * k - 1) := by linarith [hmem.2]
  have hreg := hedge (2 * k - 1) (by omega) (by omega) (by linarith)
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda2 hk hkp
  have hdk := (rm_cum hda2 hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := by have := min_le_right M N; omega
  have hy2 : y ^ 2 ≤ τ / 8 := hd.hYt.trans ht1
  have hnone := rm_noeig_up_win hda2 hk hkp haτ (by have := hd.hy; positivity) hy2 hd.hwin
  have hexcl : sortedEig A (cumCount N σ (k - 1) + i) ≤ edgeVal N σ (2 * k - 1) + y ^ 2 := by
    rcases lt_or_ge k 2 with hk2 | hk2
    · exact (rm_above1 hA hj1 hjN fun l hl => hnone l hl fun h => absurd h (by omega)).le
    · have hsep := rm_sep_up hda2 hk2 hreg
      have hg := hd.hgaps (k - 1) (by omega) (by omega)
        (by rw [show 2 * (k - 1) = 2 * k - 2 by omega]; linarith)
        (by rw [show 2 * (k - 1) = 2 * k - 2 by omega,
          show 2 * k - 2 + 1 = 2 * k - 1 by omega]; linarith)
      exact (rm_above2 hA hj1 hjN (P := gapMid N σ (k - 1)) (by rw [hg]; omega)
        fun l h1 h2 => hnone l h1 fun _ => h2).le
  have hb := rm_edge_upper hda2 hσ hA hk hkp hreg ht2 (by linarith) hi hiN hγ
    (fun E hE => hd.hcount E (Or.inr ⟨2 * k - 1, by omega, by omega, by linarith,
      abs_le.2 ⟨by linarith [hE.1], by linarith [hE.2]⟩⟩))
    hexcl hd.hs hd.hy hd.hYt hd.hA2 hd.hA3 hd.hA4 hd.hA5
  exact hb.trans (rm_rig_le (le_min hi (by omega)) (min_le_left _ _))

/-- Theorem 3.12 within `t/2` of the lower edge `a_{2k} ≥ τ/2`. -/
private lemma rm_rig_dn {τ ε s y : ℝ} {σ : Fin M → ℝ} (hda2 : DensityAssumptions (τ / 2) N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hd : RmData τ ε s y σ A)
    (hedge : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    {k i : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hi : 1 ≤ i) (hiN : i ≤ bandNat N σ k)
    (haτ : τ / 2 ≤ edgeVal N σ (2 * k))
    (hγ : gammaBand N σ k i ≤ edgeVal N σ (2 * k) + min (τ / 8) (edgeTau0 (τ / 2)) / 2) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
      rigBound N (bandNat N σ k) i ε := by
  have hτ : 0 < τ := by have := hda2.pos; linarith
  set t := min (τ / 8) (edgeTau0 (τ / 2)) with ht
  have ht1 : t ≤ τ / 8 := min_le_left _ _
  have ht2 : t ≤ edgeTau0 (τ / 2) := min_le_right _ _
  have hreg := hedge (2 * k) (by omega) (by omega) haτ
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda2 hk hkp
  have hdk := rm_cum hda2 hσ hk hkp
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := by have := min_le_right M N; have := hdk.1; omega
  have hy2 : y ^ 2 ≤ τ / 8 := hd.hYt.trans ht1
  obtain ⟨P, hP1, hP2, hPx⟩ : ∃ P : ℝ, edgeVal N σ (2 * k) / 2 ≤ P ∧
      (k < numBands N σ → edgeVal N σ (2 * k + 1) + τ / 4 ≤ P) ∧
      cumCount N σ k ≤ eigCount A P := by
    rcases lt_or_eq_of_le hkp with hlt | heq
    · have hsep := rm_sep_dn hda2 hk hlt hreg
      have hb0 := rm_edge_nonneg hda2 (k := 2 * k + 1) (by omega) (by omega)
      refine ⟨gapMid N σ k, by unfold gapMid; linarith, fun _ => by unfold gapMid; linarith,
        le_of_eq (hd.hgaps k hk hlt haτ (by linarith)).symm⟩
    · refine ⟨edgeVal N σ (2 * k) / 2, le_rfl, fun h => absurd h (by omega), ?_⟩
      have hb := hd.hbot (by rw [← heq]; exact haτ)
      rw [← heq] at hb
      rw [hb, ← hdk.2, heq]
  have hnone := rm_noeig_dn_win hda2 hk hkp hreg (by have := hd.hy; positivity) hy2 hP1 hP2
    hd.hwin hd.hout
  have hexcl : edgeVal N σ (2 * k) - y ^ 2 ≤ sortedEig A (cumCount N σ (k - 1) + i) :=
    rm_below hA hj1 hjN (P := P) (by omega) hnone
  have hb := rm_edge_lower hda2 hσ hA hk hkp hreg ht2 hi hiN hγ
    (fun E hE => hd.hcount E (Or.inr ⟨2 * k, by omega, by omega, haτ,
      abs_le.2 ⟨by linarith [hE.1], by linarith [hE.2]⟩⟩))
    hexcl hd.hs hd.hy hd.hYt hd.hA2 hd.hA3 hd.hA4 hd.hA5
  exact hb.trans (rm_rig_le (le_min hi (by omega)) (min_le_right _ _))

/-- Theorem 3.12 at distance `> t/2` from the edges of the band `k`: the bulk inversion with
`c₀ = c(t/4)`. -/
private lemma rm_rig_mid {τ ε s y : ℝ} {c : ℝ → ℝ} {σ : Fin M → ℝ}
    (hda2 : DensityAssumptions (τ / 2) N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hd : RmData τ ε s y σ A) {k i : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ)
    (hbulk : RegularBulk c N σ k) (hi : 1 ≤ i) (hiN : i ≤ bandNat N σ k)
    (hγτ : τ ≤ gammaBand N σ k i)
    (hγ1 : edgeVal N σ (2 * k) + min (τ / 8) (edgeTau0 (τ / 2)) / 2 ≤ gammaBand N σ k i)
    (hγ2 : gammaBand N σ k i ≤ edgeVal N σ (2 * k - 1) - min (τ / 8) (edgeTau0 (τ / 2)) / 2)
    (hr1 : (s + 1) / (c (min (τ / 8) (edgeTau0 (τ / 2)) / 4) * N) ≤
      min (τ / 8) (edgeTau0 (τ / 2)) / 4)
    (hr2 : (s + 1) / (c (min (τ / 8) (edgeTau0 (τ / 2)) / 4) * N) ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
      rigBound N (bandNat N σ k) i ε := by
  have hτ : 0 < τ := by have := hda2.pos; linarith
  obtain ⟨hN0, -, -⟩ := rm_facts hda2
  set t := min (τ / 8) (edgeTau0 (τ / 2)) with ht
  have ht1 : t ≤ τ / 8 := min_le_left _ _
  have ht0 : 0 < t := lt_min (by linarith)
    (by have := edgeTau'_pos (show 0 < τ / 2 by linarith); unfold edgeTau' at this; linarith)
  obtain ⟨-, -, hb⟩ := hbulk
  obtain ⟨hc0, hρ⟩ := hb (t / 4) (by positivity)
  set c₀ := c (t / 4) with hc₀
  set r := (s + 1) / (c₀ * N) with hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hs := hd.hs
  have hr0 : 0 < r := by rw [hr]; have : 0 < s + 1 := by linarith
                         positivity
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda2 hk hkp
  have hdk := (rm_cum hda2 hσ hk hkp).1
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjMN : cumCount N σ (k - 1) + i ≤ min M N := by omega
  have hjN : cumCount N σ (k - 1) + i ≤ N := hjMN.trans (min_le_right _ _)
  obtain ⟨-, hnγ⟩ := nClass_gammaLoc hda2 hσ hj1 hjMN
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  rw [hγdef] at hγ1 hγ2 hγτ ⊢
  have hcore := rm_bulk_core hda2.nonneg hN0 hA hj1 hjN hnγ hr0 (by linarith) hc0.le
    (fun x hx => hρ x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (le_of_eq (by rw [hr]; field_simp))
    (hd.hcount _ (Or.inl (show 3 * τ / 4 ≤ _ by linarith)))
    (hd.hcount _ (Or.inl (show 3 * τ / 4 ≤ _ by linarith)))
  exact (hcore.trans hr2).trans (rm_rig_bulk (le_min hi (by omega))
    ((min_le_left _ _).trans (by omega)))

/-- Theorem 3.12 on one sample, for all `k ≤ p` and `i ≤ N_k` with `γ_{k,i} ≥ τ`. -/
private lemma rm_rig_det {τ ε s y : ℝ} {c : ℝ → ℝ} {σ : Fin M → ℝ}
    (hda2 : DensityAssumptions (τ / 2) N σ)
    (hσ : ∀ j, 0 < σ j) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hd : RmData τ ε s y σ A)
    (hedge : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    (hbulk : ∀ k, 1 ≤ k → k ≤ numBands N σ → RegularBulk c N σ k)
    (hr1 : (s + 1) / (c (min (τ / 8) (edgeTau0 (τ / 2)) / 4) * N) ≤
      min (τ / 8) (edgeTau0 (τ / 2)) / 4)
    (hr2 : (s + 1) / (c (min (τ / 8) (edgeTau0 (τ / 2)) / 4) * N) ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹) :
    ∀ k, 1 ≤ k → k ≤ numBands N σ → ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
      τ ≤ gammaBand N σ k i →
        |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
          rigBound N (bandNat N σ k) i ε := by
  intro k hk hkp i hi hiN hγτ
  have hτ : 0 < τ := by have := hda2.pos; linarith
  set t := min (τ / 8) (edgeTau0 (τ / 2)) with ht
  have ht1 : t ≤ τ / 8 := min_le_left _ _
  rcases le_or_gt (edgeVal N σ (2 * k - 1) - t / 2) (gammaBand N σ k i) with hup | hup
  · exact rm_rig_up hda2 hσ hA hd hedge hk hkp hi hiN hγτ hup
  by_cases hdn : τ / 2 ≤ edgeVal N σ (2 * k) ∧ gammaBand N σ k i ≤ edgeVal N σ (2 * k) + t / 2
  · exact rm_rig_dn hda2 hσ hA hd hedge hk hkp hi hiN hdn.1 hdn.2
  · have hγ1 : edgeVal N σ (2 * k) + t / 2 ≤ gammaBand N σ k i := by
      by_cases ha : τ / 2 ≤ edgeVal N σ (2 * k)
      · exact (lt_of_not_ge fun h => hdn ⟨ha, h⟩).le
      · linarith
    exact rm_rig_mid hda2 hσ hA hd hk hkp (hbulk k hk hkp) hi hiN hγτ hγ1 hup.le hr1 hr2

/-- The gaps `k < p` with `a_{2k} ≥ τ/2` and width `≥ τ/2` number at most
`⌊2τ⁻¹(1 + τ⁻¹)/(τ/2)⌋ + 1`: the edges `a_{2k} ≥ τ/2` are `τ/2`-separated and lie in
`[0, 2τ⁻¹(1 + τ⁻¹)]`. -/
private lemma rm_card_gaps {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hedge : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k) :
    ((Finset.range (numBands N σ + 1)).filter (fun k => 1 ≤ k ∧ k < numBands N σ ∧
      τ / 2 ≤ edgeVal N σ (2 * k) ∧
        τ / 2 ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1))).card ≤
      ⌊2 * τ⁻¹ * (1 + τ⁻¹) / (τ / 2)⌋₊ + 1 := by
  obtain ⟨hN, -, hS⟩ := rm_facts hda
  have hτ := hda.pos
  have hh : 0 < τ / 2 := by linarith
  set f : ℕ → ℕ := fun k => ⌊edgeVal N σ (2 * k) / (τ / 2)⌋₊ with hf
  refine (Finset.card_le_card_of_injOn (t := Finset.range (⌊2 * τ⁻¹ * (1 + τ⁻¹) /
    (τ / 2)⌋₊ + 1)) f ?_ ?_).trans (by simp)
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio, hf]
    have hb := (edgeVal_mem_Icc N σ hda.nonneg hN hS hda.pos hda.phi_lower hda.phi_upper
      hda.bound_Sigma (k := 2 * k) (by omega) (by omega)).2
    have := Nat.floor_le_floor (div_le_div_of_nonneg_right hb hh.le)
    omega
  · intro k₁ hk₁ k₂ hk₂ he
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk₁ hk₂
    simp only [hf] at he
    by_contra hne
    have hsep := (hedge (2 * k₁) (by omega) (by omega) hk₁.2.2.2.1).2.2.2.1 (2 * k₂) (by omega)
      (by omega) (by omega)
    have h0₁ : 0 ≤ edgeVal N σ (2 * k₁) / (τ / 2) :=
      div_nonneg (by linarith [hk₁.2.2.2.1]) hh.le
    have h0₂ : 0 ≤ edgeVal N σ (2 * k₂) / (τ / 2) :=
      div_nonneg (by linarith [hk₂.2.2.2.1]) hh.le
    have a1 := Nat.floor_le h0₁
    have a2 := Nat.lt_floor_add_one (edgeVal N σ (2 * k₁) / (τ / 2))
    have b1 := Nat.floor_le h0₂
    have b2 := Nat.lt_floor_add_one (edgeVal N σ (2 * k₂) / (τ / 2))
    rw [he] at a1 a2
    have hlt : |edgeVal N σ (2 * k₁) / (τ / 2) - edgeVal N σ (2 * k₂) / (τ / 2)| < 1 :=
      abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at hlt
    linarith

/-- Theorem 3.12 (`thm:rigidity`) at fixed `N`, under (T_diag), with every edge with
`a_k ≥ τ/2` regular at `τ/2`: (rigidity) for all `k ≤ p`, `i ≤ N_k` with `γ_{k,i} ≥ τ`, simultaneously. -/
theorem rigidity (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k → τ ≤ gammaBand N (specOf Sig) k i →
          |lamBand Sig (X ω) k i - gammaBand N (specOf Sig) k i| ≤
            rigBound N (bandNat N (specOf Sig) k) i ε} := by
  set t := min (τ / 8) (edgeTau0 (τ / 2)) with ht
  have ht0 : 0 < t := lt_min (by linarith)
    (by have := edgeTau'_pos (show 0 < τ / 2 by linarith); unfold edgeTau' at this; linarith)
  by_cases hc0 : 0 < c (t / 4)
  swap
  · refine ⟨0, fun N _ Ω _ _ M Sig X hm _ hbulk => absurd ?_ hc0⟩
    have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
    obtain ⟨hN, -, hS⟩ := rm_facts hda
    have hp := (card_innerCrit N (specOf Sig) hda.nonneg hN hS).2
    exact ((hbulk 1 le_rfl hp).2.2 (t / 4) (by positivity)).1
  set ε₁ := min ε 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by have := lt_min hε one_pos; rw [hε₁]; linarith
  have hε₁ε : 2 * ε₁ ≤ ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  have hε₁ε' : ε₁ < ε := by linarith
  have hε₁2 : ε₁ < 2 / 3 := by have := min_le_right ε 1; rw [hε₁]; linarith
  have hε₁1 : ε₁ < 1 := by linarith
  obtain ⟨N₁, h₁⟩ := count_edgeWin τ C c ε₁ (D + 1 + 1 + 1) hτ hε₁0
  obtain ⟨N₂, h₂⟩ := gap_edgeWin τ C ε₁ (D + 1 + 1 + 1) hτ hε₁0 hε₁2
  obtain ⟨N₃, h₃⟩ := gap_outside τ C (τ / 16) (τ / 4) (D + 1 + 1 + 1) hτ (by linarith)
    (by linarith)
  obtain ⟨N₄, h₄⟩ := prop_counting τ C (τ / 2) (D + 1 + 1) hτ (by linarith)
  obtain ⟨N₅, h₅⟩ := bottom_count τ C (τ / 2) (D + 1 + 1 + 1) hτ (by linarith)
  obtain ⟨N₆, h₆⟩ := rm_num (c₁ := rmC1 (τ / 2)) (c₂ := rmC2 (τ / 2)) (t := t)
    (rm_C1_pos (by linarith)) ht0 hε₁0 hε₁ε hε₁2
  obtain ⟨N₇, h₇⟩ := rm_num_bulk (w := t / 4) hc0 (by positivity) hε₁0 hε₁ε' hε₁1
  set B := ⌊2 * τ⁻¹ * (1 + τ⁻¹) / (τ / 2)⌋₊ + 1 with hB
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ (max B 2))),
    fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  have hNa : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hNb : max (max N₅ N₆) (max N₇ (max B 2)) ≤ N := le_of_max_le_right hN
  have hN7 : max N₇ (max B 2) ≤ N := le_of_max_le_right hNb
  have hN2 : 2 ≤ N := le_of_max_le_right (le_of_max_le_right hN7)
  have hNB : B ≤ N := le_of_max_le_left (le_of_max_le_right hN7)
  obtain ⟨hs1, hyeq, hYt, hA2, hA3, hA4, hA5⟩ :=
    h₆ N (le_of_max_le_right (le_of_max_le_left hNb))
  obtain ⟨hr1, hr2⟩ := h₇ N (le_of_max_le_left hN7)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2) := by positivity
  set σ := specOf Sig with hσdef
  have hda : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hda2 : DensityAssumptions (τ / 2) N σ :=
    (hm.mono (by linarith) (by linarith)).diagModel_specOf.densityAssumptions (by linarith)
  have hσ := rm_sigma_pos hm
  have hEc := h₁ N (le_of_max_le_left (le_of_max_le_left hNa)) M Sig X hm hedge hbulk
  have hEw := h₂ N (le_of_max_le_right (le_of_max_le_left hNa)) M Sig X hm hedge
  have hEo := h₃ N (le_of_max_le_left (le_of_max_le_right hNa)) M Sig X hm
  obtain ⟨Eb, hEb, hbx⟩ : ∃ Eb : Set Ω, HighProbAt N (D + 1 + 1 + 1) Eb ∧
      ∀ ω ∈ Eb, τ / 2 ≤ edgeVal N σ (2 * numBands N σ) →
        eigCount (QN Sig (X ω)) (edgeVal N σ (2 * numBands N σ) / 2) = min M N := by
    by_cases hb : τ / 2 ≤ edgeVal N σ (2 * numBands N σ)
    · exact ⟨_, h₅ N (le_of_max_le_left (le_of_max_le_left hNb)) M Sig X hm hb,
        fun ω hω _ => hω⟩
    · exact ⟨Set.univ, rm_hp_univ, fun ω _ h => absurd h hb⟩
  set S := (Finset.range (numBands N σ + 1)).filter (fun k => 1 ≤ k ∧ k < numBands N σ ∧
      τ / 2 ≤ edgeVal N σ (2 * k) ∧
        τ / 2 ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) with hS
  have hSc : (S.card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact_mod_cast (rm_card_gaps hda hedge).trans hNB
  have hEg := HighProbAt.biInter S (D := D + 1) (C := 1) (by omega) hSc
    (A := fun k => {ω | eigCount (QN Sig (X ω)) (gapMid N σ k) = cumCount N σ k})
    fun k hk => by
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hk
      exact h₄ N (le_of_max_le_right (le_of_max_le_right hNa)) M Sig X k hm hk.2.1 hk.2.2.1
        hk.2.2.2.1 hk.2.2.2.2
  refine rm_hp_mono (rm_hp_inter hN2 (rm_hp_inter hN2 (rm_hp_inter hN2 hEc hEw)
    (rm_hp_inter hN2 hEo hEb)) hEg) ?_
  rintro ω ⟨⟨⟨hc, hw⟩, ho, hb⟩, hg⟩
  simp only [Set.mem_ofPred_eq] at hc hw ho ⊢
  have hg' : ∀ k, 1 ≤ k → k < numBands N σ → τ / 2 ≤ edgeVal N σ (2 * k) →
      τ / 2 ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1) →
        eigCount (QN Sig (X ω)) (gapMid N σ k) = cumCount N σ k := by
    intro k hk1 hkp ha hw'
    have hkS : k ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hk1, hkp, ha, hw'⟩
    exact Set.mem_iInter₂.1 hg k hkS
  have hd : RmData τ ε (N ^ ε₁) ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε₁ / 2)) σ (QN Sig (X ω)) :=
    ⟨hs1, hy, hYt, hA2, hA3, hA4, hA5, hc, fun l hl => by rw [hyeq]; exact hw l hl, ho, hg',
      hbx ω hb⟩
  exact rm_rig_det hda2 hσ (rm_herm hm.sigma.posDef (X ω)) hd hedge hbulk hr1 hr2

/-! ## Instances

Gaussian `X` with `Σ = I_M` and `N = 2M` (Marchenko–Pastur data `σ = 1`, `M/N = 1/2`), at
`τ = 1/5`, `ε = D = 1`. Assumption 2.1 is discharged at every `M ≥ 1`. The regularity hypotheses
(Definition 2.7) concern the deterministic edges and density of `ϱ` at `N = 2M`; they stay
binders, as does `2M ≥ N₀`. They hold together for this data: `p = 1`,
`a₁ = 3/2 + √2`, `a₂ = 3/2 − √2 < τ/2`, `|a₁ − a₂| = 2√2`, `|x₁ + 1| = √2 − 1`, and the
density `ρ(E) = √((a₁ − E)(E − a₂))/(2πE)` is at least `0.07 min(1, τ')^{1/2}` on
`[a₂ + τ', a₁ − τ']`. -/

/-- `Σ = I` satisfies the eigenvalue conditions of Assumption 2.1 at `τ = 1/5`. -/
private lemma rm_sigma_one (M : ℕ) :
    SigmaAssumption (1 / 5 : ℝ) (1 : Matrix (Fin M) (Fin M) ℝ) where
  posDef := Matrix.PosDef.one
  eigenvalues_le := fun i => by
    rw [eigenvalues_one]
    norm_num
  gap := by
    have h : {i : Fin M | (Matrix.PosDef.one :
        (1 : Matrix (Fin M) (Fin M) ℝ).PosDef).isHermitian.eigenvalues i
          ∈ Set.Icc 0 (1 / 5 : ℝ)} = ∅ := by
      ext i
      simp only [eigenvalues_one, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      norm_num
    rw [h]
    simp only [Set.ncard_empty, Nat.cast_zero]
    positivity

/-- Assumption 2.1 for Gaussian `X`, `Σ = I_M`, `N = 2M`, `τ = 1/5`. -/
private lemma rm_model_mp {M : ℕ} (hM : 1 ≤ M) :
    IsModel (1 / 5) gaussMoment M (2 * M) (1 : Matrix (Fin M) (Fin M) ℝ) (gaussX M (2 * M)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hr : (M : ℝ) / ((2 * M : ℕ) : ℝ) = 1 / 2 := by push_cast; field_simp
  exact isModel_gaussX (by omega) (by rw [hr]; norm_num) (by rw [hr]; norm_num) (rm_sigma_one M)

/-- `rigidity` for Gaussian `X`, `Σ = I_M`, `N = 2M`, at `τ = 1/5`, `ε = D = 1` and
`c(τ') = √(min(1, τ'))/20` (conditional: the edge and bulk regularity hypotheses are binders).
This `c` tends to `0` with `τ'`, as any admissible `c` must: by `rhoDens_edge` the density
vanishes like a square root at a regular edge, while `[a₂ + τ', a₁ − τ']` reaches `a₁` as
`τ' → 0`. For the data above the density on that window is at least
`0.07 min(1, τ')^{1/2} ≥ c(τ')`. -/
example : ∃ N₀ : ℕ, ∀ M : ℕ, 1 ≤ M → N₀ ≤ 2 * M →
    (∀ k, 1 ≤ k → k ≤ 2 * numBands (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) →
      1 / 5 / 2 ≤ edgeVal (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k →
      RegularEdge (1 / 5 / 2) (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k) →
    (∀ k, 1 ≤ k → k ≤ numBands (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) →
      RegularBulk (fun τ' => √(min 1 τ') / 20) (2 * M)
        (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k) →
    HighProbAt (Ω := GaussSpace M (2 * M)) (2 * M) 1 {ω | ∀ k, 1 ≤ k →
      k ≤ numBands (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k →
        1 / 5 ≤ gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k i →
        |lamBand (1 : Matrix (Fin M) (Fin M) ℝ) (gaussX M (2 * M) ω) k i -
            gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k i| ≤
          rigBound (2 * M) (bandNat (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) k) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity (1 / 5) gaussMoment (fun τ' => √(min 1 τ') / 20) 1 1
    (by norm_num) (by norm_num)
  exact ⟨N₀, fun M hM hN he hb => h (2 * M) hN M 1 (gaussX M (2 * M)) (rm_model_mp hM) he hb⟩

/-- `rigidity_edge` for Gaussian `X`, `Σ = I_M`, `N = 2M`, at `τ = 1/5`, `ε = D = 1`, at the
top edge `k = 1` (band `k̂ = 1`; conditional: the regularity of the edge is a binder). -/
example : ∃ N₀ : ℕ, ∀ M : ℕ, 1 ≤ M → N₀ ≤ 2 * M →
    RegularEdge (1 / 5) (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 →
    HighProbAt (Ω := GaussSpace M (2 * M)) (2 * M) 1 {ω | ∀ i, 1 ≤ i →
      i ≤ bandNat (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 →
      gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 i ∈
        Set.Icc (edgeVal (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 - edgeTau' (1 / 5) / 2)
          (edgeVal (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 + edgeTau' (1 / 5) / 2) →
      |lamBand (1 : Matrix (Fin M) (Fin M) ℝ) (gaussX M (2 * M) ω) 1 i -
          gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 i| ≤
        rigBound (2 * M) (bandNat (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_edge (1 / 5) gaussMoment 1 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun M hM hN he => h (2 * M) hN M 1 (gaussX M (2 * M)) 1 (rm_model_mp hM) he⟩

/-- `rigidity_bulk` for Gaussian `X`, `Σ = I_M`, `N = 2M`, at `τ = 1/5`, `τ' = 1/10`,
`ε = D = 1`, `c(τ') = √(min(1, τ'))/20`, in the band `k = 1` with its regular upper edge
(conditional: the bulk and edge regularity are binders). -/
example : ∃ N₀ : ℕ, ∀ M : ℕ, 1 ≤ M → N₀ ≤ 2 * M →
    RegularBulk (fun τ' => √(min 1 τ') / 20) (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 →
    RegularEdge (1 / 5) (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) (2 * 1 - 1) →
    HighProbAt (Ω := GaussSpace M (2 * M)) (2 * M) 1 {ω | ∀ i, 1 ≤ i →
      i ≤ bandNat (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 →
      gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 i ∈
        Set.Icc (edgeVal (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) (2 * 1) + 1 / 10)
          (edgeVal (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) (2 * 1 - 1) - 1 / 10) →
      |lamBand (1 : Matrix (Fin M) (Fin M) ℝ) (gaussX M (2 * M) ω) 1 i -
          gammaBand (2 * M) (specOf (1 : Matrix (Fin M) (Fin M) ℝ)) 1 i| ≤
        ((2 * M : ℕ) : ℝ) ^ (1 : ℝ) * ((2 * M : ℕ) : ℝ)⁻¹} := by
  obtain ⟨N₀, h⟩ := rigidity_bulk (1 / 5) (1 / 10) (fun τ' => √(min 1 τ') / 20) gaussMoment 1 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N₀, fun M hM hN hb he =>
    h (2 * M) hN M 1 (gaussX M (2 * M)) 1 (rm_model_mp hM) hb (Or.inr he)⟩

end Anisotropic

#print axioms Anisotropic.rigidity
#print axioms Anisotropic.rigidity_edge
#print axioms Anisotropic.rigidity_bulk
