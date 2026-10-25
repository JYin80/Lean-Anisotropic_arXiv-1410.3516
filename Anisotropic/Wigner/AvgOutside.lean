import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeSqrt
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The averaged law with gain outside the spectrum, for a random symmetric matrix with the averaged law and rigid extremes -/

/-- Maximum modulus with the weight `((ζ − E)² − r²)⁴` on the circle `|ζ − E| = r`. -/
theorem norm_mul_weight_le {f : ℂ → ℂ} {E r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (E : ℂ) r))
    (hM : ∀ ζ : ℂ, ‖ζ - E‖ = r → ‖f ζ‖ * ‖(ζ - E) ^ 2 - (r : ℂ) ^ 2‖ ^ 4 ≤ M)
    {z : ℂ} (hz : ‖z - E‖ < r) : ‖f z‖ * ‖(z - E) ^ 2 - (r : ℂ) ^ 2‖ ^ 4 ≤ M := by
  set F : ℂ → ℂ := fun ζ => f ζ * ((ζ - E) ^ 2 - (r : ℂ) ^ 2) ^ 4 with hFdef
  have hF : DifferentiableOn ℂ F (Metric.closedBall (E : ℂ) r) :=
    hf.mul ((((differentiableOn_id.sub_const _).pow 2).sub_const _).pow 4)
  have hd : DiffContOnCl ℂ F (Metric.ball (E : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact hF
  have hzc : z ∈ closure (Metric.ball (E : ℂ) r) := subset_closure (mem_ball_iff_norm.2 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd
    (C := M) (fun ζ hζ => by
      rw [frontier_ball _ hr.ne'] at hζ
      have := hM ζ (mem_sphere_iff_norm.1 hζ)
      simpa only [hFdef, norm_mul, norm_pow] using this) hzc
  simpa only [hFdef, norm_mul, norm_pow] using key

/-- On the circle `|ζ − E| = ρ`: `|(ζ − E)² − ρ²| = 2ρ |Im ζ|`. -/
private theorem aux_norm_weight {E ρ : ℝ} (hρ : 0 ≤ ρ) {ζ : ℂ} (hζ : ‖ζ - E‖ = ρ) :
    ‖(ζ - E) ^ 2 - (ρ : ℂ) ^ 2‖ = 2 * ρ * |ζ.im| := by
  set x := ζ.re - E
  set y := ζ.im
  have hu : ζ - (E : ℂ) = ⟨x, y⟩ := Complex.ext (by simp [x]) (by simp [y])
  have hxy : x ^ 2 + y ^ 2 = ρ ^ 2 := by
    rw [← hζ, hu, Complex.sq_norm, Complex.normSq_mk]; ring
  have hw : (ζ - E) ^ 2 - (ρ : ℂ) ^ 2 = ⟨-2 * y ^ 2, 2 * x * y⟩ := by
    rw [hu]
    apply Complex.ext
    · simp [sq]; nlinarith [hxy]
    · simp [sq]; ring
  rw [hw]
  have h2 : ‖(⟨-2 * y ^ 2, 2 * x * y⟩ : ℂ)‖ ^ 2 = (2 * ρ * |y|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk, mul_pow, mul_pow, sq_abs]
    nlinarith [hxy]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- At `z = E + iη`: `|(z − E)² − ρ²| = ρ² + η²`. -/
private theorem aux_norm_weight_center {E ρ : ℝ} {z : ℂ} (hz : z.re = E) :
    ‖(z - E) ^ 2 - (ρ : ℂ) ^ 2‖ = ρ ^ 2 + z.im ^ 2 := by
  have hw : (z - E) ^ 2 - (ρ : ℂ) ^ 2 = ((-(ρ ^ 2 + z.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [sq, hz]; ring
    · simp [sq, hz]
  rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]

/-- Maximum modulus with the weight `((ζ − E)² − ρ²)⁴`, `ρ = r/2`, for a conjugation-symmetric
`g` analytic on `B(E, r)` with `|g| ≤ B` there and `|g(ζ)| ≤ Y / Im ζ` on the arc
`{|ζ − E| = ρ, Im ζ ≥ T}`: at `z = E + iη` inside the circle,
`|g(z)| ρ⁸ ≤ 16 Y ρ⁷ + B (2ρT)⁴`. -/
private theorem aux_core {g : ℂ → ℂ} {E r B Y T : ℝ} (hr : 0 < r) (hY : 0 ≤ Y)
    (hg : DifferentiableOn ℂ g (Metric.ball (E : ℂ) r))
    (hconj : ∀ ζ ∈ Metric.ball (E : ℂ) r, g ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (g ζ))
    (hB : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖g ζ‖ ≤ B)
    (harc : ∀ ζ : ℂ, ‖ζ - E‖ = r / 2 → T ≤ ζ.im → ‖g ζ‖ ≤ Y / ζ.im)
    {z : ℂ} (hz : ‖z - E‖ < r / 2) (hzE : z.re = E) :
    ‖g z‖ * (r / 2) ^ 8 ≤ 16 * Y * (r / 2) ^ 7 + B * (2 * (r / 2) * T) ^ 4 := by
  set ρ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsub : Metric.closedBall (E : ℂ) ρ ⊆ Metric.ball (E : ℂ) r :=
    Metric.closedBall_subset_ball (by linarith)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB E (Metric.mem_ball_self hr))
  have hM : ∀ ζ : ℂ, ‖ζ - E‖ = ρ →
      ‖g ζ‖ * ‖(ζ - E) ^ 2 - (ρ : ℂ) ^ 2‖ ^ 4 ≤ 16 * Y * ρ ^ 7 + B * (2 * ρ * T) ^ 4 := by
    intro ζ hζ
    have hζb : ζ ∈ Metric.ball (E : ℂ) r := hsub (mem_closedBall_iff_norm.2 hζ.le)
    rw [aux_norm_weight hρ0.le hζ]
    have him : |ζ.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (ζ - E)
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    by_cases hTζ : T ≤ |ζ.im|
    · -- the arc: reduce to `Im ζ ≥ T` by conjugation
      have hY' : ‖g ζ‖ ≤ Y / |ζ.im| := by
        rcases le_or_gt 0 ζ.im with h0 | h0
        · rw [abs_of_nonneg h0] at hTζ ⊢
          exact harc ζ hζ hTζ
        · rw [abs_of_neg h0] at hTζ ⊢
          have hc : ‖(starRingEnd ℂ) ζ - E‖ = ρ := by
            rw [← Complex.conj_ofReal, ← map_sub, Complex.norm_conj, hζ]
          have := harc _ hc (by simpa using hTζ)
          rw [← Complex.norm_conj, ← hconj ζ hζb]
          simpa using this
      rcases (abs_nonneg ζ.im).eq_or_lt with h0 | hpos
      · rw [← h0]
        simp only [mul_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
        positivity
      · calc ‖g ζ‖ * (2 * ρ * |ζ.im|) ^ 4 ≤ Y / |ζ.im| * (2 * ρ * |ζ.im|) ^ 4 :=
              mul_le_mul_of_nonneg_right hY' (by positivity)
          _ = 16 * Y * ρ ^ 4 * |ζ.im| ^ 3 := by field_simp; ring
          _ ≤ 16 * Y * ρ ^ 4 * ρ ^ 3 := by gcongr
          _ = 16 * Y * ρ ^ 7 := by ring
          _ ≤ 16 * Y * ρ ^ 7 + B * (2 * ρ * T) ^ 4 := le_add_of_nonneg_right (by positivity)
    · push Not at hTζ
      calc ‖g ζ‖ * (2 * ρ * |ζ.im|) ^ 4 ≤ B * (2 * ρ * T) ^ 4 := by
            apply mul_le_mul (hB ζ hζb) _ (by positivity) hB0
            gcongr
          _ ≤ 16 * Y * ρ ^ 7 + B * (2 * ρ * T) ^ 4 := le_add_of_nonneg_left (by positivity)
  have hgc : DifferentiableOn ℂ g (Metric.closedBall (E : ℂ) ρ) := hg.mono hsub
  have key := norm_mul_weight_le hρ0 hgc hM hz
  rw [aux_norm_weight_center hzE] at key
  have h1 : ρ ^ 8 ≤ (ρ ^ 2 + z.im ^ 2) ^ 4 := by
    have : ρ ^ 2 ≤ ρ ^ 2 + z.im ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    calc ρ ^ 8 = (ρ ^ 2) ^ 4 := by ring
      _ ≤ _ := by gcongr
  exact le_trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) key

/-- Cauchy estimate and mean value: if `|g| ≤ B` on `B(E, r)`, then `g` is `4B/r`-Lipschitz on
`B(E, 3r/4)`. -/
private theorem aux_lip {g : ℂ → ℂ} {E r B : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball (E : ℂ) r))
    (hB : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖g ζ‖ ≤ B) {w₁ w₂ : ℂ}
    (h₁ : w₁ ∈ Metric.ball (E : ℂ) (3 * r / 4)) (h₂ : w₂ ∈ Metric.ball (E : ℂ) (3 * r / 4)) :
    ‖g w₂ - g w₁‖ ≤ 4 * B / r * ‖w₂ - w₁‖ := by
  have hsub : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4),
      Metric.closedBall x (r / 4) ⊆ Metric.ball (E : ℂ) r := by
    intro x hx y hy
    rw [mem_ball_iff_norm] at hx ⊢
    rw [mem_closedBall_iff_norm] at hy
    calc ‖y - E‖ = ‖(y - x) + (x - E)‖ := by ring_nf
      _ ≤ ‖y - x‖ + ‖x - E‖ := norm_add_le _ _
      _ < r := by linarith
  have hd : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4), DifferentiableAt ℂ g x := fun x hx =>
    hg.differentiableAt (Metric.isOpen_ball.mem_nhds
      (hsub x hx (Metric.mem_closedBall_self (by positivity))))
  have hder : ∀ x ∈ Metric.ball (E : ℂ) (3 * r / 4), ‖deriv g x‖ ≤ 4 * B / r := by
    intro x hx
    have hR : (0 : ℝ) < r / 4 := by positivity
    have hcont : DiffContOnCl ℂ g (Metric.ball x (r / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hR.ne']
      exact hg.mono (hsub x hx)
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hcont
      (fun y hy => hB y (hsub x hx (Metric.sphere_subset_closedBall hy)))
    calc ‖deriv g x‖ ≤ B / (r / 4) := this
      _ = 4 * B / r := by field_simp
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hder (convex_ball _ _) h₁ h₂

/-- The net on the arc: grid points `pⱼₖ = E − r/2 + jh + i kh`. If `|g| ≤ B` on `B(E, r)`,
`8h ≤ r`, `h ≤ t`, and `|g(p)| ≤ X / Im p` at every grid point with `jh ≤ r`, `t ≤ kh ≤ r/2`,
`p ∈ B(E, 3r/4)`, then `|g(ζ)| ≤ 2X / Im ζ + 8Bh/r` on the arc `{|ζ − E| = r/2, Im ζ ≥ 2t}`. -/
private theorem aux_arc {g : ℂ → ℂ} {E r B h t X : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball (E : ℂ) r))
    (hB : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖g ζ‖ ≤ B) (hh : 0 < h) (hh8 : 8 * h ≤ r) (hht : h ≤ t)
    (hX : 0 ≤ X)
    (hnet : ∀ j k : ℕ, (j : ℝ) * h ≤ r → t ≤ (k : ℝ) * h → (k : ℝ) * h ≤ r / 2 →
      ‖(((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I) - E‖ < 3 * r / 4 →
      ‖g (((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I)‖ ≤ X / ((k : ℝ) * h))
    {ζ : ℂ} (hζ : ‖ζ - E‖ = r / 2) (hζt : 2 * t ≤ ζ.im) :
    ‖g ζ‖ ≤ 2 * X / ζ.im + 4 * B / r * (2 * h) := by
  have hre : |ζ.re - E| ≤ r / 2 := by
    have := Complex.abs_re_le_norm (ζ - E)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have him : ζ.im ≤ r / 2 := by
    have := Complex.abs_im_le_norm (ζ - E)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith [le_abs_self ζ.im]
  have ht0 : 0 < t := lt_of_lt_of_le hh hht
  have hζ0 : 0 < ζ.im := by linarith
  set u := ζ.re - E + r / 2 with hu
  have hu0 : 0 ≤ u := by rw [abs_le] at hre; linarith
  have hu1 : u ≤ r := by rw [abs_le] at hre; linarith
  set j := ⌊u / h⌋₊ with hj
  set k := ⌊ζ.im / h⌋₊ with hk
  have hj1 : (j : ℝ) * h ≤ u := by
    have := Nat.floor_le (div_nonneg hu0 hh.le)
    rwa [le_div_iff₀ hh] at this
  have hj2 : u < (j : ℝ) * h + h := by
    have := Nat.lt_floor_add_one (u / h)
    rw [div_lt_iff₀ hh] at this
    linarith
  have hk1 : (k : ℝ) * h ≤ ζ.im := by
    have := Nat.floor_le (div_nonneg hζ0.le hh.le)
    rwa [le_div_iff₀ hh] at this
  have hk2 : ζ.im < (k : ℝ) * h + h := by
    have := Nat.lt_floor_add_one (ζ.im / h)
    rw [div_lt_iff₀ hh] at this
    linarith
  set p : ℂ := ((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I with hp
  have hpre : p.re = E - r / 2 + j * h := by simp [hp]
  have hpim : p.im = k * h := by simp [hp]
  have hpz : ‖ζ - p‖ < 2 * h := by
    calc ‖ζ - p‖ ≤ |(ζ - p).re| + |(ζ - p).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |ζ.re - p.re| + |ζ.im - p.im| := by simp
      _ < h + h := by
          rw [hpre, hpim]
          apply add_lt_add
          · rw [abs_lt]; constructor <;> linarith
          · rw [abs_lt]; constructor <;> linarith
      _ = 2 * h := by ring
  have hpE : ‖p - E‖ < 3 * r / 4 := by
    calc ‖p - E‖ = ‖(p - ζ) + (ζ - E)‖ := by ring_nf
      _ ≤ ‖p - ζ‖ + ‖ζ - E‖ := norm_add_le _ _
      _ < 2 * h + r / 2 := by rw [norm_sub_rev]; linarith
      _ ≤ 3 * r / 4 := by linarith
  have hkt : t ≤ (k : ℝ) * h := by linarith
  have hnetp := hnet j k (by linarith) hkt (by linarith) hpE
  rw [← hp] at hnetp
  have hζb : ζ ∈ Metric.ball (E : ℂ) (3 * r / 4) := by
    rw [mem_ball_iff_norm, hζ]; linarith
  have hlip := aux_lip hr hg hB (mem_ball_iff_norm.2 hpE) hζb
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB E (Metric.mem_ball_self hr))
  have hkpos : 0 < (k : ℝ) * h := by linarith
  have hhalf : ζ.im / 2 ≤ (k : ℝ) * h := by linarith
  calc ‖g ζ‖ = ‖g p + (g ζ - g p)‖ := by ring_nf
    _ ≤ ‖g p‖ + ‖g ζ - g p‖ := norm_add_le _ _
    _ ≤ X / ((k : ℝ) * h) + 4 * B / r * ‖ζ - p‖ := add_le_add hnetp hlip
    _ ≤ X / (ζ.im / 2) + 4 * B / r * (2 * h) := by
        gcongr
    _ = 2 * X / ζ.im + 4 * B / r * (2 * h) := by field_simp

/-- The empirical Stieltjes transform of points at distance `≥ d` from `E` is analytic on
`B(E, r)` for `r < d`, bounded by `(d − r)⁻¹` there, and conjugation-symmetric. -/
private theorem aux_emp {N : ℕ} (lam : Fin N → ℝ) {E d r : ℝ} (hrd : r < d)
    (hlam : ∀ k, d ≤ |lam k - E|) :
    DifferentiableOn ℂ (empStieltjes lam) (Metric.ball (E : ℂ) r) ∧
      (∀ ζ ∈ Metric.ball (E : ℂ) r, ‖empStieltjes lam ζ‖ ≤ (d - r)⁻¹) ∧
      (∀ ζ : ℂ, empStieltjes lam ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (empStieltjes lam ζ)) := by
  have hdist : ∀ ζ ∈ Metric.ball (E : ℂ) r, ∀ k, d - r ≤ ‖(lam k : ℂ) - ζ‖ := by
    intro ζ hζ k
    rw [mem_ball_iff_norm] at hζ
    have h1 : |lam k - E| = ‖(lam k : ℂ) - E‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(lam k : ℂ) - E‖ ≤ ‖(lam k : ℂ) - ζ‖ + ‖ζ - E‖ := by
      calc ‖(lam k : ℂ) - E‖ = ‖((lam k : ℂ) - ζ) + (ζ - E)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [hlam k]
  have hne : ∀ ζ ∈ Metric.ball (E : ℂ) r, ∀ k, (lam k : ℂ) - ζ ≠ 0 := by
    intro ζ hζ k h0
    have := hdist ζ hζ k
    rw [h0, norm_zero] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro ζ hζ
    unfold empStieltjes
    refine (DifferentiableAt.differentiableWithinAt ?_)
    refine (differentiableAt_const _).mul ?_
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).sub differentiableAt_id).inv (hne ζ hζ k)
  · intro ζ hζ
    unfold empStieltjes
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have : (0 : ℝ) ≤ (d - r)⁻¹ := inv_nonneg.2 (by linarith)
      simpa using this
    have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
    have hdr : 0 < d - r := by linarith
    calc ‖(N : ℂ)⁻¹ * ∑ j, ((lam j : ℂ) - ζ)⁻¹‖ ≤ (N : ℝ)⁻¹ * ∑ j, ‖((lam j : ℂ) - ζ)⁻¹‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, (d - r)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
          rw [norm_inv]
          exact inv_anti₀ hdr (hdist ζ hζ j)
      _ = (d - r)⁻¹ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  · intro ζ
    unfold empStieltjes
    rw [map_mul, map_inv₀, map_sum, Complex.conj_natCast]
    congr 2
    ext j
    rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- The real orthogonal matrix of eigenvectors of a symmetric `H`: `U Uᵀ = 1`, `Uᵀ U = 1`,
`H = U diag(λ) Uᵀ`. -/
private theorem aux_eig_decomp {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      H = U * diagonal hH.eigenvalues * Uᵀ := by
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- `N⁻¹ tr (W + A − ζ)⁻¹` is the Stieltjes transform of the eigenvalues of the symmetric
`W + A`, for `Im ζ ≠ 0`. -/
private theorem aux_mNW_eq {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hH : (Wm + A).IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    mNW A Wm ζ = empStieltjes (specOf (Wm + A)) ζ := by
  obtain ⟨U, hUU, hUU', hAU⟩ := aux_eig_decomp hH
  set l := hH.eigenvalues with hl
  have hne : ∀ k, (l k : ℂ) - ζ ≠ 0 := by
    intro k h0
    apply hζ
    have := congrArg Complex.im h0
    simpa using this
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx (Wm + A) - ζ • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - ζ) * (cplx U)ᵀ := by
    have h1 : cplx (Wm + A) = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hAU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - ζ) =
        diagonal (fun k => (l k : ℂ)) - ζ • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  have hG : GW A Wm ζ = cplx U * diagonal (fun k => ((l k : ℂ) - ζ)⁻¹) * (cplx U)ᵀ := by
    unfold GW
    refine Matrix.inv_eq_right_inv ?_
    rw [hM]
    calc cplx U * diagonal (fun k => (l k : ℂ) - ζ) * (cplx U)ᵀ *
          (cplx U * diagonal (fun k => ((l k : ℂ) - ζ)⁻¹) * (cplx U)ᵀ)
        = cplx U * diagonal (fun k => (l k : ℂ) - ζ) * ((cplx U)ᵀ * cplx U) *
          diagonal (fun k => ((l k : ℂ) - ζ)⁻¹) * (cplx U)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
          have : (fun k => ((l k : ℂ) - ζ) * ((l k : ℂ) - ζ)⁻¹) = fun _ => 1 := by
            funext k
            exact mul_inv_cancel₀ (hne k)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]
  unfold mNW empStieltjes
  rw [hG, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.trace_diagonal,
    specOf_eq hH]

/-- The extreme eigenvalues bound all eigenvalues: `λ_N ≤ λ_k ≤ λ_1`. -/
private theorem aux_eig_bounds {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (hN : 1 ≤ N) (k : Fin N) : sortedEig H N ≤ specOf H k ∧ specOf H k ≤ sortedEig H 1 := by
  constructor
  · have h := (sortedEig_ge_iff hH (i := N) hN le_rfl (sortedEig H N)).1 le_rfl
    unfold eigCount at h
    have hc : (Finset.univ.filter fun j => sortedEig H N ≤ specOf H j).card =
        Fintype.card (Fin N) := by
      apply le_antisymm (Finset.card_le_univ _)
      simpa using h
    have := Finset.eq_univ_of_card _ hc
    have hk := Finset.mem_univ k
    rw [← this] at hk
    exact (Finset.mem_filter.1 hk).2
  · rw [sortedEig_ge_iff hH le_rfl hN]
    unfold eigCount
    exact Finset.card_pos.2 ⟨k, by simp⟩

/-- The standing bound is invariant under the reflection `a ↦ −a` (through `m^W_{−a}(−z̄) =
−conj m^W_a(z)`). -/
private theorem aux_sb_neg {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} {a : Fin N → ℝ}
    (h : StandingBoundW τ a (domW τ N)) : StandingBoundW τ (-a) (domW τ N) := by
  intro z hz i
  set w := -(starRingEnd ℂ) z with hwdef
  have hw : w ∈ domW τ N := by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨by simpa [w] using h1, by simpa [w] using h2, by simpa [w] using h3,
      by simpa [w] using h4⟩
  have hz' : -(starRingEnd ℂ) w = z := by simp [w]
  have hm : mW (-a) z = -(starRingEnd ℂ) (mW a w) := by rw [← hz']; exact mW_neg hN a hw.1
  have e : -(mW (-a) z) + (((-a) i : ℝ) : ℂ) - z = -(starRingEnd ℂ) (-(mW a w) + a i - w) := by
    rw [hm, ← hz']
    simp only [map_sub, map_add, map_neg, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg,
]
    ring
  rw [e, norm_neg, Complex.norm_conj]
  exact h w hw i

/-- The continuation of `m^W` on both sides of `[L₋, L₊]`: for `κ(E) > 0` there is an analytic `f`
on `B(E, c min(κ, 1))` equal to `m^W` on the upper half-disc, conjugation-symmetric and bounded by
`K` (the left side by reflection). -/
private theorem aux_cont {τ : ℝ} (hτ : 0 < τ) :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) → ∀ E : ℝ, 0 < kappaW a E →
        ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (E : ℂ) (c * min (kappaW a E) 1)) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (kappaW a E) 1), 0 < ζ.im → f ζ = mW a ζ) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (kappaW a E) 1),
            f ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (f ζ)) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (kappaW a E) 1), ‖f ζ‖ ≤ K) := by
  obtain ⟨c, K, hc, hc4, hK, N₀, h⟩ := mW_continuation_right hτ
  refine ⟨c, K, hc, hc4, hK, max N₀ 1, fun N hN a ha hSB E hκ => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N ≥ N₀ := le_of_max_le_left hN
  unfold kappaW at hκ ⊢
  rcases max_choice (max (E - LpW a) (LmW a - E)) 0 with h0 | h0
  swap
  · rw [h0] at hκ; exact absurd hκ (lt_irrefl 0)
  rw [h0] at hκ ⊢
  rcases max_choice (E - LpW a) (LmW a - E) with h1 | h1
  · rw [h1] at hκ ⊢
    exact h N hN0 a ha hSB E (by linarith)
  · rw [h1] at hκ ⊢
    have ha' : ∀ i, |(-a) i| ≤ τ⁻¹ - 2 := fun i => by simpa using ha i
    have hL : LmW a - E = -E - LpW (-a) := by rw [LmW_neg]; ring
    obtain ⟨f, hf, hfm, hfc, hfb⟩ :=
      h N hN0 (-a) ha' (aux_sb_neg hN1 hSB) (-E) (by rw [hL] at hκ; linarith)
    rw [← hL] at hf hfm hfc hfb
    set R := c * min (LmW a - E) 1 with hR
    have hmem : ∀ ζ ∈ Metric.ball (E : ℂ) R, -(starRingEnd ℂ) ζ ∈ Metric.ball ((-E : ℝ) : ℂ) R := by
      intro ζ hζ
      rw [mem_ball_iff_norm] at hζ ⊢
      have : -(starRingEnd ℂ) ζ - ((-E : ℝ) : ℂ) = -(starRingEnd ℂ) (ζ - E) := by
        simp [map_sub, Complex.conj_ofReal]; ring
      rw [this, norm_neg, Complex.norm_conj]
      exact hζ
    have hmem' : ∀ ζ ∈ Metric.ball (E : ℂ) R, -ζ ∈ Metric.ball ((-E : ℝ) : ℂ) R := by
      intro ζ hζ
      rw [mem_ball_iff_norm] at hζ ⊢
      have : -ζ - ((-E : ℝ) : ℂ) = -(ζ - E) := by push_cast; ring
      rw [this, norm_neg]
      exact hζ
    refine ⟨fun ζ => -(starRingEnd ℂ) (f (-(starRingEnd ℂ) ζ)), ?_, ?_, ?_, ?_⟩
    · intro ζ hζ
      have hd : DifferentiableAt ℂ f (-(starRingEnd ℂ) ζ) :=
        hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hmem ζ hζ))
      have hg : DifferentiableAt ℂ (fun w => f (-w)) ((starRingEnd ℂ) ζ) :=
        hd.comp _ differentiableAt_id.neg
      have := hg.conj_conj
      rw [Complex.conj_conj] at this
      exact this.neg.differentiableWithinAt
    · intro ζ hζ hζim
      have hw : 0 < (-(starRingEnd ℂ) ζ).im := by simpa using hζim
      have hm := mW_neg hN1 (-a) hw
      rw [neg_neg] at hm
      have hzz : -(starRingEnd ℂ) (-(starRingEnd ℂ) ζ) = ζ := by simp
      rw [hzz] at hm
      simp only
      rw [hm, hfm _ (hmem ζ hζ) hw]
    · intro ζ hζ
      have e1 : -(starRingEnd ℂ) ζ = (starRingEnd ℂ) (-ζ) := by simp
      simp only [Complex.conj_conj]
      rw [e1, hfc _ (hmem' ζ hζ)]
      simp
    · intro ζ hζ
      simp only [norm_neg, Complex.norm_conj]
      exact hfb _ (hmem ζ hζ)

/-- `X ≤ N^p` for all large `N`, when `p > 0`. -/
private theorem aux_ev_rpow {p : ℝ} (hp : 0 < p) (X : ℝ) :
    ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)

/-- `S(maxᵢ aᵢ + 1) ≤ 1`. -/
private theorem aux_sW_le_one {N : ℕ} (a : Fin N → ℝ) : sW a ((⨆ i, a i) + 1) ≤ 1 := by
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
private theorem aux_sW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : ∀ i, a i < x) :
    ContinuousAt (sW a) x := by
  unfold sW
  refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
  have hne : (a i - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hx i).ne)
  exact ((continuousAt_const.sub continuousAt_id).pow 2).inv₀ hne

/-- If `maxᵢ aᵢ + τ/4 ≤ x₊`: `x₊ ≤ maxᵢ aᵢ + 1` and `S(x₊) = 1`. -/
private theorem aux_xp_facts {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {a : Fin N → ℝ}
    (hgap : (⨆ i, a i) + τ / 4 ≤ xpW a) : xpW a ≤ (⨆ i, a i) + 1 ∧ sW a (xpW a) = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  set T := {x | α < x ∧ sW a x ≤ 1} with hT
  have hbdd : BddBelow T := ⟨α, fun x hx => hx.1.le⟩
  have hmem : α + 1 ∈ T := ⟨by linarith, aux_sW_le_one a⟩
  have hxp : xpW a = sInf T := rfl
  have hup : xpW a ≤ α + 1 := hxp ▸ csInf_le hbdd hmem
  refine ⟨hup, ?_⟩
  have hgt : ∀ i, a i < xpW a := fun i => by linarith [hle i]
  have hc := aux_sW_continuousAt a hgt
  apply le_antisymm
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), 1 < sW a y := hc.eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨y, hyT, hy⟩ := exists_lt_of_csInf_lt ⟨α + 1, hmem⟩
      (show sInf T < xpW a + δ by rw [← hxp]; linarith)
    have hy1 : xpW a ≤ y := hxp ▸ csInf_le hbdd hyT
    have : dist y (xpW a) < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball this, hyT.2]
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), sW a y < 1 := hc.eventually (gt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set y := xpW a - min (δ / 2) (τ / 8) with hy
    have hm1 : 0 < min (δ / 2) (τ / 8) := lt_min (by linarith) (by linarith)
    have hm2 : min (δ / 2) (τ / 8) ≤ δ / 2 := min_le_left _ _
    have hm3 : min (δ / 2) (τ / 8) ≤ τ / 8 := min_le_right _ _
    have hyd : dist y (xpW a) < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hyT : y ∈ T := ⟨by linarith, (hball hyd).le⟩
    have := hxp ▸ csInf_le hbdd hyT
    linarith

/-- `−B ≤ L₊ ≤ B + 2` when `|aᵢ| ≤ B` (`L₊ = x₊ + N⁻¹ ∑ᵢ (x₊ − aᵢ)⁻¹`, `x₊ ≤ maxᵢ aᵢ + 1`,
and `N⁻¹ ∑ᵢ (x₊ − aᵢ)⁻¹ ≤ S(x₊)^{1/2} = 1`). -/
private theorem aux_LpW_bounds {τ : ℝ} (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ τ⁻¹ - 2) →
      StandingBoundW τ a (domW τ N) → ∀ B : ℝ, (∀ i, |a i| ≤ B) → -B ≤ LpW a ∧ LpW a ≤ B + 2 := by
  obtain ⟨N₁, hN₁⟩ := xpW_sub_ge hτ
  refine ⟨max N₁ 1, fun N hN a ha hSB B hB => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have : Nonempty (Fin N) := ⟨⟨0, hN1⟩⟩
  have hgap := (hN₁ N (le_of_max_le_left hN) a ha hSB).1
  obtain ⟨hup, hS⟩ := aux_xp_facts hN1 hτ hgap
  set x := xpW a with hx
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  have hpos : ∀ i, 0 < x - a i := fun i => by linarith [hle i]
  set u : Fin N → ℝ := fun i => (x - a i)⁻¹ with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => (inv_pos.2 (hpos i)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : LpW a = x + (N : ℝ)⁻¹ * ∑ i, u i := by
    rw [show LpW a = gW a x from rfl]
    unfold gW
    have : ∀ i, (a i - x)⁻¹ = -u i := fun i => by simp only [hu]; rw [← inv_neg, neg_sub]
    simp only [this, Finset.sum_neg_distrib]
    ring
  have hsq : ∑ i, u i ^ 2 = N := by
    have h1 : sW a x = (N : ℝ)⁻¹ * ∑ i, u i ^ 2 := by
      unfold sW
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hu, inv_pow]
      congr 1
      ring
    rw [hS] at h1
    field_simp at h1
    linarith
  have hsum : ∑ i, u i ≤ N := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := u)
    rw [hsq, Finset.card_univ, Fintype.card_fin] at hcs
    have h0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu0 i
    nlinarith
  have hmean0 : 0 ≤ (N : ℝ)⁻¹ * ∑ i, u i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hu0 i)
  have hmean1 : (N : ℝ)⁻¹ * ∑ i, u i ≤ 1 := by
    rw [inv_mul_le_iff₀ hNpos]; linarith
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  have hα1 := abs_le.1 (hB i₀)
  rw [hi₀] at hα1
  constructor
  · rw [hL]; linarith [hle ⟨0, hN1⟩, abs_le.1 (hB ⟨0, hN1⟩)]
  · rw [hL]; linarith

/-- `|E| ≤ B + 2 + X` when `0 < κ(E) ≤ X`, `−B ≤ L₊ ≤ B + 2` and `−(B + 2) ≤ L₋ ≤ B`. -/
private theorem aux_E_bound {N : ℕ} {a : Fin N → ℝ} {E B X : ℝ} (hκ : 0 < kappaW a E)
    (hκX : kappaW a E ≤ X) (hp : -B ≤ LpW a ∧ LpW a ≤ B + 2) (hm : -(B + 2) ≤ LmW a ∧ LmW a ≤ B) :
    |E| ≤ B + 2 + X := by
  unfold kappaW at hκ hκX
  rcases max_choice (max (E - LpW a) (LmW a - E)) 0 with h0 | h0
  swap
  · rw [h0] at hκ; exact absurd hκ (lt_irrefl 0)
  rw [h0] at hκ hκX
  rw [abs_le]
  rcases max_choice (E - LpW a) (LmW a - E) with h1 | h1
  · rw [h1] at hκ hκX
    constructor <;> linarith [hp.1, hp.2]
  · rw [h1] at hκ hκX
    constructor <;> linarith [hm.1, hm.2]

/-- `κ(E) − δ ≤ |λ − E|` for every `λ ∈ [L₋ − δ, L₊ + δ]`, when `κ(E) > 0`. -/
private theorem aux_eig_dist {N : ℕ} {a : Fin N → ℝ} {E δ l : ℝ} (hκ : 0 < kappaW a E)
    (hl1 : LmW a - δ ≤ l) (hl2 : l ≤ LpW a + δ) : kappaW a E - δ ≤ |l - E| := by
  unfold kappaW at hκ ⊢
  rcases max_choice (max (E - LpW a) (LmW a - E)) 0 with h0 | h0
  swap
  · rw [h0] at hκ; exact absurd hκ (lt_irrefl 0)
  rw [h0] at hκ ⊢
  rcases max_choice (E - LpW a) (LmW a - E) with h1 | h1
  · rw [h1]
    calc E - LpW a - δ ≤ E - l := by linarith
      _ ≤ |l - E| := by rw [abs_sub_comm]; exact le_abs_self _
  · rw [h1]
    calc LmW a - E - δ ≤ l - E := by linarith
      _ ≤ |l - E| := le_abs_self _

/-- The deterministic estimate for one realization `W` (fixed `ω`): if the eigenvalues of `W + A`
are at distance `≥ 7κ/8` from `E`, `f` continues `m^W` on `B(E, r)` with `r ≤ κ/4`, and
`|m_N − m^W| ≤ X / Im p` at the grid points `p` of the arc net, then at `z = E + iη` inside
the circle `|ζ − E| = r/2`:
`|m_N(z) − m^W(z)| (r/2)⁸ ≤ 48 X (r/2)⁷ + (2/κ + K)(4 (r/2) t)⁴`. -/
private theorem aux_omega {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {f : ℂ → ℂ} {E κ r K X h t : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ κ / 4)
    (hf : DifferentiableOn ℂ f (Metric.ball (E : ℂ) r))
    (hfm : ∀ ζ ∈ Metric.ball (E : ℂ) r, 0 < ζ.im → f ζ = mW (specOf A) ζ)
    (hfc : ∀ ζ ∈ Metric.ball (E : ℂ) r, f ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (f ζ))
    (hfb : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖f ζ‖ ≤ K)
    (hlam : ∀ k, 7 * κ / 8 ≤ |specOf (Wm + A) k - E|)
    (hh : 0 < h) (hh8 : 8 * h ≤ r) (hht : h ≤ t) (hX : 0 ≤ X) (hhX : 4 * (2 / κ + K) * h ≤ X)
    (hnet : ∀ j k : ℕ, (j : ℝ) * h ≤ r → t ≤ (k : ℝ) * h → (k : ℝ) * h ≤ r / 2 →
      ‖(((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I) - E‖ < 3 * r / 4 →
      ‖mNW A Wm (((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I) -
        mW (specOf A) (((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I)‖ ≤
          X / ((k : ℝ) * h))
    {z : ℂ} (hz : ‖z - E‖ < r / 2) (hzE : z.re = E) (hz0 : 0 < z.im) :
    ‖mNW A Wm z - mW (specOf A) z‖ * (r / 2) ^ 8 ≤
      16 * (3 * X) * (r / 2) ^ 7 + (2 / κ + K) * (2 * (r / 2) * (2 * t)) ^ 4 := by
  set lam := specOf (Wm + A) with hlamdef
  obtain ⟨hsd, hsb, hsc⟩ := aux_emp lam (d := 7 * κ / 8) (r := r) (by linarith) hlam
  set g : ℂ → ℂ := fun ζ => empStieltjes lam ζ - f ζ with hgdef
  set B := 2 / κ + K with hBdef
  have hg : DifferentiableOn ℂ g (Metric.ball (E : ℂ) r) := hsd.sub hf
  have hgc : ∀ ζ ∈ Metric.ball (E : ℂ) r, g ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (g ζ) := by
    intro ζ hζ
    simp only [hgdef, map_sub, hsc ζ, hfc ζ hζ]
  have hgb : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖g ζ‖ ≤ B := by
    intro ζ hζ
    have h1 : (7 * κ / 8 - r)⁻¹ ≤ 2 / κ := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      linarith
    calc ‖g ζ‖ ≤ ‖empStieltjes lam ζ‖ + ‖f ζ‖ := norm_sub_le _ _
      _ ≤ (7 * κ / 8 - r)⁻¹ + K := add_le_add (hsb ζ hζ) (hfb ζ hζ)
      _ ≤ B := by rw [hBdef]; linarith
  have hgm : ∀ ζ ∈ Metric.ball (E : ℂ) r, 0 < ζ.im → g ζ = mNW A Wm ζ - mW (specOf A) ζ := by
    intro ζ hζ hζim
    simp only [hgdef, hfm ζ hζ hζim, aux_mNW_eq hH hζim.ne']
    rfl
  have hnet' : ∀ j k : ℕ, (j : ℝ) * h ≤ r → t ≤ (k : ℝ) * h → (k : ℝ) * h ≤ r / 2 →
      ‖(((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I) - E‖ < 3 * r / 4 →
      ‖g (((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I)‖ ≤
        X / ((k : ℝ) * h) := by
    intro j k hj hk1 hk2 hpE
    have hmem : (((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I) ∈
        Metric.ball (E : ℂ) r := by
      rw [mem_ball_iff_norm]; linarith
    have him : 0 < ((((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I)).im := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero]
      linarith [lt_of_lt_of_le hh hht]
    rw [hgm _ hmem him]
    exact hnet j k hj hk1 hk2 hpE
  have harc : ∀ ζ : ℂ, ‖ζ - E‖ = r / 2 → 2 * t ≤ ζ.im → ‖g ζ‖ ≤ 3 * X / ζ.im := by
    intro ζ hζ hζt
    have h1 := aux_arc hr hg hgb hh hh8 hht hX hnet' hζ hζt
    have ht0 : 0 < t := lt_of_lt_of_le hh hht
    have hζ0 : 0 < ζ.im := by linarith
    have him : ζ.im ≤ r / 2 := by
      have := Complex.abs_im_le_norm (ζ - E)
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith [le_abs_self ζ.im]
    have h2 : 4 * B / r * (2 * h) ≤ X / ζ.im := by
      rw [le_div_iff₀ hζ0]
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hgb E (Metric.mem_ball_self hr))
      calc 4 * B / r * (2 * h) * ζ.im ≤ 4 * B / r * (2 * h) * (r / 2) := by gcongr
        _ = 4 * B * h := by field_simp
        _ ≤ X := hhX
    calc ‖g ζ‖ ≤ 2 * X / ζ.im + 4 * B / r * (2 * h) := h1
      _ ≤ 2 * X / ζ.im + X / ζ.im := by linarith
      _ = 3 * X / ζ.im := by ring
  have key := aux_core (T := 2 * t) hr (by positivity : 0 ≤ 3 * X) hg hgc hgb harc hz hzE
  have hzb : z ∈ Metric.ball (E : ℂ) r := by rw [mem_ball_iff_norm]; linarith
  rw [hgm z hzb hz0] at key
  exact key

/-- `N^{1/3} · N · (N^{−1+τ})⁴ ≤ (N^{−2/3+τ_S})⁴` for `τ ≤ τ_S`. -/
private theorem aux_rpow_t {n τ τS : ℝ} (hn : 1 ≤ n) (h : τ ≤ τS) :
    n ^ (1 / 3 : ℝ) * n * (n ^ (-1 + τ)) ^ 4 ≤ (n ^ (-2 / 3 + τS)) ^ 4 := by
  have hn0 : 0 < n := by linarith
  rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_mul_natCast hn0.le]
  have e : n ^ (1 / 3 : ℝ) * n = n ^ (1 / 3 + 1 : ℝ) := by rw [Real.rpow_add hn0, Real.rpow_one]
  rw [e, ← Real.rpow_add hn0]
  apply Real.rpow_le_rpow_of_exponent_le hn
  push_cast
  linarith

/-- `8 N^{ε₁} N^{−2/3} ≤ N^{−2/3+τ_S}` once `8 ≤ N^{τ_S/2}` and `ε₁ ≤ τ_S/2`. -/
private theorem aux_rpow_delta {n τS ε₁ : ℝ} (hn : 1 ≤ n) (h8 : 8 ≤ n ^ (τS / 2))
    (hε : ε₁ ≤ τS / 2) : 8 * (n ^ ε₁ * n ^ (-2 / 3 : ℝ)) ≤ n ^ (-2 / 3 + τS) := by
  have hn0 : 0 < n := by linarith
  calc 8 * (n ^ ε₁ * n ^ (-2 / 3 : ℝ)) ≤ n ^ (τS / 2) * (n ^ ε₁ * n ^ (-2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = n ^ (τS / 2 + ε₁ + -2 / 3) := by rw [Real.rpow_add hn0, Real.rpow_add hn0]; ring
    _ ≤ n ^ (-2 / 3 + τS) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

/-- `N^{ε₁} N^{ε/2} ≤ N^ε` for `ε₁ ≤ ε/2`. -/
private theorem aux_rpow_eps {n ε ε₁ : ℝ} (hn : 1 ≤ n) (h : ε₁ ≤ ε / 2) :
    n ^ ε₁ * n ^ (ε / 2) ≤ n ^ ε := by
  have hn0 : 0 < n := by linarith
  rw [← Real.rpow_add hn0]
  exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

/-- The final arithmetic: from `Q (r/2)⁸ ≤ 48 X (r/2)⁷ + (2/κ + K)(4 (r/2) t)⁴` with `r ≥ c τ_S κ`,
`X = N^{ε₁}/N` and the large-`N` conditions to `Q ≤ N^ε N^{−τ_S/2} / (N η)`. -/
private theorem aux_final {n ε ε₁ τS c K κ η r t X Q : ℝ} (hn1 : 1 ≤ n) (hτS : 0 < τS)
    (hc : 0 < c) (hK : 0 < K) (hκ0 : 0 < κ) (hη : 0 < η) (hκhi : κ ≤ τS⁻¹)
    (hrlow : c * τS * κ ≤ r) (hηhi : η ≤ n ^ (-τS / 2) * κ) (hX : X = n ^ ε₁ / n)
    (h192 : 192 * n ^ ε₁ ≤ c * τS * n ^ ε)
    (ht4 : 2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) * (n * t ^ 4) ≤ κ ^ 4) (hε1 : 1 ≤ n ^ ε)
    (key : Q * (r / 2) ^ 8 ≤
      16 * (3 * X) * (r / 2) ^ 7 + (2 / κ + K) * (2 * (r / 2) * (2 * t)) ^ 4) :
    Q ≤ n ^ ε * (n ^ (-τS / 2) / (n * η)) := by
  have hn0 : 0 < n := by linarith
  have hcτ : 0 < c * τS := mul_pos hc hτS
  set u := c * τS * κ / 2 with hu
  have hu0 : 0 < u := by positivity
  set ρ := r / 2 with hρ
  have huρ : u ≤ ρ := by rw [hu, hρ]; linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le hu0 huρ
  set B := 2 / κ + K with hB
  have hB0 : 0 < B := by positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  set T0 := n ^ ε / (n * κ) with hT0
  have hT0t : T0 ≤ n ^ ε * (n ^ (-τS / 2) / (n * η)) := by
    rw [hT0, div_eq_mul_one_div (n ^ ε)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hQ : Q ≤ 48 * X / ρ + 256 * B * t ^ 4 / ρ ^ 4 := by
    have h1 : Q ≤ (16 * (3 * X) * ρ ^ 7 + B * (2 * ρ * (2 * t)) ^ 4) / ρ ^ 8 :=
      (le_div_iff₀ (by positivity)).2 key
    have e : (16 * (3 * X) * ρ ^ 7 + B * (2 * ρ * (2 * t)) ^ 4) / ρ ^ 8 =
        48 * X / ρ + 256 * B * t ^ 4 / ρ ^ 4 := by
      rw [div_add_div _ _ hρ0.ne' (by positivity), div_eq_div_iff (by positivity) (by positivity)]
      ring
    linarith
  have h1 : 48 * X / ρ ≤ T0 / 2 := by
    calc 48 * X / ρ ≤ 48 * X / u := div_le_div_of_nonneg_left (by positivity) hu0 huρ
      _ ≤ T0 / 2 := by
          have e1 : 48 * X / u = 96 * n ^ ε₁ / (n * (c * τS) * κ) := by
            rw [hX, hu, div_eq_div_iff (by positivity) (by positivity)]
            field_simp
            ring
          have e2 : T0 / 2 = n ^ ε / (2 * n * κ) := by
            rw [hT0, div_div, div_eq_div_iff (by positivity) (by positivity)]; ring
          rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
          have := mul_le_mul_of_nonneg_right h192 (by positivity : (0 : ℝ) ≤ n * κ)
          nlinarith
  have h2 : 256 * B * t ^ 4 / ρ ^ 4 ≤ T0 / 2 := by
    have hBκ : B * κ ≤ 2 + K / τS := by
      rw [hB, add_mul, div_mul_cancel₀ _ hκ0.ne']
      have : K * κ ≤ K / τS := by
        rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hκhi hK.le
      linarith
    have hu4 : u ^ 4 ≤ ρ ^ 4 := pow_le_pow_left₀ hu0.le huρ 4
    calc 256 * B * t ^ 4 / ρ ^ 4 ≤ 256 * B * t ^ 4 / u ^ 4 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hu4
      _ ≤ T0 / 2 := by
          have e1 : 256 * B * t ^ 4 / u ^ 4 = 4096 * B * t ^ 4 / ((c * τS) ^ 4 * κ ^ 4) := by
            rw [hu, div_eq_div_iff (by positivity) (by positivity)]
            ring
          have e2 : T0 / 2 = n ^ ε / (2 * n * κ) := by
            rw [hT0, div_div, div_eq_div_iff (by positivity) (by positivity)]; ring
          rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
          have hC : 2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) * (c * τS) ^ 4 =
              8192 * (2 + K / τS) := by
            rw [mul_assoc, div_mul_cancel₀ _ (by positivity)]; ring
          have h3 : 8192 * (2 + K / τS) * (n * t ^ 4) ≤ (c * τS) ^ 4 * κ ^ 4 := by
            have := mul_le_mul_of_nonneg_left ht4 (by positivity : (0 : ℝ) ≤ (c * τS) ^ 4)
            calc 8192 * (2 + K / τS) * (n * t ^ 4) =
                (c * τS) ^ 4 * (2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) * (n * t ^ 4)) := by
                  rw [← hC]; ring
              _ ≤ _ := this
          have h4 : (c * τS) ^ 4 * κ ^ 4 ≤ n ^ ε * ((c * τS) ^ 4 * κ ^ 4) :=
            le_mul_of_one_le_left (by positivity) hε1
          have h6 : 8192 * (B * κ) * (n * t ^ 4) ≤ 8192 * (2 + K / τS) * (n * t ^ 4) := by
            gcongr
          calc 4096 * B * t ^ 4 * (2 * n * κ) = 8192 * (B * κ) * (n * t ^ 4) := by ring
            _ ≤ _ := by linarith
  linarith

/-- The grid point `E − r/2 + j h + i k h`, `h = r/(16N²)`, of the net on the arc. -/
private def aux_grid (E r : ℝ) (N : ℕ) (jk : ℕ × ℕ) : ℂ :=
  ((E - r / 2 + jk.1 * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) +
    ((jk.2 * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) * Complex.I

/-- The radius `r = c min(κ, 1)`: `0 < r ≤ κ/4`, `r ≤ 1/4` and `r ≥ c τ_S κ` when `κ ≤ τ_S⁻¹`. -/
private theorem aux_radius {c κ τS : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hκ0 : 0 < κ)
    (hτS : 0 < τS) (hτS1 : τS ≤ 1) (hκhi : κ ≤ τS⁻¹) :
    0 < c * min κ 1 ∧ c * min κ 1 ≤ κ / 4 ∧ c * min κ 1 ≤ 1 / 4 ∧ c * τS * κ ≤ c * min κ 1 := by
  have hmin : τS * κ ≤ min κ 1 := by
    refine le_min (mul_le_of_le_one_left hκ0.le hτS1) ?_
    calc τS * κ ≤ τS * τS⁻¹ := mul_le_mul_of_nonneg_left hκhi hτS.le
      _ = 1 := mul_inv_cancel₀ hτS.ne'
  have hminpos : 0 < min κ 1 := lt_min hκ0 one_pos
  refine ⟨mul_pos hc hminpos, ?_, ?_, ?_⟩
  · calc c * min κ 1 ≤ 1 / 4 * κ := mul_le_mul hc4 (min_le_left _ _) hminpos.le (by norm_num)
      _ = κ / 4 := by ring
  · calc c * min κ 1 ≤ 1 / 4 * 1 := mul_le_mul hc4 (min_le_right _ _) hminpos.le (by norm_num)
      _ = 1 / 4 := by ring
  · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hmin hc.le

/-- The net parameters `h = r/(16N²)`, `t = N^{−1+τ}`, `X = N^{ε₁}/N`: `8h ≤ r`, `h ≤ t`,
`4(2/κ + K) h ≤ X`. -/
private theorem aux_params {n τ ε₁ κ r K : ℝ} (hn : 300 ≤ n) (hτ : 0 < τ) (hε₁0 : 0 < ε₁)
    (hκ0 : 0 < κ) (hr0 : 0 < r) (hrκ : r ≤ κ / 4) (hr14 : r ≤ 1 / 4) (hK : 0 < K) (hKn : K ≤ n) :
    0 < r / (16 * n ^ 2) ∧ 8 * (r / (16 * n ^ 2)) ≤ r ∧ r / (16 * n ^ 2) ≤ n ^ (-1 + τ) ∧
      0 ≤ n ^ ε₁ / n ∧ 4 * (2 / κ + K) * (r / (16 * n ^ 2)) ≤ n ^ ε₁ / n := by
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have h16 : (0 : ℝ) < 16 * n ^ 2 := by positivity
  have ht_low : n⁻¹ ≤ n ^ (-1 + τ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hX1 : 1 / n ≤ n ^ ε₁ / n :=
    div_le_div_of_nonneg_right (Real.one_le_rpow hn1 hε₁0.le) hn0.le
  refine ⟨by positivity, ?_, ?_, le_trans (by positivity) hX1, ?_⟩
  · rw [mul_div_assoc', div_le_iff₀ h16]
    have : (8 : ℝ) ≤ 16 * n ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hr0.le]
  · refine le_trans ?_ ht_low
    rw [div_le_iff₀ h16]
    have : n⁻¹ * (16 * n ^ 2) = 16 * n := by field_simp
    rw [this]
    linarith
  · have h2r : 2 / κ * r ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hκ0]; linarith
    have hKr : K * r ≤ n / 4 := by
      calc K * r ≤ K * (1 / 4) := mul_le_mul_of_nonneg_left hr14 hK.le
        _ ≤ n / 4 := by linarith
    calc 4 * (2 / κ + K) * (r / (16 * n ^ 2)) = (2 / κ * r + K * r) / (4 * n ^ 2) := by
          field_simp; ring
      _ ≤ (1 / 2 + n / 4) / (4 * n ^ 2) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / n := by rw [div_le_div_iff₀ (by positivity) hn0]; nlinarith
      _ ≤ n ^ ε₁ / n := hX1

/-- The grid points used on the arc lie in `𝐃^W(τ, N)`, have index `< 16N² + 1`, and the
averaged law there gives `|m_N − m^W| ≤ X / Im p`. -/
private theorem aux_net {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} {τ τS ε₁ E r : ℝ}
    (hn1 : (1 : ℝ) ≤ N) (hr0 : 0 < r) (hr14 : r ≤ 1 / 4) (hτS4 : 4 ≤ τS⁻¹)
    (hτinv : 4 * τS⁻¹ ≤ τ⁻¹) (hEb : |E| ≤ τS⁻¹ + 2 + τS⁻¹)
    (hnet : ∀ j k : ℕ, j < 16 * N ^ 2 + 1 → k < 16 * N ^ 2 + 1 →
      aux_grid E r N (j, k) ∈ domW τ N →
      ‖mNW A Wm (aux_grid E r N (j, k)) - mW (specOf A) (aux_grid E r N (j, k))‖ ≤
        (N : ℝ) ^ ε₁ * (1 / (N * (aux_grid E r N (j, k)).im)))
    (j k : ℕ) (hj : (j : ℝ) * (r / (16 * (N : ℝ) ^ 2)) ≤ r)
    (hk1 : (N : ℝ) ^ (-1 + τ) ≤ (k : ℝ) * (r / (16 * (N : ℝ) ^ 2)))
    (hk2 : (k : ℝ) * (r / (16 * (N : ℝ) ^ 2)) ≤ r / 2) :
    ‖mNW A Wm (((E - r / 2 + j * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) +
        ((k * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) * Complex.I) -
      mW (specOf A) (((E - r / 2 + j * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) +
        ((k * (r / (16 * (N : ℝ) ^ 2)) : ℝ) : ℂ) * Complex.I)‖ ≤
      (N : ℝ) ^ ε₁ / N / ((k : ℝ) * (r / (16 * (N : ℝ) ^ 2))) := by
  set n : ℝ := (N : ℝ) with hn
  set h := r / (16 * n ^ 2) with hh
  have hn0 : (0 : ℝ) < n := by linarith
  have h16 : (0 : ℝ) < 16 * n ^ 2 := by positivity
  have hh0 : 0 < h := by positivity
  have ht0 : 0 < n ^ (-1 + τ) := Real.rpow_pos_of_pos hn0 _
  have hj' : (j : ℝ) ≤ 16 * n ^ 2 := by
    rw [hh, mul_div_assoc', div_le_iff₀ h16] at hj
    nlinarith
  have hk' : (k : ℝ) ≤ 16 * n ^ 2 := by
    rw [hh, mul_div_assoc', div_le_iff₀ h16] at hk2
    nlinarith
  have hjN : j ≤ 16 * N ^ 2 := by rw [hn] at hj'; exact_mod_cast hj'
  have hkN : k ≤ 16 * N ^ 2 := by rw [hn] at hk'; exact_mod_cast hk'
  have hgrid : aux_grid E r N (j, k) =
      ((E - r / 2 + j * h : ℝ) : ℂ) + ((k * h : ℝ) : ℂ) * Complex.I := rfl
  have hpre : (aux_grid E r N (j, k)).re = E - r / 2 + j * h := by rw [hgrid]; simp
  have hpim : (aux_grid E r N (j, k)).im = k * h := by rw [hgrid]; simp
  have hpdom : aux_grid E r N (j, k) ∈ domW τ N := by
    have hj0 : (0 : ℝ) ≤ j * h := by positivity
    refine ⟨by rw [hpim]; linarith, ?_, by rw [hpim]; exact hk1, by rw [hpim]; linarith⟩
    rw [hpre, abs_le]
    rw [abs_le] at hEb
    constructor <;> linarith
  have hb := hnet j k (by omega) (by omega) hpdom
  rw [hpim, hgrid] at hb
  have hkh : 0 < (k : ℝ) * h := lt_of_lt_of_le ht0 hk1
  calc _ ≤ n ^ ε₁ * (1 / (n * (k * h))) := hb
    _ = n ^ ε₁ / n / ((k : ℝ) * h) := by field_simp

/-- The estimate on the good event, for one realization `Wm`: rigid extremes within
`N^{ε₁} N^{−2/3}` and the averaged law at the grid points give
`|m_N(z) − m^W(z)| ≤ N^ε N^{−τ_S/2}/(Nη)` at `z ∈ 𝐒_τ`. -/
private theorem aux_good {N : ℕ} (hN1 : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hH : (Wm + A).IsHermitian) {τ τS ε ε₁ c K E κ : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hτ : 0 < τ) (hτS : 0 < τS) (hτS1 : τS ≤ 1 / 4) (hτinv : 4 * τS⁻¹ ≤ τ⁻¹) (hττS : τ ≤ τS / 4)
    (hε₁0 : 0 < ε₁) (hε₁τ : ε₁ ≤ τS / 2) (hε₁ε : ε₁ ≤ ε / 2)
    (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hK : 0 < K)
    (hn300 : (300 : ℝ) ≤ N) (hKN : K ≤ N) (h8N : 8 ≤ (N : ℝ) ^ (τS / 2))
    (hcN : 2 / (c * τS) + 1 ≤ (N : ℝ) ^ (τS / 2)) (h192N : 192 / (c * τS) ≤ (N : ℝ) ^ (ε / 2))
    (hC₁N : 2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hκ : κ = kappaW (specOf A) E) (hκlo : (N : ℝ) ^ (-2 / 3 + τS) ≤ κ) (hκhi : κ ≤ τS⁻¹)
    (hEb : |E| ≤ τS⁻¹ + 2 + τS⁻¹)
    (hf : DifferentiableOn ℂ f (Metric.ball (E : ℂ) (c * min κ 1)))
    (hfm : ∀ ζ ∈ Metric.ball (E : ℂ) (c * min κ 1), 0 < ζ.im → f ζ = mW (specOf A) ζ)
    (hfc : ∀ ζ ∈ Metric.ball (E : ℂ) (c * min κ 1),
      f ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (f ζ))
    (hfb : ∀ ζ ∈ Metric.ball (E : ℂ) (c * min κ 1), ‖f ζ‖ ≤ K)
    (hrig1 : max (sortedEig (Wm + A) 1 - LpW (specOf A)) 0 ≤
      (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-2 / 3 : ℝ))
    (hrig2 : max (LmW (specOf A) - sortedEig (Wm + A) N) 0 ≤
      (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-2 / 3 : ℝ))
    (hnet : ∀ j k : ℕ, j < 16 * N ^ 2 + 1 → k < 16 * N ^ 2 + 1 →
      aux_grid E (c * min κ 1) N (j, k) ∈ domW τ N →
      ‖mNW A Wm (aux_grid E (c * min κ 1) N (j, k)) -
        mW (specOf A) (aux_grid E (c * min κ 1) N (j, k))‖ ≤
        (N : ℝ) ^ ε₁ * (1 / (N * (aux_grid E (c * min κ 1) N (j, k)).im)))
    (hzE : z.re = E) (hηlo : (N : ℝ) ^ (-τS) * κ ≤ z.im)
    (hηhi : z.im ≤ (N : ℝ) ^ (-τS / 2) * κ) :
    ‖mNW A Wm z - mW (specOf A) z‖ ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (-τS / 2) / (N * z.im)) := by
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hτS4 : 4 ≤ τS⁻¹ := by rw [le_inv_comm₀ (by norm_num) hτS]; linarith
  have hq0 : 0 < (N : ℝ) ^ (-2 / 3 + τS) := Real.rpow_pos_of_pos hn0 _
  have hκ0 : 0 < κ := lt_of_lt_of_le hq0 hκlo
  have hz0 : 0 < z.im := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hn0 _) hκ0) hηlo
  obtain ⟨hr0, hrκ, hr14, hrlow⟩ := aux_radius hc hc4 hκ0 hτS (by linarith) hκhi
  -- eigenvalues away from `E`
  have hδκ : (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ κ / 8 := by
    have := aux_rpow_delta hn1 h8N hε₁τ; linarith
  have hlam : ∀ k, 7 * κ / 8 ≤ |specOf (Wm + A) k - E| := by
    intro k
    obtain ⟨hk1, hk2⟩ := aux_eig_bounds hH hN1 k
    have hκ0' : 0 < kappaW (specOf A) E := hκ ▸ hκ0
    have := aux_eig_dist hκ0'
      ((show LmW (specOf A) - (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ sortedEig (Wm + A) N by
        linarith [le_max_left (LmW (specOf A) - sortedEig (Wm + A) N) 0]).trans hk1)
      (hk2.trans (show sortedEig (Wm + A) 1 ≤
          LpW (specOf A) + (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-2 / 3 : ℝ) by
        linarith [le_max_left (sortedEig (Wm + A) 1 - LpW (specOf A)) 0]))
    rw [← hκ] at this
    linarith
  obtain ⟨hh0, hh8, hht, hX0, hhX⟩ := aux_params hn300 hτ hε₁0 hκ0 hr0 hrκ hr14 hK hKN
  have hzn : ‖z - (E : ℂ)‖ = z.im := by
    have e : z - (E : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp [hzE]) (by simp)
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hz0]
  have hηr : z.im < c * min κ 1 / 2 := by
    have hinv : (N : ℝ) ^ (-τS / 2) < c * τS / 2 := by
      rw [show -τS / 2 = -(τS / 2) by ring, Real.rpow_neg hn0.le,
        inv_lt_comm₀ (Real.rpow_pos_of_pos hn0 _) (by positivity)]
      calc (c * τS / 2)⁻¹ = 2 / (c * τS) := by field_simp
        _ < (N : ℝ) ^ (τS / 2) := by linarith
    calc z.im ≤ (N : ℝ) ^ (-τS / 2) * κ := hηhi
      _ < c * τS / 2 * κ := mul_lt_mul_of_pos_right hinv hκ0
      _ ≤ c * min κ 1 / 2 := by linarith
  have key := aux_omega hH hκ0 hr0 hrκ hf hfm hfc hfb hlam hh0 hh8 hht hX0 hhX
    (fun j k hj hk1 hk2 _ => aux_net hn1 hr0 hr14 hτS4 hτinv hEb hnet j k hj hk1 hk2)
    (by rw [hzn]; exact hηr) hzE hz0
  have h192 : 192 * (N : ℝ) ^ ε₁ ≤ c * τS * (N : ℝ) ^ ε := by
    have h1 : 192 ≤ c * τS * (N : ℝ) ^ (ε / 2) := by
      calc (192 : ℝ) ≤ (N : ℝ) ^ (ε / 2) * (c * τS) := (div_le_iff₀ (mul_pos hc hτS)).1 h192N
        _ = c * τS * (N : ℝ) ^ (ε / 2) := by ring
    have h2 := aux_rpow_eps hn1 hε₁ε
    have h3 : 0 < (N : ℝ) ^ ε₁ := Real.rpow_pos_of_pos hn0 _
    calc 192 * (N : ℝ) ^ ε₁ ≤ c * τS * (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ ε₁ :=
          mul_le_mul_of_nonneg_right h1 h3.le
      _ = c * τS * ((N : ℝ) ^ ε₁ * (N : ℝ) ^ (ε / 2)) := by ring
      _ ≤ c * τS * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left h2 (by positivity)
  have ht4 : 2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) * ((N : ℝ) * ((N : ℝ) ^ (-1 + τ)) ^ 4) ≤
      κ ^ 4 := by
    have h1 := aux_rpow_t hn1 (show τ ≤ τS by linarith)
    have h2 : ((N : ℝ) ^ (-2 / 3 + τS)) ^ 4 ≤ κ ^ 4 := pow_le_pow_left₀ hq0.le hκlo 4
    have h3 : 0 ≤ (N : ℝ) * ((N : ℝ) ^ (-1 + τ)) ^ 4 := by positivity
    calc 2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) * ((N : ℝ) * ((N : ℝ) ^ (-1 + τ)) ^ 4) ≤
        (N : ℝ) ^ (1 / 3 : ℝ) * ((N : ℝ) * ((N : ℝ) ^ (-1 + τ)) ^ 4) :=
          mul_le_mul_of_nonneg_right hC₁N h3
      _ = (N : ℝ) ^ (1 / 3 : ℝ) * N * ((N : ℝ) ^ (-1 + τ)) ^ 4 := by ring
      _ ≤ κ ^ 4 := h1.trans h2
  exact aux_final hn1 hτS hc hK hκ0 hz0 hκhi hrlow hηhi rfl h192 ht4
    (Real.one_le_rpow hn1 (by linarith)) key

/-- Union bound: `ℙ(S) ≤ (2 + |I|) x` when `S ⊆ R₁ ∪ R₂ ∪ ⋃_{i ∈ I} Gᵢ` and each piece has
probability `≤ x`. -/
private theorem aux_prob {Ω : Type} [MeasureSpace Ω] {S R1 R2 : Set Ω} {G : ℕ × ℕ → Set Ω}
    {I : Finset (ℕ × ℕ)} {x y : ℝ} (hx : 0 ≤ x)
    (hsub : ∀ ω, ω ∉ R1 → ω ∉ R2 → (∀ i ∈ I, ω ∉ G i) → ω ∉ S)
    (h1 : ℙ R1 ≤ ENNReal.ofReal x) (h2 : ℙ R2 ≤ ENNReal.ofReal x)
    (hG : ∀ i ∈ I, ℙ (G i) ≤ ENNReal.ofReal x) (hxy : (2 + I.card) * x ≤ y) :
    ℙ S ≤ ENNReal.ofReal y := by
  have hS : S ⊆ R1 ∪ R2 ∪ ⋃ i ∈ I, G i := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    exact hsub ω hcon.1.1 hcon.1.2 (fun i hi => hcon.2 i hi) hω
  calc ℙ S ≤ ℙ (R1 ∪ R2 ∪ ⋃ i ∈ I, G i) := measure_mono hS
    _ ≤ ℙ R1 + ℙ R2 + ℙ (⋃ i ∈ I, G i) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal x + ENNReal.ofReal x + ∑ i ∈ I, ENNReal.ofReal x :=
        add_le_add (add_le_add h1 h2) ((measure_biUnion_finset_le I G).trans
          (Finset.sum_le_sum fun i hi => hG i hi))
    _ = ENNReal.ofReal ((2 + I.card) * x) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hx), ← ENNReal.ofReal_add hx hx,
          ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => hx),
          Finset.sum_const, nsmul_eq_mul]
        congr 1
        ring
    _ ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal hxy

/-- The count of the union bound: `(2 + (16N² + 1)²) N^{−(D+5)} ≤ N^{−D}` for `N ≥ 300`. -/
private theorem aux_count {N : ℕ} (hN : 300 ≤ N) (D : ℝ) :
    (2 + ((16 * N ^ 2 + 1) * (16 * N ^ 2 + 1) : ℕ)) * (N : ℝ) ^ (-(D + 5)) ≤ (N : ℝ) ^ (-D) := by
  have hn : (300 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ (-(D + 5)) = (N : ℝ) ^ (-D) / (N : ℝ) ^ 5 := by
    rw [show -(D + 5) = -D - (5 : ℕ) by push_cast; ring, Real.rpow_sub hn0, Real.rpow_natCast]
  rw [e, mul_div_assoc', div_le_iff₀ (by positivity)]
  have hpos : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hn0 _
  rw [mul_comm ((N : ℝ) ^ (-D))]
  apply mul_le_mul_of_nonneg_right _ hpos.le
  push_cast
  have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by nlinarith
  have h5 : 300 * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := by
    have : (N : ℝ) ^ 5 = (N : ℝ) * (N : ℝ) ^ 4 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hn (by positivity)
  nlinarith

/-- The averaged law with gain on `𝐒_τ` (§12.4, the estimate "not hard to deduce"): if the
averaged law holds for `W + A` on `𝐃^W(τ, N)` and its extreme eigenvalues are rigid, then
`N⁻¹ tr(W + A − z)⁻¹ − m^W(z) = O_≺(N^{−τ_S/2}(Nη)⁻¹)` on `𝐒_τ`. -/
theorem avg_law_outside (τ τS ε D : ℝ) (hτ : 0 < τ) (hττS : τ ≤ τS / 4) (hτS1 : τS ≤ 1 / 4)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τS⁻¹ → (∀ ω, (W ω)ᵀ = W ω) →
      StandingBoundW τ (specOf A) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ A W (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => W ω + A) →
      AveragedPhiLawWAt N ε D A W (outDomW τS (specOf A))
        (fun z => (N : ℝ) ^ (-τS / 2) / (N * z.im)) := by
  have hτS : 0 < τS := by linarith
  obtain ⟨c, K, hc, hc4, hK, Nc, hcont⟩ := aux_cont hτ
  obtain ⟨NL, hLb⟩ := aux_LpW_bounds hτ
  have hε₁0 : 0 < min τS ε / 2 := by have := lt_min hτS hε; positivity
  have hε₁τ : min τS ε / 2 ≤ τS / 2 := by have := min_le_left τS ε; linarith
  have hε₁ε : min τS ε / 2 ≤ ε / 2 := by have := min_le_right τS ε; linarith
  have hev : ∀ᶠ N : ℕ in atTop, (Nc ≤ N ∧ NL ≤ N ∧ 300 ≤ N) ∧ (K ≤ (N : ℝ) ∧
      8 ≤ (N : ℝ) ^ (τS / 2)) ∧ (2 / (c * τS) + 1 ≤ (N : ℝ) ^ (τS / 2) ∧
      192 / (c * τS) ≤ (N : ℝ) ^ (ε / 2)) ∧
      2 * (4096 * (2 + K / τS) / (c * τS) ^ 4) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    filter_upwards [eventually_ge_atTop Nc, eventually_ge_atTop NL, eventually_ge_atTop 300,
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop K),
      aux_ev_rpow (half_pos hτS) 8, aux_ev_rpow (half_pos hτS) (2 / (c * τS) + 1),
      aux_ev_rpow (half_pos hε) (192 / (c * τS)),
      aux_ev_rpow (by norm_num : (0 : ℝ) < 1 / 3) (2 * (4096 * (2 + K / τS) / (c * τS) ^ 4))]
      with N h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩, h8⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨min τS ε / 2, D + 5, hε₁0, N₀, ?_⟩
  intro N hN Ω _ _ A W hA hAn hW hSB hlaw hrig
  obtain ⟨⟨hNc, hNL, hN300⟩, ⟨hKN, h8N⟩, ⟨hcN, h192N⟩, hC₁N⟩ := hN₀ N hN
  intro z hz
  have hN1 : 1 ≤ N := by omega
  have hn300 : (300 : ℝ) ≤ N := by exact_mod_cast hN300
  have hn0 : (0 : ℝ) < N := by linarith
  have ha : ∀ i, |specOf A i| ≤ τS⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hAn
  have hτinv : 4 * τS⁻¹ ≤ τ⁻¹ := by
    have : 4 * τS⁻¹ = (τS / 4)⁻¹ := by field_simp
    rw [this]
    exact inv_anti₀ hτ hττS
  have hτS4 : 4 ≤ τS⁻¹ := by rw [le_inv_comm₀ (by norm_num) hτS]; linarith
  have ha' : ∀ i, |specOf A i| ≤ τ⁻¹ - 2 := fun i => (ha i).trans (by linarith)
  obtain ⟨hκlo, hκhi, hηlo, hηhi⟩ := hz
  have hκ0 : 0 < kappaW (specOf A) z.re :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hκlo
  obtain ⟨f, hf, hfm, hfc, hfb⟩ := hcont N hNc (specOf A) ha' hSB z.re hκ0
  have hp := hLb N hNL (specOf A) ha' hSB τS⁻¹ ha
  have hm : -(τS⁻¹ + 2) ≤ LmW (specOf A) ∧ LmW (specOf A) ≤ τS⁻¹ := by
    have h := hLb N hNL (-specOf A) (fun i => by simpa using ha' i) (aux_sb_neg hN1 hSB) τS⁻¹
      (fun i => by simpa using ha i)
    rw [LmW_neg]
    constructor <;> linarith [h.1, h.2]
  have hEb : |z.re| ≤ τS⁻¹ + 2 + τS⁻¹ := aux_E_bound hκ0 hκhi hp hm
  have hrig1 := hrig.1
  have hrig2 := hrig.2
  refine aux_prob (I := Finset.range (16 * N ^ 2 + 1) ×ˢ Finset.range (16 * N ^ 2 + 1))
    (G := fun jk => {ω | aux_grid z.re (c * min (kappaW (specOf A) z.re) 1) N jk ∈ domW τ N ∧
      (N : ℝ) ^ (min τS ε / 2) *
        (1 / (N * (aux_grid z.re (c * min (kappaW (specOf A) z.re) 1) N jk).im)) <
      ‖mNW A (W ω) (aux_grid z.re (c * min (kappaW (specOf A) z.re) 1) N jk) -
        mW (specOf A) (aux_grid z.re (c * min (kappaW (specOf A) z.re) 1) N jk)‖})
    (Real.rpow_nonneg hn0.le _) ?_ hrig1 hrig2 ?_ ?_
  · intro ω h1 h2 h3 hbad
    have hWh : (W ω).IsHermitian := by
      unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hW ω
    have hH : (W ω + A).IsHermitian := hWh.add hA
    have hr1 : max (sortedEig (W ω + A) 1 - LpW (specOf A)) 0 ≤
        (N : ℝ) ^ (min τS ε / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := le_of_not_gt fun hlt => h1 hlt
    have hr2 : max (LmW (specOf A) - sortedEig (W ω + A) N) 0 ≤
        (N : ℝ) ^ (min τS ε / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := le_of_not_gt fun hlt => h2 hlt
    have hbound := aux_good hN1 hH hτ hτS hτS1 hτinv hττS hε₁0 hε₁τ hε₁ε hc hc4 hK hn300 hKN
      h8N hcN h192N hC₁N rfl hκlo hκhi hEb hf hfm hfc hfb hr1 hr2
      (fun j k hj hk hdom => by
        have := h3 (j, k) (Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_range.2 hk⟩)
        exact not_lt.1 fun hlt => this ⟨hdom, hlt⟩) rfl hηlo hηhi
    exact absurd hbad (not_lt.2 hbound)
  · intro jk _
    by_cases hmem : aux_grid z.re (c * min (kappaW (specOf A) z.re) 1) N jk ∈ domW τ N
    · refine (measure_mono ?_).trans (hlaw _ hmem)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact hω.2
    · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      exact absurd hω.1 hmem
  · rw [Finset.card_product, Finset.card_range]
    exact aux_count hN300 D


/-- Maximum modulus with the weight at `f(ζ) = ζ`, `E = 0`, `r = 1`, `M = 16`, `z = i/2`
(`|ζ² − 1| ≤ 2` on the unit circle). -/
example : ‖(fun ζ : ℂ => ζ) (Complex.I / 2)‖ *
    ‖(Complex.I / 2 - ((0 : ℝ) : ℂ)) ^ 2 - ((1 : ℝ) : ℂ) ^ 2‖ ^ 4 ≤ 16 := by
  refine norm_mul_weight_le (f := fun ζ => ζ) (E := 0) (r := 1) one_pos
    differentiableOn_id (fun ζ hζ => ?_) ?_
  · have h0 : ‖ζ‖ = 1 := by simpa using hζ
    have h1 : ‖(ζ - ((0 : ℝ) : ℂ)) ^ 2 - ((1 : ℝ) : ℂ) ^ 2‖ ≤ 2 := by
      calc _ ≤ ‖(ζ - ((0 : ℝ) : ℂ)) ^ 2‖ + ‖((1 : ℝ) : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = 2 := by simp [h0]; norm_num
    calc ‖ζ‖ * ‖(ζ - ((0 : ℝ) : ℂ)) ^ 2 - ((1 : ℝ) : ℂ) ^ 2‖ ^ 4 ≤ 1 * 2 ^ 4 := by
          rw [h0]; gcongr
      _ = 16 := by norm_num
  · norm_num

#print axioms norm_mul_weight_le
#print axioms avg_law_outside

end Anisotropic
