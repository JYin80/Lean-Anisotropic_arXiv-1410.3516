import Mathlib

/-!
# A volumetric net of the unit sphere

A finite `η`-net of the Euclidean unit sphere of `ℝ^d` with at most `(3/η)^d` points, for
`0 < η ≤ 1`. This is the covering tool for the lower bound `c ≤ E₁₁` of Lemma 10.4 for a
Gaussian block.

The proof is volumetric. A finite subset of the sphere whose points are pairwise at Euclidean
distance more than `η` has at most `(3/η)^d` points, because the open balls of radius `η/2`
around its points are pairwise disjoint and lie in the ball of radius `1 + η/2`. Hence such a
set cannot be enlarged forever, and a set that cannot be enlarged is an `η`-net.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- The squared Euclidean norm of `x` read in `EuclideanSpace ℝ (Fin d)` is `x ⬝ᵥ x`. -/
private lemma sphereNet_norm_sq {d : ℕ} (x : Fin d → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- `(x - y) ⬝ᵥ (x - y)` is symmetric in `x` and `y`. -/
private lemma sphereNet_sub_dot_comm {d : ℕ} (x y : Fin d → ℝ) :
    (x - y) ⬝ᵥ (x - y) = (y - x) ⬝ᵥ (y - x) := by
  rw [← neg_sub y x, neg_dotProduct, dotProduct_neg, neg_neg]

/-- A finite subset of the unit sphere of `ℝ^d` whose distinct points are at squared
Euclidean distance more than `η²` has at most `(3/η)^d` points, for `0 < η ≤ 1`. -/
private lemma sphereNet_card_le (d : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (T : Finset (Fin d → ℝ)) (hT : ∀ u ∈ T, u ⬝ᵥ u = 1)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → η ^ 2 < (x - y) ⬝ᵥ (x - y)) :
    (T.card : ℝ) ≤ (3 / η) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
      have := hT u hu
      simp at this
    simp [this]
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set E := EuclideanSpace ℝ (Fin d)
  let e : (Fin d → ℝ) → E := fun x => WithLp.toLp 2 x
  have hnorm : ∀ u ∈ T, ‖e u‖ = 1 := by
    intro u hu
    have h1 := sphereNet_norm_sq u
    rw [hT u hu] at h1
    have h0 : 0 ≤ ‖e u‖ := norm_nonneg _
    nlinarith
  have hdist : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → η ≤ dist (e x) (e y) := by
    intro x hx y hy hxy
    rw [dist_eq_norm]
    have h1 : e x - e y = WithLp.toLp 2 (x - y) := (WithLp.toLp_sub 2 x y).symm
    have h2 := sphereNet_norm_sq (d := d) (x - y)
    rw [← h1] at h2
    have h3 := hsep x hx y hy hxy
    rw [← h2] at h3
    exact (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3).le
  -- volumes of balls in `E`
  set C : ℝ≥0∞ := ENNReal.ofReal (√Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) with hC
  have hball : ∀ (x : E) (r : ℝ), 0 ≤ r →
      volume (Metric.ball x r) = ENNReal.ofReal (r ^ d) * C := by
    intro x r hr
    rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_pow hr]
  have hC0 : C ≠ 0 := by
    rw [hC, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    apply div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    exact Real.Gamma_pos_of_pos (by positivity)
  have hCtop : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hη2 : 0 ≤ η / 2 := by positivity
  have hdisj : (T : Set (Fin d → ℝ)).PairwiseDisjoint
      (fun x => Metric.ball (e x) (η / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    have := hdist x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ T, Metric.ball (e x) (η / 2)) ⊆ Metric.ball (0 : E) (1 + η / 2) := by
    refine Set.iUnion₂_subset fun x hx => Metric.ball_subset_ball' ?_
    rw [dist_zero_right, hnorm x hx]
    linarith
  have hvol : (T.card : ℝ≥0∞) * (ENNReal.ofReal ((η / 2) ^ d) * C) ≤
      ENNReal.ofReal ((1 + η / 2) ^ d) * C := by
    calc (T.card : ℝ≥0∞) * (ENNReal.ofReal ((η / 2) ^ d) * C)
        = ∑ x ∈ T, volume (Metric.ball (e x) (η / 2)) := by
          rw [Finset.sum_congr rfl fun x _ => hball (e x) (η / 2) hη2, Finset.sum_const,
            nsmul_eq_mul]
      _ = volume (⋃ x ∈ T, Metric.ball (e x) (η / 2)) :=
          (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
      _ ≤ volume (Metric.ball (0 : E) (1 + η / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((1 + η / 2) ^ d) * C := hball 0 _ (by positivity)
  rw [← mul_assoc] at hvol
  have hvol' := (ENNReal.mul_le_mul_iff_left hC0 hCtop).mp hvol
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol'
  have hpos : 0 < (η / 2) ^ d := by positivity
  have hkey : (3 / η) ^ d * (η / 2) ^ d = (3 / 2) ^ d := by
    rw [← mul_pow]; congr 1; field_simp
  have hbase : (1 + η / 2) ^ d ≤ (3 / 2) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  refine le_of_mul_le_mul_right ?_ hpos
  rw [hkey]
  exact hvol'.trans hbase

/-- Volumetric net of the unit sphere of `ℝ^d`: size at most `(3/η)^d`. -/
theorem exists_sphere_net (d : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : Finset (Fin d → ℝ), (∀ u ∈ T, u ⬝ᵥ u = 1) ∧ (T.card : ℝ) ≤ (3 / η) ^ d ∧
      ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 → ∃ u' ∈ T, (u - u') ⬝ᵥ (u - u') ≤ η ^ 2 := by
  classical
  -- a separated subset of the sphere that cannot be enlarged
  suffices h : ∃ T : Finset (Fin d → ℝ), ((∀ u ∈ T, u ⬝ᵥ u = 1) ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → η ^ 2 < (x - y) ⬝ᵥ (x - y)) ∧
      ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 → ∃ u' ∈ T, (u - u') ⬝ᵥ (u - u') ≤ η ^ 2 by
    obtain ⟨T, ⟨hT, hsep⟩, hnet⟩ := h
    exact ⟨T, hT, sphereNet_card_le d hη hη1 T hT hsep, hnet⟩
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ n : ℕ, ∃ T : Finset (Fin d → ℝ), ((∀ u ∈ T, u ⬝ᵥ u = 1) ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → η ^ 2 < (x - y) ⬝ᵥ (x - y)) ∧ T.card = n := by
    intro n
    induction n with
    | zero => exact ⟨∅, ⟨by simp, by simp⟩, rfl⟩
    | succ n ih =>
      obtain ⟨T, hTsep, hcard⟩ := ih
      obtain ⟨u, hu, hfar⟩ := hcon T hTsep
      have huT : u ∉ T := by
        intro huT
        have := hfar u huT
        simp only [sub_self, zero_dotProduct] at this
        nlinarith
      refine ⟨insert u T, ⟨?_, ?_⟩, by rw [Finset.card_insert_of_notMem huT, hcard]⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hu
        · exact hTsep.1 v hv
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx' <;>
          rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact absurd rfl hxy
        · exact hfar y hy'
        · rw [sphereNet_sub_dot_comm]; exact hfar x hx'
        · exact hTsep.2 x hx' y hy' hxy
  obtain ⟨T, ⟨hT, hsep⟩, hcard⟩ := hgrow (⌊(3 / η) ^ d⌋₊ + 1)
  have h1 := sphereNet_card_le d hη hη1 T hT hsep
  rw [hcard] at h1
  push_cast at h1
  linarith [Nat.lt_floor_add_one ((3 / η) ^ d)]

/-- The net at `d = 2`, `η = 1/2`: at most `36` points on the unit circle. -/
example : ∃ T : Finset (Fin 2 → ℝ), (∀ u ∈ T, u ⬝ᵥ u = 1) ∧
    (T.card : ℝ) ≤ (3 / (1 / 2 : ℝ)) ^ 2 ∧
      ∀ u : Fin 2 → ℝ, u ⬝ᵥ u = 1 → ∃ u' ∈ T, (u - u') ⬝ᵥ (u - u') ≤ (1 / 2 : ℝ) ^ 2 :=
  exists_sphere_net 2 (by norm_num) (by norm_num)

end Anisotropic
