module

public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.LinAlg.Spectral
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Min–max in counting form: subspace bounds, Weyl in counting form, rank and PSD perturbations, the lattice lemma -/

section MinMaxAux

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- The orthogonal matrix whose columns are the eigenvectors of `A`. -/
private def eU (hA : A.IsHermitian) : Matrix (Fin K) (Fin K) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)

/-- The coordinates of `w` in the eigenbasis of `A`. -/
private def eC (hA : A.IsHermitian) (w : Fin K → ℝ) : Fin K → ℝ :=
  star (eU hA) *ᵥ w

private lemma eU_star_mul (hA : A.IsHermitian) : star (eU hA) * eU hA = 1 :=
  Unitary.coe_star_mul_self _

private lemma eU_mul_star (hA : A.IsHermitian) : eU hA * star (eU hA) = 1 :=
  Unitary.coe_mul_star_self _

private lemma eU_mulVec_eC (hA : A.IsHermitian) (w : Fin K → ℝ) : eU hA *ᵥ eC hA w = w := by
  unfold eC
  rw [mulVec_mulVec, eU_mul_star, one_mulVec]

private lemma eU_orth_dot (hA : A.IsHermitian) (x y : Fin K → ℝ) :
    (eU hA *ᵥ x) ⬝ᵥ (eU hA *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, mulVec_mulVec]
  have : (eU hA)ᵀ * eU hA = 1 := by
    have h := eU_star_mul hA
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [this, one_mulVec]

private lemma eU_decomp (hA : A.IsHermitian) :
    A = eU hA * diagonal hA.eigenvalues * star (eU hA) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [eU] using this

private lemma dot_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ w = ∑ j, (eC hA w j) ^ 2 := by
  conv_lhs => rw [← eU_mulVec_eC hA w]
  rw [eU_orth_dot]
  simp [dotProduct, sq]

private lemma quad_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ (A *ᵥ w) = ∑ j, hA.eigenvalues j * (eC hA w j) ^ 2 := by
  have h1 : A *ᵥ w = eU hA *ᵥ (diagonal hA.eigenvalues *ᵥ eC hA w) := by
    conv_lhs => rw [eU_decomp hA]
    unfold eC
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1]
  nth_rewrite 1 [← eU_mulVec_eC hA w]
  rw [eU_orth_dot]
  simp only [dotProduct, mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- On vectors whose eigencoordinates vanish at every eigenvalue `≥ E`, the form is `< E |w|²`
unless `w = 0`. -/
private lemma quad_lt_of_zero (hA : A.IsHermitian) {E : ℝ} {w : Fin K → ℝ} (hw : w ≠ 0)
    (hz : ∀ j, E ≤ hA.eigenvalues j → eC hA w j = 0) :
    w ⬝ᵥ (A *ᵥ w) < E * (w ⬝ᵥ w) := by
  have hne : ∃ j, eC hA w j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hw
    have : w ⬝ᵥ w = 0 := by rw [dot_eq_sum hA]; simp [hcon]
    exact dotProduct_self_eq_zero.mp this
  obtain ⟨j₀, hj₀⟩ := hne
  rw [quad_eq_sum hA, dot_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
  · by_cases hj : E ≤ hA.eigenvalues j
    · rw [hz j hj]; simp
    · exact mul_le_mul_of_nonneg_right (not_le.mp hj).le (sq_nonneg _)
  · have hj : ¬ E ≤ hA.eigenvalues j₀ := fun h => hj₀ (hz j₀ h)
    exact mul_lt_mul_of_pos_right (not_le.mp hj) (by positivity)

/-- On vectors whose eigencoordinates vanish at every eigenvalue `< E`, the form is `≥ E |w|²`. -/
private lemma le_quad_of_zero (hA : A.IsHermitian) {E : ℝ} {w : Fin K → ℝ}
    (hz : ∀ j, hA.eigenvalues j < E → eC hA w j = 0) :
    E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w) := by
  rw [quad_eq_sum hA, dot_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : hA.eigenvalues j < E
  · rw [hz j hj]; simp
  · exact mul_le_mul_of_nonneg_right (not_lt.mp hj) (sq_nonneg _)

/-- The linear map recording the eigencoordinates of `w` indexed by `s`. -/
private def cMap (hA : A.IsHermitian) (s : Finset (Fin K)) : (Fin K → ℝ) →ₗ[ℝ] (s → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : s → Fin K)) ∘ₗ Matrix.mulVecLin (star (eU hA))

private lemma mem_ker_cMap (hA : A.IsHermitian) (s : Finset (Fin K)) (w : Fin K → ℝ) :
    w ∈ LinearMap.ker (cMap hA s) ↔ ∀ j ∈ s, eC hA w j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 j.2

/-- The kernel of `cMap hA s` has dimension at least `K − |s|`. -/
private lemma le_finrank_ker_cMap (hA : A.IsHermitian) (s : Finset (Fin K)) :
    K ≤ Module.finrank ℝ (LinearMap.ker (cMap hA s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (cMap hA s)
  have h1 : Module.finrank ℝ (LinearMap.range (cMap hA s)) ≤ s.card := by
    calc Module.finrank ℝ (LinearMap.range (cMap hA s)) ≤ Module.finrank ℝ (s → ℝ) :=
          Submodule.finrank_le _
      _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℝ (Fin K → ℝ) = K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

/-- A subspace meeting the kernel of `cMap hA s` trivially has dimension at most `|s|`. -/
private lemma finrank_le_card_of_zero (hA : A.IsHermitian) (V : Submodule ℝ (Fin K → ℝ))
    (s : Finset (Fin K)) (h : ∀ w ∈ V, (∀ j ∈ s, eC hA w j = 0) → w = 0) :
    Module.finrank ℝ V ≤ s.card := by
  have hinj : Function.Injective ((cMap hA s) ∘ₗ V.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : x.1 ∈ LinearMap.ker (cMap hA s) := hx
    exact Subtype.ext (h x.1 x.2 ((mem_ker_cMap hA s x.1).mp hx'))
  calc Module.finrank ℝ V ≤ Module.finrank ℝ (s → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

private lemma eigCount_eq_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E = (Finset.univ.filter fun j => E ≤ hA.eigenvalues j).card := by
  unfold eigCount
  rw [specOf_eq hA]

private lemma eigCount_add_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E + (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j).card = K := by
  rw [eigCount_eq_card hA, Finset.card_filter_add_card_filter_not]
  simp

/-- Cauchy–Schwarz with the `L²` operator norm: `⟨w, M w⟩ ≤ ‖M‖ |w|²`. -/
private lemma quad_le_norm (M : Matrix (Fin K) (Fin K) ℝ) (w : Fin K → ℝ) :
    w ⬝ᵥ (M *ᵥ w) ≤ ‖M‖ * (w ⬝ᵥ w) := by
  set x : EuclideanSpace ℝ (Fin K) := WithLp.toLp 2 w with hx
  have h1 := Matrix.l2_opNorm_mulVec M x
  have h2 : ‖x‖ ^ 2 = w ⬝ᵥ w := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hx, dotProduct, sq]
  have h3 : w ⬝ᵥ (M *ᵥ w) ≤ ‖x‖ * ‖(EuclideanSpace.equiv (Fin K) ℝ).symm (M *ᵥ x)‖ := by
    have h := real_inner_le_norm x ((EuclideanSpace.equiv (Fin K) ℝ).symm (M *ᵥ x))
    have h' : inner ℝ x ((EuclideanSpace.equiv (Fin K) ℝ).symm (M *ᵥ x)) = w ⬝ᵥ (M *ᵥ w) := by
      simp [PiLp.inner_apply, dotProduct, hx, mul_comm]
    rwa [h'] at h
  calc w ⬝ᵥ (M *ᵥ w) ≤ ‖x‖ * ‖(EuclideanSpace.equiv (Fin K) ℝ).symm (M *ᵥ x)‖ := h3
    _ ≤ ‖x‖ * (‖M‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖M‖ * (w ⬝ᵥ w) := by rw [← h2]; ring

/-- The counting function is constant between two thresholds in a window without eigenvalues. -/
private lemma eigCount_eq_of_gap {l u x y : ℝ}
    (hgap : ∀ i, specOf A i ∉ Set.Icc l u) (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) :
    eigCount A x = eigCount A y := by
  have key : ∀ x y, x ∈ Set.Icc l u → y ∈ Set.Icc l u → x ≤ y → eigCount A x = eigCount A y := by
    intro x y hx hy hxy
    unfold eigCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra h'
      exact hgap i ⟨by linarith [hx.1], by linarith [hy.2, not_le.mp h']⟩
    · intro h
      exact hxy.trans h
  rcases le_total x y with h | h
  · exact key x y hx hy h
  · exact (key y x hy hx h).symm

end MinMaxAux

/-- Min–max, lower half: a subspace on which `⟨w, A w⟩ ≥ E |w|²` has dimension `≤ n_A(E)`. -/
theorem eigCount_ge_of_subspace {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    {E : ℝ} (V : Submodule ℝ (Fin K → ℝ)) (hV : ∀ w ∈ V, E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w)) :
    Module.finrank ℝ V ≤ eigCount A E := by
  rw [eigCount_eq_card hA]
  refine finrank_le_card_of_zero hA V _ fun w hw hz => ?_
  by_contra hw0
  have h1 := quad_lt_of_zero hA hw0 (fun j hj => hz j (by simpa using hj))
  have h2 := hV w hw
  linarith

/-- Min–max, upper half: a subspace on which `⟨w, A w⟩ < E |w|²` (`w ≠ 0`) has dimension
`≤ K − n_A(E)`. -/
theorem eigCount_le_of_subspace {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    {E : ℝ} (V : Submodule ℝ (Fin K → ℝ))
    (hV : ∀ w ∈ V, w ≠ 0 → w ⬝ᵥ (A *ᵥ w) < E * (w ⬝ᵥ w)) :
    eigCount A E + Module.finrank ℝ V ≤ K := by
  have h1 := finrank_le_card_of_zero hA V (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j) ?_
  · have := eigCount_add_card hA E
    omega
  · intro w hw hz
    by_contra hw0
    have h2 := hV w hw hw0
    have h3 := le_quad_of_zero hA (E := E) (w := w) (fun j hj => hz j (by simpa using hj))
    linarith

/-- Weyl's inequality in counting form: `n_A(E + δ) ≤ n_B(E)` if `‖A − B‖ ≤ δ`. -/
theorem eigCount_weyl {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {δ : ℝ} (h : ‖A - B‖ ≤ δ) (E : ℝ) :
    eigCount A (E + δ) ≤ eigCount B E := by
  set s := Finset.univ.filter fun j => ¬ E + δ ≤ hA.eigenvalues j with hs
  have h1 := le_finrank_ker_cMap hA s
  have h2 : eigCount A (E + δ) + s.card = K := eigCount_add_card hA (E + δ)
  have h3 : eigCount A (E + δ) ≤ Module.finrank ℝ (LinearMap.ker (cMap hA s)) := by omega
  refine h3.trans (eigCount_ge_of_subspace hB (LinearMap.ker (cMap hA s)) fun w hw => ?_)
  have hz : ∀ j, hA.eigenvalues j < E + δ → eC hA w j = 0 := fun j hj =>
    (mem_ker_cMap hA s w).mp hw j (by simp [hs, hj])
  have h4 := le_quad_of_zero hA hz
  have h5 := quad_le_norm (A - B) w
  have h6 : w ⬝ᵥ ((A - B) *ᵥ w) = w ⬝ᵥ (A *ᵥ w) - w ⬝ᵥ (B *ᵥ w) := by
    rw [sub_mulVec, dotProduct_sub]
  have hw0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h7 : ‖A - B‖ * (w ⬝ᵥ w) ≤ δ * (w ⬝ᵥ w) := mul_le_mul_of_nonneg_right h hw0
  have h8 : (E + δ) * (w ⬝ᵥ w) = E * (w ⬝ᵥ w) + δ * (w ⬝ᵥ w) := add_mul _ _ _
  linarith

/-- A perturbation of rank `r` raises the count by at most `r`. -/
theorem eigCount_le_add_rank {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (E : ℝ) : eigCount (A + B) E ≤ eigCount A E + B.rank := by
  have hAB : (A + B).IsHermitian := hA.add hB
  set s := Finset.univ.filter fun j => E ≤ hA.eigenvalues j with hs
  have h1 := le_finrank_ker_cMap hA s
  have h2 : K ≤ Module.finrank ℝ (LinearMap.ker B.mulVecLin) + B.rank := by
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    unfold Matrix.rank
    omega
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (cMap hA s))
    (LinearMap.ker B.mulVecLin)
  have h4 : Module.finrank ℝ ↥(LinearMap.ker (cMap hA s) ⊔ LinearMap.ker B.mulVecLin) ≤ K := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h5 := eigCount_le_of_subspace hAB (E := E)
    (LinearMap.ker (cMap hA s) ⊓ LinearMap.ker B.mulVecLin) (fun w hw hw0 => by
      obtain ⟨hw1, hw2⟩ := hw
      have hz : ∀ j, E ≤ hA.eigenvalues j → eC hA w j = 0 := fun j hj =>
        (mem_ker_cMap hA s w).mp hw1 j (by simp [hs, hj])
      have hBw : B *ᵥ w = 0 := hw2
      have h6 := quad_lt_of_zero hA hw0 hz
      rw [add_mulVec, dotProduct_add, hBw, dotProduct_zero, add_zero]
      exact h6)
  have h6 : s.card = eigCount A E := (eigCount_eq_card hA E).symm
  omega

/-- No eigenvalue is `≥ E` when `‖A‖ < E`. -/
theorem eigCount_eq_zero_of_norm_lt {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}
    (hA : A.IsHermitian) {E : ℝ} (h : ‖A‖ < E) : eigCount A E = 0 := by
  rw [eigCount_eq_card hA, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  set w := eU hA *ᵥ Pi.single j 1 with hw
  have hc : eC hA w = Pi.single j 1 := by
    unfold eC
    rw [hw, mulVec_mulVec, eU_star_mul, one_mulVec]
  have h1 : w ⬝ᵥ w = 1 := by
    rw [dot_eq_sum hA, hc]
    simp [Pi.single_apply]
  have h2 : w ⬝ᵥ (A *ᵥ w) = hA.eigenvalues j := by
    rw [quad_eq_sum hA, hc]
    simp [Pi.single_apply]
  have h3 := quad_le_norm A w
  rw [h1, h2] at h3
  linarith

/-- The continuity step of Lemmas 10.3 and 10.4 in counting form: along a chain `Q_0, …, Q_n` with
thresholds `θ_j`, if `‖Q_{j+1} − Q_j‖ + |θ_{j+1} − θ_j| < δ` and `Q_j` has no eigenvalue in
`[θ_j − δ, θ_j + δ]`, then `n_{Q_n}(θ_n) = n_{Q_0}(θ_0)`. -/
theorem eigCount_lattice {K : ℕ} (Q : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ j, (Q j).IsHermitian) (θ : ℕ → ℝ) {δ : ℝ} (n : ℕ)
    (hstep : ∀ j < n, ‖Q (j + 1) - Q j‖ + |θ (j + 1) - θ j| < δ)
    (hgap : ∀ j < n, ∀ i, specOf (Q j) i ∉ Set.Icc (θ j - δ) (θ j + δ)) :
    eigCount (Q n) (θ n) = eigCount (Q 0) (θ 0) := by
  have key : ∀ j, j ≤ n → eigCount (Q j) (θ j) = eigCount (Q 0) (θ 0) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      have ih' := ih hjn.le
      have hd : 0 ≤ ‖Q (j + 1) - Q j‖ := norm_nonneg _
      have he : 0 ≤ |θ (j + 1) - θ j| := abs_nonneg _
      have hs := hstep j hjn
      have hg := hgap j hjn
      have w1 := eigCount_weyl (hQ (j + 1)) (hQ j) (le_refl ‖Q (j + 1) - Q j‖)
        (θ (j + 1) - ‖Q (j + 1) - Q j‖)
      have w2 := eigCount_weyl (hQ j) (hQ (j + 1)) (δ := ‖Q (j + 1) - Q j‖)
        (by rw [norm_sub_rev]) (θ (j + 1))
      rw [sub_add_cancel] at w1
      have habs := abs_le.mp (le_refl |θ (j + 1) - θ j|)
      have ha : θ (j + 1) - ‖Q (j + 1) - Q j‖ ∈ Set.Icc (θ j - δ) (θ j + δ) :=
        ⟨by linarith [habs.1, habs.2], by linarith [habs.1, habs.2]⟩
      have hb : θ (j + 1) + ‖Q (j + 1) - Q j‖ ∈ Set.Icc (θ j - δ) (θ j + δ) :=
        ⟨by linarith [habs.1, habs.2], by linarith [habs.1, habs.2]⟩
      have hc : θ j ∈ Set.Icc (θ j - δ) (θ j + δ) := ⟨by linarith, by linarith⟩
      have e1 := eigCount_eq_of_gap hg ha hc
      have e2 := eigCount_eq_of_gap hg hb hc
      have : eigCount (Q (j + 1)) (θ (j + 1)) = eigCount (Q j) (θ j) := by omega
      rw [this, ih']
  exact key n le_rfl

section MinMaxExamples

/-- `A = diag(2, 0)`, `E = 1` (`n_A(1) = 1`): the line `ℝ e₀` has `⟨w, A w⟩ = 2 c² ≥ c²`, so its
dimension is `≤ n_A(1)`. -/
example : Module.finrank ℝ (Submodule.span ℝ {(Pi.single 0 1 : Fin 2 → ℝ)}) ≤
    eigCount (diagonal ![(2 : ℝ), 0]) 1 :=
  eigCount_ge_of_subspace (isHermitian_diagonal _) _ fun w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [dotProduct, Fin.isValue, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
      Pi.single_eq_same, mul_one, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      mul_zero, add_zero, one_mul, mulVec_diagonal, cons_val_zero, cons_val_one,
      cons_val_fin_one]
    nlinarith [sq_nonneg c]

/-- `A = diag(2, 0)`, `E = 1`: the line `ℝ e₁` has `⟨w, A w⟩ = 0 < c² = E |w|²` for `w ≠ 0`, so
`n_A(1) + dim ≤ K = 2`. -/
example : eigCount (diagonal ![(2 : ℝ), 0]) 1 +
    Module.finrank ℝ (Submodule.span ℝ {(Pi.single 1 1 : Fin 2 → ℝ)}) ≤ 2 :=
  eigCount_le_of_subspace (isHermitian_diagonal _) _ fun w hw hw0 => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hc : c ≠ 0 := fun h => hw0 (by simp [h])
    simp only [dotProduct, Fin.isValue, Pi.smul_apply, smul_eq_mul, mulVec_diagonal,
      Fin.sum_univ_two, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
      cons_val_zero, Pi.single_eq_same, mul_one, cons_val_one, cons_val_fin_one, zero_mul,
      add_zero, zero_add, one_mul, mul_self_pos]
    exact hc

end MinMaxExamples

end Anisotropic
