import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # `L±` are the extreme points of `supp ϱ^W`, and the interval-support form -/

/-- `S(w) = N⁻¹ ∑ᵢ |aᵢ − w|⁻²` on `ℂ`. -/
private def aux_S {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹

/-- `T(w) = N⁻¹ ∑ᵢ (aᵢ − w)⁻²`, so that `g′(w) = 1 − T(w)` for `g(w) = w − m_A(w)`. -/
private def aux_T {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i, (((a i : ℂ) - w) ^ 2)⁻¹

/-- `S(x + iy) = N⁻¹ ∑ᵢ ((aᵢ − x)² + y²)⁻¹`. -/
private def aux_F {N : ℕ} (a : Fin N → ℝ) (x y : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2 + y ^ 2)⁻¹

private lemma aux_S_eq {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : aux_S a w = aux_F a w.re w.im := by
  unfold aux_S aux_F
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

private lemma aux_F_zero {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : aux_F a x 0 = sW a x := by
  simp [aux_F, sW]

private lemma aux_Npos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  exact inv_pos.2 this

private lemma aux_le_iSup {N : ℕ} (a : Fin N → ℝ) (i : Fin N) : a i ≤ ⨆ j, a j :=
  le_ciSup (Finite.bddAbove_range a) i

private lemma aux_ne_of_gt {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : (⨆ j, a j) < w.re)
    (i : Fin N) : (a i : ℂ) - w ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  rw [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h1
  linarith [aux_le_iSup a i]

/-- `Im m_A(w) = Im w · S(w)`. -/
private lemma aux_im_stieltjesA {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    (stieltjesA a w).im = w.im * aux_S a w := by
  unfold stieltjesA aux_S
  have hc : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have ht : ∀ i, (((a i : ℂ) - w)⁻¹).im = w.im * (Complex.normSq ((a i : ℂ) - w))⁻¹ := by
    intro i
    rw [Complex.inv_im]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    ring
  rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

private lemma aux_S_pos {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im) :
    0 < aux_S a w := by
  unfold aux_S
  refine mul_pos (aux_Npos hN) ?_
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  refine Finset.sum_pos (fun i _ => inv_pos.2 (Complex.normSq_pos.2 ?_)) hne
  intro h
  have h1 := congrArg Complex.im h
  rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at h1
  linarith

/-- `Re T(w) < S(w)` off the real axis. -/
private lemma aux_re_T_lt {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    (aux_T a w).re < aux_S a w := by
  unfold aux_T aux_S
  have hc : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hc, Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_lt_mul_of_pos_left ?_ (aux_Npos hN)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
  set p := a i - w.re
  set q := w.im
  have hq : 0 < q ^ 2 := by positivity
  have hD : 0 < p ^ 2 + q ^ 2 := by positivity
  have h1 : Complex.normSq ((a i : ℂ) - w) = p ^ 2 + q ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, p, q]
    ring
  have h2 : ((((a i : ℂ) - w) ^ 2)⁻¹).re = (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) ^ 2 := by
    rw [Complex.inv_re, map_pow, h1]
    congr 1
    rw [pow_two, Complex.mul_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, p, q]
    ring
  rw [h2, h1, div_lt_iff₀ (by positivity)]
  rw [pow_two (p ^ 2 + q ^ 2), ← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  linarith

/-- `w ↦ w − m_A(w)` has strict derivative `1 − T(w)` off the spectrum. -/
private lemma aux_hasStrictDerivAt {N : ℕ} (a : Fin N → ℝ) {w : ℂ}
    (hw : ∀ i, (a i : ℂ) - w ≠ 0) :
    HasStrictDerivAt (fun x => x - stieltjesA a x) (1 - aux_T a w) w := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasStrictDerivAt (fun y => ((a i : ℂ) - y)⁻¹) ((((a i : ℂ) - w) ^ 2)⁻¹) w := by
    intro i _
    have h1 := (hasStrictDerivAt_inv (hw i)).comp w ((hasStrictDerivAt_id w).const_sub (a i : ℂ))
    convert h1 using 1
    · rfl
    · ring
  have hs := (HasStrictDerivAt.sum h).const_mul ((N : ℂ)⁻¹)
  have hA : HasStrictDerivAt (stieltjesA a) (aux_T a w) w := by
    unfold stieltjesA aux_T
    convert hs using 1
    funext y
    simp [Finset.sum_apply]
  exact (hasStrictDerivAt_id w).sub hA

/-- `ϱ^W(E) = Im w₀/π` when `g(w₀) = E` and a local inverse of `g` near `E` maps `ℂ₊` into
`ℂ₊`: then `m^W = φ − id` on `ℂ₊` near `E` by uniqueness of `m^W`. -/
private lemma aux_rhoW_of_inv {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {E : ℝ} {w₀ : ℂ}
    {φ : ℂ → ℂ} (hc : Tendsto φ (𝓝 (E : ℂ)) (𝓝 w₀))
    (hinv : ∀ᶠ z in 𝓝 (E : ℂ), φ z - stieltjesA a (φ z) = z)
    (hpos : ∀ᶠ z in 𝓝 (E : ℂ), 0 < z.im → 0 < (φ z).im) :
    rhoW a E = w₀.im / Real.pi := by
  set γ : ℝ → ℂ := fun η => (E : ℂ) + (η : ℂ) * Complex.I with hγdef
  have hγ : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (E : ℂ)) := by
    have hcont : Continuous γ := by fun_prop
    have h := hcont.tendsto 0
    simp only [γ, Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hγeq : ∀ η : ℝ, (⟨E, η⟩ : ℂ) = γ η := fun η => by
    apply Complex.ext <;> simp [γ]
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (φ (γ η) - γ η).im / Real.pi = (mW a ⟨E, η⟩).im / Real.pi := by
    filter_upwards [hγ.eventually (hinv.and hpos), self_mem_nhdsWithin] with η hη hη0
    obtain ⟨h1, h2⟩ := hη
    have hη' : 0 < (γ η).im := by simpa [γ] using hη0
    have hφ : 0 < (φ (γ η)).im := h2 hη'
    have hm : φ (γ η) - γ η = stieltjesA a (φ (γ η)) := by linear_combination h1
    rw [hγeq]
    congr 2
    symm
    apply mW_eq_of_spec hN a hη'
    · rw [hm, aux_im_stieltjesA]
      exact mul_pos hφ (aux_S_pos hN a hφ)
    · rw [show γ η + (φ (γ η) - γ η) = φ (γ η) by ring]
      exact hm
  have hlim : Tendsto (fun η => (φ (γ η) - γ η).im / Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (w₀.im / Real.pi)) := by
    have h := (Complex.continuous_im.tendsto _).comp ((hc.comp hγ).sub hγ)
    have h3 := h.div_const Real.pi
    simpa using h3
  unfold rhoW
  exact (hlim.congr' hev).limUnder_eq

/-- `ϱ^W(E) = Im w₀/π` at `E = g(w₀)` when `g′(w₀) ≠ 0` and either `Im w₀ > 0`, or `S < 1` near
`w₀` (then `Im g(w) = Im w · (1 − S(w))` forces `Im w > 0` on the preimage of `ℂ₊`). -/
private lemma aux_rhoW_of_strict {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {E : ℝ} {w₀ d : ℂ}
    (hf : HasStrictDerivAt (fun w => w - stieltjesA a w) d w₀) (hd : d ≠ 0)
    (hfE : w₀ - stieltjesA a w₀ = (E : ℂ))
    (hcase : 0 < w₀.im ∨ (aux_S a w₀ < 1 ∧ ContinuousAt (aux_S a) w₀)) :
    rhoW a E = w₀.im / Real.pi := by
  set φ := hf.localInverse _ d w₀ hd
  have hleft : φ (w₀ - stieltjesA a w₀) = w₀ := (hf.eventually_left_inverse hd).self_of_nhds
  have hc0 : Tendsto φ (𝓝 (w₀ - stieltjesA a w₀)) (𝓝 w₀) := by
    have h1 : Tendsto φ (𝓝 (w₀ - stieltjesA a w₀)) (𝓝 (φ (w₀ - stieltjesA a w₀))) :=
      (hf.to_localInverse hd).hasDerivAt.continuousAt.tendsto
    rw [hleft] at h1
    exact h1
  rw [hfE] at hc0
  have hinv : ∀ᶠ z in 𝓝 (E : ℂ), φ z - stieltjesA a (φ z) = z := by
    have h1 := hf.eventually_right_inverse hd
    rw [hfE] at h1
    exact h1
  apply aux_rhoW_of_inv hN a hc0 hinv
  rcases hcase with hw | ⟨hS, hSc⟩
  · have h1 : ∀ᶠ z in 𝓝 (E : ℂ), 0 < (φ z).im :=
      ((Complex.continuous_im.tendsto w₀).comp hc0).eventually (lt_mem_nhds hw)
    filter_upwards [h1] with z hz _ using hz
  · have h1 : ∀ᶠ z in 𝓝 (E : ℂ), aux_S a (φ z) < 1 :=
      (hSc.tendsto.comp hc0).eventually (gt_mem_nhds hS)
    filter_upwards [h1, hinv] with z hz hzi hzpos
    have him := congrArg Complex.im hzi
    rw [Complex.sub_im, aux_im_stieltjesA] at him
    by_contra hle
    push Not at hle
    nlinarith

private lemma aux_sW_lt {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {x y : ℝ}
    (hx : (⨆ j, a j) < x) (hxy : x < y) : sW a y < sW a x := by
  unfold sW
  refine mul_lt_mul_of_pos_left ?_ (aux_Npos hN)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
  have h1 : 0 < x - a i := by linarith [aux_le_iSup a i]
  have h2 : 0 < y - a i := by linarith
  rw [inv_lt_inv₀ (by nlinarith) (by nlinarith)]
  nlinarith

private lemma aux_sW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : (⨆ j, a j) < x) :
    ContinuousAt (sW a) x := by
  have h : ∀ i, (a i - x) ^ 2 ≠ 0 := fun i => by
    have : a i - x < 0 := by linarith [aux_le_iSup a i]
    exact pow_ne_zero 2 this.ne
  show ContinuousAt (fun x => (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹) x
  fun_prop (disch := exact h _)

private lemma aux_gW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : (⨆ j, a j) < x) :
    ContinuousAt (gW a) x := by
  have h : ∀ i, a i - x ≠ 0 := fun i => by
    have : a i - x < 0 := by linarith [aux_le_iSup a i]
    exact this.ne
  show ContinuousAt (fun x => x - (N : ℝ)⁻¹ * ∑ i, (a i - x)⁻¹) x
  fun_prop (disch := exact h _)

private lemma aux_gW_ge {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : (⨆ j, a j) < x) :
    x ≤ gW a x := by
  unfold gW
  have h1 : ∑ i, (a i - x)⁻¹ ≤ 0 :=
    Finset.sum_nonpos fun i _ => inv_nonpos.2 (by linarith [aux_le_iSup a i])
  have h2 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  nlinarith

/-- `x₊ > maxᵢ aᵢ`, `S(x₊) ≤ 1`, and `S > 1` on `(maxᵢ aᵢ, x₊)`. -/
private lemma aux_xpW {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    (⨆ j, a j) < xpW a ∧ sW a (xpW a) ≤ 1 ∧
      ∀ x, (⨆ j, a j) < x → x < xpW a → 1 < sW a x := by
  set α := ⨆ j, a j with hα
  set T := {x | α < x ∧ sW a x ≤ 1} with hT
  have hx : xpW a = sInf T := rfl
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hne : T.Nonempty := by
    refine ⟨α + 1, by linarith, ?_⟩
    unfold sW
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin N)), ((a i - (α + 1)) ^ 2)⁻¹ ≤ 1 := by
      intro i _
      have h1 : 1 ≤ α + 1 - a i := by linarith [aux_le_iSup a i]
      apply inv_le_one_of_one_le₀
      nlinarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
    calc (N : ℝ)⁻¹ * ∑ i, ((a i - (α + 1)) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ * N :=
          mul_le_mul_of_nonneg_left h2 (aux_Npos hN).le
      _ = 1 := inv_mul_cancel₀ hNr.ne'
  have hbdd : BddBelow T := ⟨α, fun x hx => hx.1.le⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i = α := exists_eq_ciSup_of_finite
  have hlow : ∀ x ∈ T, α + (N : ℝ)⁻¹ ≤ x := by
    rintro x ⟨hxα, hxS⟩
    by_contra hlt
    push Not at hlt
    have hterm : (N : ℝ)⁻¹ * ((a i₀ - x) ^ 2)⁻¹ ≤ sW a x := by
      unfold sW
      refine mul_le_mul_of_nonneg_left ?_ (aux_Npos hN).le
      exact Finset.single_le_sum (f := fun i => ((a i - x) ^ 2)⁻¹)
        (fun i _ => by positivity) (Finset.mem_univ i₀)
    rw [hi₀] at hterm
    have hu : 0 < x - α := by linarith
    have hNi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
    have h3 : 0 < (α - x) ^ 2 := by nlinarith
    have h1 : (α - x) ^ 2 < (N : ℝ)⁻¹ := by nlinarith [aux_Npos hN]
    have h4 : (N : ℝ) < ((α - x) ^ 2)⁻¹ := by
      rw [lt_inv_comm₀ hNr h3]
      exact h1
    have h5 : 1 < (N : ℝ)⁻¹ * ((α - x) ^ 2)⁻¹ := by
      calc (1 : ℝ) = (N : ℝ)⁻¹ * N := (inv_mul_cancel₀ hNr.ne').symm
        _ < _ := mul_lt_mul_of_pos_left h4 (aux_Npos hN)
    linarith
  have hge : α + (N : ℝ)⁻¹ ≤ xpW a := by rw [hx]; exact le_csInf hne hlow
  have hgt : α < xpW a := by linarith [aux_Npos hN]
  have hbelow : ∀ x, α < x → x < xpW a → 1 < sW a x := by
    intro x hx1 hx2
    by_contra h
    push Not at h
    have := csInf_le hbdd ⟨hx1, h⟩
    rw [← hx] at this
    linarith
  refine ⟨hgt, ?_, hbelow⟩
  by_contra h
  push Not at h
  have hev : ∀ᶠ x in 𝓝 (xpW a), 1 < sW a x :=
    (aux_sW_continuousAt a hgt).eventually (lt_mem_nhds h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨x, hxT, hxlt⟩ := exists_lt_of_csInf_lt hne (show sInf T < sInf T + ε by linarith)
  have hle : sInf T ≤ x := csInf_le hbdd hxT
  have h1 := @hball x (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  linarith [hxT.2]

private lemma aux_iSup_lt_LpW {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) : (⨆ j, a j) < LpW a := by
  have h := (aux_xpW hN a).1
  exact lt_of_lt_of_le h (aux_gW_ge a h)

private lemma aux_f_ofReal {N : ℕ} (a : Fin N → ℝ) (x : ℝ) :
    (x : ℂ) - stieltjesA a x = (gW a x : ℂ) := by
  unfold gW stieltjesA
  push_cast
  ring

/-- `ϱ^W = 0` on `(L₊, ∞)`. -/
private lemma aux_rhoW_right {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {E : ℝ} (hE : LpW a < E) :
    rhoW a E = 0 := by
  obtain ⟨hα, hS, -⟩ := aux_xpW hN a
  have hLp : LpW a = gW a (xpW a) := rfl
  have hxpE : xpW a < E := lt_of_le_of_lt (aux_gW_ge a hα) (hLp ▸ hE)
  have hcont : ContinuousOn (gW a) (Set.Icc (xpW a) E) := fun x hx =>
    (aux_gW_continuousAt a (by linarith [hx.1])).continuousWithinAt
  obtain ⟨xE, hxE, hgxE⟩ :=
    intermediate_value_Icc hxpE.le hcont ⟨(hLp ▸ hE).le, aux_gW_ge a (by linarith)⟩
  have hxE' : xpW a < xE := lt_of_le_of_ne hxE.1 (by
    rintro rfl
    rw [← hLp] at hgxE
    linarith)
  have hαE : (⨆ j, a j) < xE := by linarith
  have hSE : sW a xE < 1 := lt_of_lt_of_le (aux_sW_lt hN a hα hxE') hS
  have hne : ∀ i, (a i : ℂ) - (xE : ℂ) ≠ 0 := aux_ne_of_gt a (by simpa using hαE)
  have hf := aux_hasStrictDerivAt a hne
  have hT : aux_T a xE = ((sW a xE : ℝ) : ℂ) := by
    unfold aux_T sW
    push_cast
    rfl
  have hd : 1 - aux_T a xE ≠ 0 := by
    rw [hT]
    intro h
    have h1 := congrArg Complex.re h
    simp at h1
    linarith
  have hfE : (xE : ℂ) - stieltjesA a xE = (E : ℂ) := by rw [aux_f_ofReal, hgxE]
  have hSc : aux_S a xE < 1 := by
    rw [aux_S_eq]
    simpa [aux_F_zero] using hSE
  have hScont : ContinuousAt (aux_S a) (xE : ℂ) := by
    have h : ∀ i, (Complex.normSq ((a i : ℂ) - (xE : ℂ))) ≠ 0 := fun i =>
      (Complex.normSq_pos.2 (hne i)).ne'
    show ContinuousAt (fun w => (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹) _
    fun_prop (disch := exact h _)
  rw [aux_rhoW_of_strict hN a hf hd hfE (Or.inr ⟨hSc, hScont⟩)]
  simp

/-- `ϱ^W(E) = Im w₀/π > 0` at `E = g(w₀)` when `Im w₀ > 0` and `S(w₀) = 1`. -/
private lemma aux_rhoW_of_S_one {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w₀ : ℂ}
    (hw : 0 < w₀.im) (hS : aux_S a w₀ = 1) :
    w₀ - stieltjesA a w₀ = (((w₀ - stieltjesA a w₀).re : ℝ) : ℂ) ∧
      rhoW a (w₀ - stieltjesA a w₀).re = w₀.im / Real.pi := by
  have hne : ∀ i, (a i : ℂ) - w₀ ≠ 0 := fun i h => by
    have h1 := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at h1
    linarith
  have hfim : (w₀ - stieltjesA a w₀).im = 0 := by
    rw [Complex.sub_im, aux_im_stieltjesA, hS]
    ring
  have hfE : w₀ - stieltjesA a w₀ = (((w₀ - stieltjesA a w₀).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by rw [hfim]; simp)
  have hf := aux_hasStrictDerivAt a hne
  have hd : 1 - aux_T a w₀ ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have hlt := aux_re_T_lt hN a (w := w₀) hw.ne'
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h1
    rw [hS] at hlt
    linarith
  exact ⟨hfE, aux_rhoW_of_strict hN a hf hd hfE (Or.inl hw)⟩

/-- `L₊ ∈ supp ϱ^W`: points `w₀ = x + iy` with `x ↑ x₊`, `y > 0` and `S(w₀) = 1` have
`g(w₀) → L₊` real, and `ϱ^W(g(w₀)) = Im w₀/π > 0`. -/
private lemma aux_LpW_mem {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    LpW a ∈ tsupport (rhoW a) := by
  obtain ⟨hα, hS, hbelow⟩ := aux_xpW hN a
  set α := ⨆ j, a j with hαdef
  set xp := xpW a with hxpdef
  have hnep : ∀ i, (a i : ℂ) - (xp : ℂ) ≠ 0 := aux_ne_of_gt a (by simpa using hα)
  have hfc : ContinuousAt (fun w => w - stieltjesA a w) (xp : ℂ) :=
    (aux_hasStrictDerivAt a hnep).hasDerivAt.continuousAt
  have hfxp : (xp : ℂ) - stieltjesA a xp = (LpW a : ℂ) := aux_f_ofReal a xp
  show LpW a ∈ closure (Function.support (rhoW a))
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1 hfc δ hδ
  set y₀ := r / 2 with hy₀def
  have hy₀ : 0 < y₀ := by positivity
  have hden : ∀ (x y : ℝ), α < x → ∀ i, (a i - x) ^ 2 + y ^ 2 ≠ 0 := by
    intro x y hx i
    have : a i - x < 0 := by linarith [aux_le_iSup a i]
    exact (add_pos_of_pos_of_nonneg (by nlinarith) (sq_nonneg y)).ne'
  have hS1 : aux_F a xp y₀ < 1 := by
    refine lt_of_lt_of_le ?_ hS
    rw [← aux_F_zero]
    unfold aux_F
    refine mul_lt_mul_of_pos_left ?_ (aux_Npos hN)
    have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
      Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
    refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
    have h1 : a i - xp < 0 := by linarith [aux_le_iSup a i]
    rw [inv_lt_inv₀ (add_pos_of_pos_of_nonneg (by nlinarith) (sq_nonneg _)) (by nlinarith)]
    nlinarith
  have hcx : ContinuousAt (fun x : ℝ => aux_F a x y₀) xp := by
    have h : ∀ i, (a i - xp) ^ 2 + y₀ ^ 2 ≠ 0 := hden xp y₀ hα
    show ContinuousAt (fun x => (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2 + y₀ ^ 2)⁻¹) xp
    fun_prop (disch := exact h _)
  obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.1 hcx _ (sub_pos.2 hS1)
  set t := min (min ε (r / 2)) (xp - α) / 2 with htdef
  have ht : 0 < t := by
    have : 0 < min (min ε (r / 2)) (xp - α) := lt_min (lt_min hε (by positivity)) (by linarith)
    positivity
  have ht1 : t < ε := by
    have := min_le_left (min ε (r / 2)) (xp - α)
    have := min_le_left ε (r / 2)
    linarith
  have ht2 : t < r / 2 := by
    have := min_le_left (min ε (r / 2)) (xp - α)
    have := min_le_right ε (r / 2)
    linarith
  have ht3 : t < xp - α := by
    have := min_le_right (min ε (r / 2)) (xp - α)
    linarith
  set x := xp - t with hxdef
  have hxα : α < x := by linarith
  have hSx : 1 < aux_F a x 0 := by rw [aux_F_zero]; exact hbelow x hxα (by linarith)
  have hSxy0 : aux_F a x y₀ < 1 := by
    have h1 := @hε' x (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2]
  have hcy : ContinuousOn (fun y : ℝ => aux_F a x y) (Set.Icc 0 y₀) := by
    have h : ∀ y i, (a i - x) ^ 2 + y ^ 2 ≠ 0 := fun y => hden x y hxα
    have : Continuous (fun y : ℝ => (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2 + y ^ 2)⁻¹) := by
      fun_prop (disch := (intro y; exact h y _))
    exact this.continuousOn
  obtain ⟨y₁, hy₁, hSy₁⟩ := intermediate_value_Icc' hy₀.le hcy ⟨hSxy0.le, hSx.le⟩
  have hy₁pos : 0 < y₁ := lt_of_le_of_ne hy₁.1 (by
    rintro rfl
    linarith)
  set w₀ : ℂ := (x : ℂ) + (y₁ : ℂ) * Complex.I with hw₀def
  have hw₀im : w₀.im = y₁ := by simp [w₀]
  have hw₀re : w₀.re = x := by simp [w₀]
  have hSw : aux_S a w₀ = 1 := by rw [aux_S_eq, hw₀re, hw₀im]; exact hSy₁
  obtain ⟨hfE, hrho⟩ := aux_rhoW_of_S_one hN a (by rw [hw₀im]; exact hy₁pos) hSw
  refine ⟨(w₀ - stieltjesA a w₀).re, ?_, ?_⟩
  · rw [Function.mem_support, hrho, hw₀im]
    exact (div_pos hy₁pos Real.pi_pos).ne'
  · have hw : dist w₀ (xp : ℂ) < r := by
      rw [Complex.dist_eq]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      have e1 : (w₀ - (xp : ℂ)).re = -t := by simp [w₀, x]
      have e2 : (w₀ - (xp : ℂ)).im = y₁ := by simp [w₀]
      rw [e1, e2, abs_neg, abs_of_pos ht, abs_of_pos hy₁pos]
      linarith [hy₁.2]
    have h1 := hball hw
    rw [hfxp, hfE, Complex.isometry_ofReal.dist_eq] at h1
    rw [dist_comm]
    exact h1

/-- Reflection: `ϱ^W_{−a}(−E) = ϱ^W_a(E)`. -/
private lemma aux_rhoW_neg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) (E : ℝ) :
    rhoW (-a) (-E) = rhoW a E := by
  unfold rhoW Filter.limUnder
  congr 1
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hz : 0 < (⟨E, η⟩ : ℂ).im := hη
  have h := mW_neg hN a hz
  have e : -(starRingEnd ℂ) (⟨E, η⟩ : ℂ) = ⟨-E, η⟩ := by apply Complex.ext <;> simp
  rw [e] at h
  rw [h]
  simp

/-- Definition 12.3: `L₋ < L₊` are the least and the greatest point of the support of `ϱ^W`,
for every spectrum `a` (no interval-support assumption). -/
theorem tsupport_rhoW_extreme {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    LmW a < LpW a ∧ tsupport (rhoW a) ⊆ Set.Icc (LmW a) (LpW a) ∧
      LmW a ∈ tsupport (rhoW a) ∧ LpW a ∈ tsupport (rhoW a) := by
  have hLm : LmW a = -LpW (-a) := LmW_neg a
  have hR : ∀ E, LpW (-a) < E → rhoW (-a) E = 0 := fun E hE => aux_rhoW_right hN (-a) hE
  refine ⟨?_, ?_, ?_, aux_LpW_mem hN a⟩
  · have i₀ : Fin N := ⟨0, hN⟩
    have h1 : -a i₀ ≤ ⨆ j, (-a) j := aux_le_iSup (-a) i₀
    have h2 := aux_iSup_lt_LpW hN (-a)
    have h3 := aux_le_iSup a i₀
    have h4 := aux_iSup_lt_LpW hN a
    rw [hLm]
    linarith
  · refine closure_minimal ?_ isClosed_Icc
    intro E hE
    rw [Function.mem_support] at hE
    constructor
    · by_contra h
      push Not at h
      apply hE
      rw [← aux_rhoW_neg hN a E]
      exact hR (-E) (by rw [hLm] at h; linarith)
    · by_contra h
      push Not at h
      exact hE (aux_rhoW_right hN a h)
  · have h3 := aux_LpW_mem hN (-a)
    rw [hLm]
    change -LpW (-a) ∈ closure (Function.support (rhoW a))
    change LpW (-a) ∈ closure (Function.support (rhoW (-a))) at h3
    rw [Metric.mem_closure_iff] at h3 ⊢
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := h3 ε hε
    refine ⟨-b, ?_, ?_⟩
    · rw [Function.mem_support, ← aux_rhoW_neg hN a, neg_neg]
      exact hb
    · rw [dist_neg_neg]
      exact hdist

/-- Under the interval-support condition of §12.1 the interval is `[L₋, L₊]`. -/
theorem intervalSupportW_eq {N : ℕ} (hN : 1 ≤ N) {a : Fin N → ℝ} {Lm Lp : ℝ}
    (h : IntervalSupportW a Lm Lp) : Lm = LmW a ∧ Lp = LpW a := by
  obtain ⟨hlt, hsub, hm, hp⟩ := tsupport_rhoW_extreme hN a
  obtain ⟨hLL, heq⟩ := h
  rw [heq] at hsub hm hp
  have h1 : Lm ∈ tsupport (rhoW a) := by rw [heq]; exact ⟨le_rfl, hLL.le⟩
  have h2 : Lp ∈ tsupport (rhoW a) := by rw [heq]; exact ⟨hLL.le, le_rfl⟩
  have h1' := (tsupport_rhoW_extreme hN a).2.1 h1
  have h2' := (tsupport_rhoW_extreme hN a).2.1 h2
  exact ⟨le_antisymm hm.1 h1'.1, le_antisymm h2'.2 hp.2⟩

#print axioms Anisotropic.tsupport_rhoW_extreme
#print axioms Anisotropic.intervalSupportW_eq

end Anisotropic
