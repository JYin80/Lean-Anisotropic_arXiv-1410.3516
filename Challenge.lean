module

public import Mathlib

@[expose] public section

/-!
# Anisotropic local laws for random matrices

Statements of the main results of A. Knowles and J. Yin, *Anisotropic local laws for random
matrices*, arXiv:1410.3516, with the definitions they use. This file imports Mathlib and nothing
else; the proofs are in the library `Anisotropic`, and `Solution.lean` connects each statement to
the theorem of the library that proves it. All results are for real matrices and real vectors,
at fixed `N ≥ N₀` with explicit constants. `docs/PAPER-VS-LEAN.md` reads every statement and lists
every difference from the printed one. Corollary 3.19 (Tracy–Widom) is not stated here: in the
library it takes the Tracy–Widom theory of the Gaussian case as hypotheses.
-/

section
open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal
noncomputable section
namespace Anisotropic
section Model
variable {Ω : Type*} [MeasureSpace Ω]
/-- The entry conditions of Assumption 2.1 for a random `K × N` matrix `X`:
measurability, independence of all entries, (cond on entries of X) and
(moments of X-1) for all `p`, the latter with the integrability of `|√N X_{iμ}|^p`. -/
structure EntryAssumption (C : ℕ → ℝ) {K N : ℕ} (X : Ω → Matrix (Fin K) (Fin N) ℝ) :
    Prop where
  measurable : ∀ i μ, Measurable fun ω => X ω i μ
  indep : iIndepFun (fun (p : Fin K × Fin N) (ω : Ω) => X ω p.1 p.2) ℙ
  mean : ∀ i μ, ∫ ω, X ω i μ = 0
  var : ∀ i μ, ∫ ω, X ω i μ ^ 2 = 1 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i μ, Integrable fun ω => |Real.sqrt N * X ω i μ| ^ p
  moment : ∀ (p : ℕ) i μ, ∫ ω, |Real.sqrt N * X ω i μ| ^ p ≤ C p

/-- The conditions of Assumption 2.1 on `Σ` under (T_diag): `Σ > 0`, (bound_Sigma)
`σ₁ ≤ τ⁻¹` for every eigenvalue, and (Sigma_gap) `π([0,τ]) ≤ 1 - τ`, where
`π = M⁻¹ ∑ᵢ δ_{σᵢ}` (def_pi), so that `M π([0,τ])` is the number of eigenvalues
in `[0,τ]` counted with multiplicity. -/
structure SigmaAssumption (τ : ℝ) {M : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) : Prop where
  posDef : Sig.PosDef
  eigenvalues_le : ∀ i, posDef.isHermitian.eigenvalues i ≤ τ⁻¹
  gap : ({i | posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M

/-- Assumption 2.1 under (T_diag): (phi_bounded) `τ ≤ M/N ≤ τ⁻¹`, the entry conditions
on `X`, and the conditions on `Σ`. -/
structure IsModel (τ : ℝ) (C : ℕ → ℝ) (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) : Prop where
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  entries : EntryAssumption C X
  sigma : SigmaAssumption τ Sig
end Model
/-- The extension `Σ̲ = diag(Σ, 1)` of (def_ul_Sigma), as a complex `𝓘 × 𝓘` matrix. -/
def ulSigma {M : ℕ} (N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (Sig.map (algebraMap ℝ ℂ)) 0 0 1

/-- The spectral domain `𝐃(τ,N)` of (def_D). -/
def specDomain (τ : ℝ) (N : ℕ) : Set ℂ :=
  {z | 0 < z.im ∧ τ ≤ ‖z‖ ∧ |z.re| ≤ τ⁻¹ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ τ⁻¹}
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal
noncomputable section
namespace Anisotropic
section Dom
variable {Ω : Type*} [MeasureSpace Ω]
/-- Definition 3.4 (i) at fixed `N`, `ε`, `D`: `P(ξ > N^ε ζ) ≤ N^{-D}`. -/
def DomAt (N : ℕ) (ε D : ℝ) (ξ ζ : Ω → ℝ) : Prop :=
  ℙ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- Definition 3.4 (ii) at fixed `N`: `ξ = O_≺(ζ)` for a complex `ξ` means `|ξ| ≺ ζ`. -/
def ODomAt (N : ℕ) (ε D : ℝ) (ξ : Ω → ℂ) (ζ : Ω → ℝ) : Prop :=
  DomAt N ε D (fun ω => ‖ξ ω‖) ζ

/-- The bilinear form `⟨v, A w⟩ = ∑_{s,t} v_s A_{st} w_t` for real test vectors. -/
def testBilin {ι : Type*} [Fintype ι] (v : ι → ℝ) (A : Matrix ι ι ℂ) (w : ι → ℝ) : ℂ :=
  (fun s => (v s : ℂ)) ⬝ᵥ (A *ᵥ fun t => (w t : ℂ))

/-- The Euclidean norm `|v|` of a real test vector. -/
def testNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ s, v s ^ 2)

/-- Definition 3.4 (iii) at fixed `N`: `A = O_≺(ζ)` in the weak operator sense, i.e.
`|⟨v, A w⟩| ≺ ζ |v| |w|` for all deterministic `v`, `w`. -/
def ODomMatAt {ι : Type*} [Fintype ι] (N : ℕ) (ε D : ℝ) (A : Ω → Matrix ι ι ℂ)
    (ζ : Ω → ℝ) : Prop :=
  ∀ v w : ι → ℝ,
    DomAt N ε D (fun ω => ‖testBilin v (A ω) w‖) (fun ω => ζ ω * testNorm v * testNorm w)

/-- Definition 4.7 at fixed `N`, `D`: `P(Ξᶜ) ≤ N^{-D}`. -/
def HighProbAt (N : ℕ) (D : ℝ) (A : Set Ω) : Prop :=
  ℙ Aᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))
end Dom
end Anisotropic
end
end
section
open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum
/-- Complexification of a real matrix. -/
noncomputable abbrev cplx {p q : Type*} (A : Matrix p q ℝ) : Matrix p q ℂ := A.map (algebraMap ℝ ℂ)

/-- `fromBlocks (-A) X Xᵀ (-z)`; `H(z)` of Definition 4.2 is the case `A = Σ⁻¹`. -/
noncomputable def linH (A : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (-cplx A) (cplx X) (cplx Xᵀ) (-(z • (1 : Matrix n n ℂ)))
open scoped Matrix.Norms.L2Operator
open Sum
/-- Inverse of `linH A X z` (precision form; minors are of this form). -/
noncomputable def GA (A : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := (linH A X z)⁻¹

/-- `G(z) = H(z)⁻¹`, Definition 4.2 and (def_G). -/
noncomputable def G (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := GA Sig⁻¹ X z

def SigU (Sig : Matrix m m ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks Sig 0 0 1
end Anisotropic
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- The distinct nonzero values `s_1 > ⋯ > s_n` of `σ` (as a finset, for `σ ≥ 0`). -/
def posVals (σ : Fin M → ℝ) : Finset ℝ :=
  (Finset.univ.image σ).filter (fun s => 0 < s)

/-- The weight `r_s = φ π({s}) = #{i | σ i = s} / N` (Appendix A). -/
def weight (N : ℕ) (σ : Fin M → ℝ) (s : ℝ) : ℝ :=
  ((Finset.univ.filter fun i => σ i = s).card : ℝ) / N

/-- `R = φ π((0,∞)) = #{i | 0 < σ i} / N`. -/
def massRatio (N : ℕ) (σ : Fin M → ℝ) : ℝ :=
  ((Finset.univ.filter fun i => 0 < σ i).card : ℝ) / N

/-- The upper half-plane `ℂ₊` as a set. -/
def upperHalf : Set ℂ := {z | 0 < z.im}

/-- The function `f` of (def_fx), `f(w) = -1/w + N⁻¹ Σ_i σ_i / (1 + σ_i w)`. -/
def fC (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  -w⁻¹ + ∑ i, (σ i : ℂ) / (N * (1 + σ i * w))

/-- The restriction of `f` to the real line. -/
def fR (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  -x⁻¹ + ∑ i, σ i / (N * (1 + σ i * x))

/-- `f''` on `ℝ`, (f_der). -/
def fR2 (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  -2 * (x ^ 3)⁻¹ + 2 * ∑ i, σ i ^ 3 / (N * (1 + σ i * x) ^ 3)
end Anisotropic
end
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- `m(z)`: the unique `w ∈ ℂ₊` with `f(w) = z`, (def_m); junk value `0` when there is none. -/
def mFun (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℂ :=
  if h : ∃ w : ℂ, 0 < w.im ∧ fC N σ w = z then h.choose else 0
end Anisotropic
end
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- `m` on `ℂ₊`, and its limit from `ℂ₊` elsewhere. -/
def mExt (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then mFun N σ z else limUnder (𝓝[upperHalf] z) (mFun N σ)
end Anisotropic
end
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- The density `π⁻¹ Im m(x + i0)`. -/
def rhoDens (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ := (mExt N σ x).im / Real.pi

/-- `ϱ = (1 - R)₊ δ₀ + 1_{(0,∞)} π⁻¹ Im m(x + i0) dx`. -/
def varrho (N : ℕ) (σ : Fin M → ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (1 - massRatio N σ) 0) • Measure.dirac 0 +
    (volume.restrict (Set.Ioi 0)).withDensity (fun x => ENNReal.ofReal (rhoDens N σ x))
end Anisotropic
end
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- `Q(x) = x² Π_s (1 + s x)² f'(x)`; its real roots off the poles are the finite
critical points of `f`, counted as in §2.2. -/
def critPoly (N : ℕ) (σ : Fin M → ℝ) : ℝ[X] :=
  ∏ s ∈ posVals σ, (1 + C s * X) ^ 2 -
    X ^ 2 * ∑ s ∈ posVals σ, C (weight N σ s * s ^ 2) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X) ^ 2

/-- `x ∈ (-s_n⁻¹, 0)`, i.e. `x ∈ I_1 ∪ ⋯ ∪ I_n` or `x` is an interior pole. -/
def InInner (σ : Fin M → ℝ) (x : ℝ) : Prop := x < 0 ∧ ∃ s ∈ posVals σ, 0 < 1 + s * x

/-- The multiset `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)`. -/
def innerCrit (N : ℕ) (σ : Fin M → ℝ) : Multiset ℝ :=
  (critPoly N σ).roots.filter (InInner σ)

/-- The number `p` of bulk components, `|𝒞| = 2p`. -/
def numBands (N : ℕ) (σ : Fin M → ℝ) : ℕ := (Multiset.card (innerCrit N σ) + 1) / 2

/-- `F(y) = f(1/y)`: the chart of `I_0` at `∞`, `I_0 ↔ (-s_n, ∞)`, `∞ ↔ 0`. -/
def FChart (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℝ :=
  -y + ∑ s ∈ posVals σ, weight N σ s * s * y / (y + s)

/-- `F'`. -/
def FChart1 (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℝ :=
  -1 + ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2

/-- `y ∈ (-s_n, ∞)`, i.e. `0 < y + s` for every `s ∈ {s_1, …, s_n}`. -/
def InChart (σ : Fin M → ℝ) (y : ℝ) : Prop := ∀ s ∈ posVals σ, 0 < y + s

/-- The critical point `x_{2p} ∈ I_0`, in the chart `y = 1/x`. -/
def yEdge (N : ℕ) (σ : Fin M → ℝ) : ℝ :=
  if h : ∃ y, InChart σ y ∧ FChart1 N σ y = 0 then h.choose else 0

/-- `x_k`, `k = 1, …, 2p`: `x_1 ≥ ⋯ ≥ x_{2p-1}` sorted, `x_{2p} = 1/y_{2p}`
(junk value `0` when `x_{2p} = ∞`). -/
def xCrit (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  if k = 2 * numBands N σ then (yEdge N σ)⁻¹
  else ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0

/-- The critical values `a_k = f(x_k)`, with `a_{2p} = F(y_{2p})`. -/
def edgeVal (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  if k = 2 * numBands N σ then FChart N σ (yEdge N σ) else fR N σ (xCrit N σ k)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- The eigenvalues of a real symmetric matrix (junk value `0` otherwise). -/
def specOf {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) : Fin K → ℝ :=
  if h : A.IsHermitian then h.eigenvalues else 0
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- (def_Pi) for a general `Σ`, at a given value `w` of `m`. -/
def piMat {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (w : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  fromBlocks (-(cplx Sig * (1 + w • cplx Sig)⁻¹)) 0 0 (w • 1)

/-- (def_Psi). -/
def Psi (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℝ :=
  √((mFun N σ z).im / (N * z.im)) + 1 / (N * z.im)

/-- (def_m_N), through the `𝓘_N × 𝓘_N` block of `G` ((G_N_ident)). -/
def mN {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ μ, G Sig Xm z (Sum.inr μ) (Sum.inr μ)

/-- `Σ̲⁻¹ (G − Π) Σ̲⁻¹`, with `m` of the eigenvalues of `Σ`. -/
def lawMat {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  (ulSigma N Sig)⁻¹ * (G Sig Xm z - piMat Sig (mFun N (specOf Sig) z)) * (ulSigma N Sig)⁻¹
section Laws
variable {Ω : Type*} [MeasureSpace Ω]
/-- Definition 3.20 (ii) at fixed `N, ε, D`: (isotropic law) on `S`. -/
def AnisotropicLawAt (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomMatAt N ε D (fun ω => lawMat Sig (X ω) z) (fun _ => Psi N (specOf Sig) z)

/-- Definition 3.20 (iii) at fixed `N, ε, D`: the averaged law on `S`. -/
def AveragedLawAt (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mN Sig (X ω) z - mFun N (specOf Sig) z)
    (fun _ => 1 / (N * z.im))
end Laws
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
namespace Anisotropic
/-- The sample space `Fin K × Fin N → ℝ` of a Gaussian `K × N` matrix. -/
def GaussSpace (K N : ℕ) : Type := Fin K × Fin N → ℝ

instance (K N : ℕ) : MeasurableSpace (GaussSpace K N) := MeasurableSpace.pi

/-- The product of `N(0, 1/N)` laws on `GaussSpace K N`. -/
instance (K N : ℕ) : MeasureSpace (GaussSpace K N) :=
  ⟨Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹⟩

/-- The coordinate matrix `X_{iμ}(ω) = ω (i, μ)` on `GaussSpace K N`. -/
def gaussX (K N : ℕ) : GaussSpace K N → Matrix (Fin K) (Fin N) ℝ := fun ω i μ => ω (i, μ)
end Anisotropic
end
end
section
open MeasureTheory Polynomial Filter Topology
open scoped ENNReal
noncomputable section
open Classical
namespace Anisotropic
variable {M : ℕ}
/-- `N_k = N ϱ([a_{2k}, a_{2k-1}])`, (def_N_k). -/
def bandCount (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  N * (varrho N σ (Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)))).toReal

/-- Definition 2.7 (i), (reg: edge). The third condition is void when `x_k = ∞`. -/
def RegularEdge (τ : ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ 2 * numBands N σ ∧ τ ≤ edgeVal N σ k ∧
    (∀ l, 1 ≤ l → l ≤ 2 * numBands N σ → l ≠ k → τ ≤ |edgeVal N σ k - edgeVal N σ l|) ∧
    (¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) → ∀ s ∈ posVals σ, τ ≤ |xCrit N σ k + s⁻¹|)

/-- Definition 2.7 (ii), with the explicit function `c : τ' ↦ c_{τ,τ'}`. -/
def RegularBulk (c : ℝ → ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ numBands N σ ∧ ∀ τ' > 0, 0 < c τ' ∧
    ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) + τ') (edgeVal N σ (2 * k - 1) - τ'), c τ' ≤ rhoDens N σ E
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}
/-- `Σ^r` on `ran Σ` and `0` on `ker Σ`, by spectral calculus (for `Σ > 0` the power of `Σ`;
for `r = −1/2` and singular `Σ ≥ 0`, the pseudo-inverse square root). -/
def sigPow (Sig : Matrix (Fin M) (Fin M) ℝ) (r : ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  cfc (fun x : ℝ => if 0 < x then x ^ r else 0) Sig

/-- (def_RM_RN): `R_N(z) = (X^* T^* T X − z)⁻¹` for a real `M × K` matrix `T`. -/
def RN {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (cplx (Xᵀ * Tᵀ * T * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- (def_RM_RN): `R_M(z) = (T X X^* T^* − z)⁻¹`. -/
def RM {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  (cplx (T * X * Xᵀ * Tᵀ) - z • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹

/-- (R_N_edge) at fixed `N, ε, D` on `S`, with `m` and `Ψ` of the eigenvalues of `Σ`. -/
def RNLawAt {Ω : Type*} [MeasureSpace Ω] (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) :
    Prop :=
  ∀ z ∈ S, ODomMatAt N ε D
    (fun ω => RN T (X ω) z - mFun N (specOf Sig) z • (1 : Matrix (Fin N) (Fin N) ℂ))
    (fun _ => Psi N (specOf Sig) z)

/-- (R_M_edge) at fixed `N, ε, D` on `S`:
`Σ^{−1/2}(R_M + (z(1 + mΣ))⁻¹)Σ^{−1/2} = O_≺(Ψ)`. -/
def RMLawAt {Ω : Type*} [MeasureSpace Ω] (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) :
    Prop :=
  ∀ z ∈ S, ODomMatAt N ε D
    (fun ω => cplx (sigPow Sig (-(1 / 2))) *
      (RM T (X ω) z + (z • (1 + mFun N (specOf Sig) z • cplx Sig))⁻¹) *
      cplx (sigPow Sig (-(1 / 2))))
    (fun _ => Psi N (specOf Sig) z)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}
/-- `Q_N = Xᵀ Σ X` (`N × N`); its nonzero eigenvalues are those of `Q = Σ^{1/2} X Xᵀ Σ^{1/2}`
(§3.2, before Theorem 3.12). -/
def QN (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Xmᵀ * Sig * Xm

/-- The eigenvalues in decreasing order, `λ_1 ≥ ⋯ ≥ λ_K` (index from `1`; `0` off range). -/
def sortedEig {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (i : ℕ) : ℝ :=
  if h : A.IsHermitian ∧ 1 ≤ i ∧ i ≤ Fintype.card (Fin K) then
    h.1.eigenvalues₀ ⟨i - 1, Nat.sub_one_lt_of_le h.2.1 h.2.2⟩
  else 0

/-- The classical counting function `n(E) = N ϱ([E, ∞))`. -/
def nClass (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : ℝ :=
  N * (varrho N σ (Set.Ici E)).toReal

/-- The classical locations (def:gamma_alpha): `γ_i = sup {E > 0 : n(E) ≥ i − 1/2}`. -/
def gammaLoc (N : ℕ) (σ : Fin M → ℝ) (i : ℕ) : ℝ :=
  sSup {E | 0 < E ∧ (i : ℝ) - 1 / 2 ≤ nClass N σ E}

/-- `d_k = N_1 + ⋯ + N_k` as a natural number (`N_l ∈ ℕ`, Lemma A.1). -/
def cumCount (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  ⌊∑ l ∈ Finset.Icc 1 k, bandCount N σ l⌋₊

/-- `N_k` (def_N_k) as a natural number. -/
def bandNat (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  ⌊bandCount N σ k⌋₊

/-- The relabelled classical location `γ_{k,i} = γ_{i + d_{k−1}}`. -/
def gammaBand (N : ℕ) (σ : Fin M → ℝ) (k i : ℕ) : ℝ :=
  gammaLoc N σ (cumCount N σ (k - 1) + i)

/-- The right side of (rigidity) at level `ε`: `N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}`. -/
def rigBound (N Nk i : ℕ) (ε : ℝ) : ℝ :=
  (N : ℝ) ^ ε * ((min i (Nk + 1 - i) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}
section ModelT
variable {Ω : Type*} [MeasureSpace Ω]
/-- Assumption 2.1 for a general deterministic `M × K` matrix `T` (`K = M̂`) and a random
`K × N` matrix `X`: (MsimN) for `M` and for `K`, the entry conditions on `X`, and
(bound_Sigma), (Sigma_gap) for the eigenvalues of `Σ = T Tᵀ` (no `Σ > 0`). -/
structure IsModelT (τ : ℝ) (C : ℕ → ℝ) (M K N : ℕ) (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) : Prop where
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  ratioK_ge : τ ≤ (K : ℝ) / N
  ratioK_le : (K : ℝ) / N ≤ τ⁻¹
  entries : EntryAssumption C X
  eig_le : ∀ i, specOf (T * Tᵀ) i ≤ τ⁻¹
  gap : ({i | specOf (T * Tᵀ) i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M
end ModelT
/-- (def_block_G) with the off-diagonal blocks `Σ^{1/2} T X R_N` and `R_N Xᵀ Tᵀ Σ^{1/2}`,
`Σ = T Tᵀ` (§11.1). -/
def blockG {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  fromBlocks
    (z • (cplx (sigPow (T * Tᵀ) (1 / 2)) * RM T X z * cplx (sigPow (T * Tᵀ) (1 / 2))))
    (cplx (sigPow (T * Tᵀ) (1 / 2) * T * X) * RN T X z)
    (RN T X z * cplx ((sigPow (T * Tᵀ) (1 / 2) * T * X)ᵀ)) (RN T X z)

/-- (def_m_N) for a general `T`: `m_N = N⁻¹ tr R_N`. -/
def mNT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * trace (RN T X z)
section LawsT
variable {Ω : Type*} [MeasureSpace Ω]
/-- (edge_G_result) for `G` of (def_block_G), in the weighted form: for all deterministic `v`,
`w`, `|⟨v, (G − Π) w⟩| ≺ Ψ |Σ̲ v| |Σ̲ w|`, with `Σ = T Tᵀ`, at fixed `N, ε, D` on `S`. -/
def AnisotropicLawTAt (N : ℕ) (ε D : ℝ) {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ v w : Fin M ⊕ Fin N → ℝ,
    DomAt N ε D
      (fun ω => ‖testBilin v (blockG T (X ω) z - piMat (T * Tᵀ) (mFun N (specOf (T * Tᵀ)) z)) w‖)
      (fun _ => Psi N (specOf (T * Tᵀ)) z * testNorm (SigU (T * Tᵀ) *ᵥ v) *
        testNorm (SigU (T * Tᵀ) *ᵥ w))

/-- (edge_G_avg_result) for a general `T` at fixed `N, ε, D` on `S`. -/
def AveragedLawTAt (N : ℕ) (ε D : ℝ) {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mNT T (X ω) z - mFun N (specOf (T * Tᵀ)) z)
    (fun _ => 1 / (N * z.im))
end LawsT
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}
/-- `λ_{k,i}` for a general `T`: the eigenvalues of `Xᵀ Tᵀ T X` (whose nonzero eigenvalues are
those of `Q = T X Xᵀ Tᵀ`), relabelled with the band counts of `Σ = T Tᵀ`. -/
def lamBandT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ)
    (k i : ℕ) : ℝ :=
  sortedEig (QN (Tᵀ * T) Xm) (cumCount N (specOf (T * Tᵀ)) (k - 1) + i)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
section Model
variable {Ω : Type*} [MeasureSpace Ω]
/-- The upper-triangular index set `{(i, j) : i ≤ j}`. -/
abbrev UpperIdx (N : ℕ) : Type := {p : Fin N × Fin N // p.1 ≤ p.2}

/-- The entry conditions of §12.1 for a Wigner matrix `W`: symmetric, measurable entries,
independent upper-triangular entries satisfying (cond on entries of X) and (moments of X-1). -/
structure WignerEntries (C : ℕ → ℝ) (N : ℕ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  measurable : ∀ i j, Measurable fun ω => W ω i j
  symm : ∀ ω, (W ω)ᵀ = W ω
  indep : iIndepFun (fun (p : UpperIdx N) (ω : Ω) => W ω p.1.1 p.1.2) ℙ
  mean : ∀ i j, ∫ ω, W ω i j = 0
  var : ∀ i j, ∫ ω, W ω i j ^ 2 = 1 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i j, Integrable fun ω => |Real.sqrt N * W ω i j| ^ p
  moment : ∀ (p : ℕ) i j, ∫ ω, |Real.sqrt N * W ω i j| ^ p ≤ C p

/-- The deformed Wigner model of §12.1: the entry conditions on `W`, and a deterministic real
symmetric `A` with `‖A‖ ≤ τ⁻¹`. -/
structure WignerModel (τ : ℝ) (C : ℕ → ℝ) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  entries : WignerEntries C N W
  symmA : A.IsHermitian
  normA : ‖A‖ ≤ τ⁻¹
end Model
/-- The variance of the GOE entry at `(i, j)`: `2/N` on the diagonal, `1/N` off it. -/
def goeVar (N : ℕ) (p : Fin N × Fin N) : ℝ≥0 :=
  if p.1 = p.2 then 2 * (N : ℝ≥0)⁻¹ else (N : ℝ≥0)⁻¹

/-- The sample space of the GOE (coordinates below the diagonal are unused). -/
def GOESpace (N : ℕ) : Type := Fin N × Fin N → ℝ

instance (N : ℕ) : MeasurableSpace (GOESpace N) := MeasurableSpace.pi

instance (N : ℕ) : MeasureSpace (GOESpace N) :=
  ⟨Measure.pi fun p : Fin N × Fin N => gaussianReal 0 (goeVar N p)⟩

/-- The GOE matrix `W_{ij} = ω (min(i,j), max(i,j))` on `GOESpace N`. -/
def goeW (N : ℕ) : GOESpace N → Matrix (Fin N) (Fin N) ℝ := fun ω i j => ω (min i j, max i j)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
/-- `m_A(w) = N⁻¹ ∑ᵢ (aᵢ − w)⁻¹` for the eigenvalues `a` of `A`. -/
def stieltjesA {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ℂ := (N : ℂ)⁻¹ * ∑ i, ((a i : ℂ) - w)⁻¹

/-- `m^W(z)`: the solution `m ∈ ℂ₊` of `m = N⁻¹ tr(−m + A − z)⁻¹ = m_A(z + m)` (§12.1);
junk value `0` when there is none. -/
def mW {N : ℕ} (a : Fin N → ℝ) (z : ℂ) : ℂ :=
  if h : ∃ m : ℂ, 0 < m.im ∧ m = stieltjesA a (z + m) then h.choose else 0
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
/-- `Ψ^W(z) = (Im m^W/(Nη))^{1/2} + (Nη)⁻¹`. -/
def PsiW {N : ℕ} (a : Fin N → ℝ) (z : ℂ) : ℝ :=
  √((mW a z).im / (N * z.im)) + 1 / (N * z.im)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
/-- `G^W(z) = (W + A − z)⁻¹`. -/
def GW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `Π^W(z) = (−m^W(z) + A − z)⁻¹`. -/
def piW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (cplx A - (mW (specOf A) z + z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `N⁻¹ tr G^W(z)`. -/
def mNW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * trace (GW A Wm z)

/-- The standing bound of §12.1: `|−m^W(z) + aᵢ − z| ≥ τ` on `S`. -/
def StandingBoundW {N : ℕ} (τ : ℝ) (a : Fin N → ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ i, τ ≤ ‖-(mW a z) + (a i : ℂ) - z‖

/-- `𝐃^W(τ, N) = {|E| ≤ τ⁻¹, N^{−1+τ} ≤ η ≤ τ⁻¹}`. -/
def domW (τ : ℝ) (N : ℕ) : Set ℂ :=
  {z | 0 < z.im ∧ |z.re| ≤ τ⁻¹ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ τ⁻¹}

/-- Definition 12.1: `S ⊆ 𝐃^W` closed under increasing `η` at fixed `E` inside `𝐃^W`. -/
def SpectralDomainW (τ : ℝ) (N : ℕ) (S : Set ℂ) : Prop :=
  S ⊆ domW τ N ∧ ∀ z ∈ S, ∀ w ∈ domW τ N, w.re = z.re → z.im ≤ w.im → w ∈ S
section Laws
variable {Ω : Type*} [MeasureSpace Ω]
/-- Definition 12.1 (i) at fixed `N, ε, D`: `(G^W − Π^W)_{st} = O_≺(Ψ^W)` on `S`. -/
def EntrywiseLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ s t, ODomAt N ε D (fun ω => (GW A (W ω) z - piW A z) s t)
    (fun _ => PsiW (specOf A) z)

/-- Definition 12.1 (ii) at fixed `N, ε, D`: `G^W − Π^W = O_≺(Ψ^W)` on `S`. -/
def AnisotropicLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomMatAt N ε D (fun ω => GW A (W ω) z - piW A z) (fun _ => PsiW (specOf A) z)

/-- Definition 12.1 (iii) at fixed `N, ε, D`: `N⁻¹ tr G^W − m^W = O_≺((Nη)⁻¹)` on `S`. -/
def AveragedLawWAt (N : ℕ) (ε D : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mNW A (W ω) z - mW (specOf A) z) (fun _ => 1 / (N * z.im))
end Laws
/-- (b) of Theorem 12.2 on `S`: `Ψ^W ≤ N^{−1/4−c₀}`. -/
def PsiSmallW {N : ℕ} (c₀ : ℝ) (a : Fin N → ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, PsiW a z ≤ (N : ℝ) ^ (-1 / 4 - c₀)
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
/-- `S(x) = N⁻¹ ∑ᵢ (aᵢ − x)⁻²` on the real axis. -/
def sW {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹

/-- `g(x) = x − m_A(x)` with `m_A(x) = N⁻¹ ∑ᵢ (aᵢ − x)⁻¹`, on the real axis; `z = g(z + m^W(z))`
is the self-consistent equation of §12.1. -/
def gW {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ := x - (N : ℝ)⁻¹ * ∑ i, (a i - x)⁻¹

/-- The critical point `x₊ > maxᵢ aᵢ` of `g`: the least `x > maxᵢ aᵢ` with `S(x) ≤ 1`. -/
def xpW {N : ℕ} (a : Fin N → ℝ) : ℝ := sInf {x | (⨆ i, a i) < x ∧ sW a x ≤ 1}

/-- The critical point `x₋ < minᵢ aᵢ` of `g`: the greatest `x < minᵢ aᵢ` with `S(x) ≤ 1`. -/
def xmW {N : ℕ} (a : Fin N → ℝ) : ℝ := sSup {x | x < (⨅ i, a i) ∧ sW a x ≤ 1}

/-- The right edge `L₊ = g(x₊)` of `ϱ^W` (§12.1, Definition 12.3). -/
def LpW {N : ℕ} (a : Fin N → ℝ) : ℝ := gW a (xpW a)

/-- The left edge `L₋ = g(x₋)` of `ϱ^W` (§12.1, Definition 12.3). -/
def LmW {N : ℕ} (a : Fin N → ℝ) : ℝ := gW a (xmW a)
section Rigid
variable {Ω : Type*} [MeasureSpace Ω]
/-- `[λ₁(H) − Lp]₊ ≺ N^{−2/3}` and `[λ_N(H) − Lm]₋ ≺ N^{−2/3}` at fixed `N, ε, D`. -/
def RigidExtremesAt (N : ℕ) (ε D Lm Lp : ℝ) (H : Ω → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  DomAt N ε D (fun ω => max (sortedEig (H ω) 1 - Lp) 0) (fun _ => (N : ℝ) ^ (-2 / 3 : ℝ)) ∧
    DomAt N ε D (fun ω => max (Lm - sortedEig (H ω) N) 0) (fun _ => (N : ℝ) ^ (-2 / 3 : ℝ))

/-- Definition 12.3 at fixed `N, ε, D`: the extreme eigenvalues of `H` are rigid with respect to
the edges `L±` of the density `ϱ^W` of the spectrum `a`. -/
def RigidExtremesWAt (N : ℕ) (ε D : ℝ) (a : Fin N → ℝ) (H : Ω → Matrix (Fin N) (Fin N) ℝ) :
    Prop :=
  RigidExtremesAt N ε D (LmW a) (LpW a) H
end Rigid
end Anisotropic
end
end
section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}
/-- `ϖ_k = (|f''(x_k)|/2)^{1/3}`. -/
def edgeScale (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  (|fR2 N σ (xCrit N σ k)| / 2) ^ (1 / 3 : ℝ)

/-- The sign `(-1)^{k+1}`: `1` at the upper end of a component, `-1` at its lower end. -/
def edgeSign (k : ℕ) : ℝ := if k % 2 = 1 then 1 else -1

/-- The index (in decreasing order) of the `i`-th extreme eigenvalue at the edge `k`:
`d_{k̂-1} + i` for odd `k` and `d_{k̂} + 1 - i` for even `k`, `k̂ = ⌈k/2⌉`. -/
def edgeIdx (N : ℕ) (σ : Fin M → ℝ) (k i : ℕ) : ℕ :=
  if k % 2 = 1 then cumCount N σ ((k + 1) / 2 - 1) + i
  else cumCount N σ ((k + 1) / 2) + 1 - i

/-- `q_{k,l}` for a symmetric `N × N` matrix `A` and the spectral data `σ`:
`q_{2j-1,l} = N^{2/3} ϖ⁻¹ (λ_{j,i} - a_{2j-1})_{i ≤ l}`,
`q_{2j,l} = -N^{2/3} ϖ⁻¹ (λ_{j,N_j+1-i} - a_{2j})_{i ≤ l}`. -/
def qVecA (N : ℕ) (σ : Fin M → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  fun i => edgeSign k * (N : ℝ) ^ (2 / 3 : ℝ) / edgeScale N σ k *
    (sortedEig A (edgeIdx N σ k (i + 1)) - edgeVal N σ k)

/-- `q_{k,l}` for a general `T`, from the eigenvalues of `Xᵀ Tᵀ T X` and the spectral data of
`Σ = T Tᵀ`. -/
def qVecT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA N (specOf (T * Tᵀ)) (QN (Tᵀ * T) Xm) k l

/-- The reference value `b_N(h, π)` of Theorem 3.18: `E h(q_{k,l})` for Gaussian `X` and
`Σ = diag(σ)`. -/
def bRef (N : ℕ) (σ : Fin M → ℝ) (k l : ℕ) (h : (Fin l → ℝ) → ℝ) : ℝ :=
  ∫ ω, h (qVecA N σ (QN (diagonal σ) (gaussX M N ω)) k l)
end Anisotropic
end
end

/-! ## The statements -/

section
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator
noncomputable section
open Classical
namespace Anisotropic
variable {M N : ℕ}

/-- Theorem 3.6, the anisotropic local law (edge_G_result) and the averaged local law (edge_G_avg_result) on the domain `𝐃(τ, N)`, under (T_diag), at fixed `N ≥ N₀`. -/
theorem thm_3_6 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      AnisotropicLawAt N ε D Sig X (specDomain τ N) ∧
        AveragedLawAt N ε D Sig X (specDomain τ N) := by
  sorry

/-- Theorem 3.7, the anisotropic local law outside the spectrum. -/
theorem thm_3_7 (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      ∀ z : ℂ, z.re ∈ Set.Icc τ τ⁻¹ → 0 < z.im → z.im ≤ τ⁻¹ →
        (N : ℝ) ^ (-2 / 3 + τ) ≤ Metric.infDist z.re (varrho N (specOf Sig)).support →
        ODomMatAt N ε D (fun ω => lawMat Sig (X ω) z)
          (fun _ => √((mFun N (specOf Sig) z).im / (N * z.im))) := by
  sorry

/-- Corollary 3.9, for general `T`. -/
theorem cor_3_9 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      RNLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        RMLawAt N ε D (T * Tᵀ) T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) := by
  sorry

/-- Theorem 3.12, rigidity of the eigenvalues, for general `T`. -/
theorem thm_3_12 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf (T * Tᵀ)) k → τ ≤ gammaBand N (specOf (T * Tᵀ)) k i →
          |lamBandT T (X ω) k i - gammaBand N (specOf (T * Tᵀ)) k i| ≤
            rigBound N (bandNat N (specOf (T * Tᵀ)) k) i ε} := by
  sorry

/-- Theorem 3.18, edge universality, for general `T` and bounded uniformly continuous test functions. -/
theorem thm_3_18 (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      |(∫ ω, h (qVecT T (X ω) k l)) - bRef N (specOf (T * Tᵀ)) k l h| ≤ ε := by
  sorry

/-- Proposition 11.1, the local laws for general `T`. -/
theorem prop_11_1 (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) → τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k →
        RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      AnisotropicLawTAt N ε D T X (specDomain τ N) ∧
        AveragedLawTAt N ε D T X (specDomain τ N) := by
  sorry

/-- Theorem 12.2, the anisotropic local law for deformed Wigner matrices. -/
theorem thm_12_2_aniso (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AnisotropicLawWAt N ε D A W S := by
  sorry

/-- Theorem 12.2, the averaged local law for deformed Wigner matrices. -/
theorem thm_12_2_avg (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε D A W S := by
  sorry

/-- Theorem 12.4, rigidity of the extreme eigenvalues of deformed Wigner matrices. -/
theorem thm_12_4 (τA : ℝ) (C : ℕ → ℝ) (τ₀ ε D : ℝ) (hτA : 0 < τA) (hτ₀ : 0 < τ₀)
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      WignerModel τA C N A W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      RigidExtremesWAt N ε D (specOf A) (fun ω => W ω + A) := by
  sorry

/-- Theorem 12.5, edge universality for deformed Wigner matrices. -/
theorem thm_12_5 (τA : ℝ) (C : ℕ → ℝ) (τ₀ : ℝ) (l : ℕ) (hτA : 0 < τA)
    (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (f : (Fin l → ℝ) → ℝ) (B L : ℝ), ContDiff ℝ 1 f → (∀ x, |f x| ≤ B) →
        (∀ x, ‖fderiv ℝ f x‖ ≤ L) → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
        WignerModel τA C N A W →
        StandingBoundW τ (specOf A) (domW τ N) →
        EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
        AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
        RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
        |(∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (W ω + A) (i + 1) - LpW (specOf A)))) -
          (∫ ω, f (fun i => (N : ℝ) ^ (2 / 3 : ℝ) *
              (sortedEig (goeW N ω + diagonal (specOf A)) (i + 1) - LpW (specOf A))))| ≤
          (N : ℝ) ^ (-c₀) := by
  sorry

end Anisotropic
end
