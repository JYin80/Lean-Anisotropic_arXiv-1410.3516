# Paper versus Lean

This document compares the paper

> A. Knowles and J. Yin, *Anisotropic local laws for random matrices*, arXiv:1410.3516v4,

with its Lean 4 + Mathlib formalization in the library `Anisotropic`. It is written for a reader who knows the paper. Numbers of theorems, equations and sections are those of the paper. TeX labels are given in backticks with their prefix (for example `thm:LL_G`), and equation tags in parentheses (for example `(edge_G_result)`). A few places that have no label are located by the line of the arXiv v4 TeX source ("TeX line"). All Lean names are in the namespace `Anisotropic`, except the Mathlib name `TendstoInDistribution` (namespace `MeasureTheory`). Each Lean name in this document exists in the library and has been checked with `#check`.

## 1. Scope

**Formalized.** All results are for real matrices (β = 1). Deterministic test vectors are real.

- **(A) Local laws and rigidity for Q = TXX\*T\*.**
  - Theorem 3.6 (`thm:LL_G`) and Theorem 3.7 (`thm:G_outside`), under (T_diag), as in the paper.
  - Corollary 3.9 (`cor:GM_GN`) and Theorem 3.12 (`thm:rigidity`), for a general M × M̂ matrix T.
  - Theorems 3.14 (`thm:edge`), 3.15 (`thm:bulk`) and 3.16 (`thm:outside`), all items:
    - item (i) under (T_diag), as in the paper;
    - items (ii) and (iii) for a general T.
  - Proposition 11.1, stated without (T_diag) (Section 4), with the reduction of §11.1 (`sec:gen_T`). This covers both M̂ ≥ M and M̂ < M.
  - For each general-T result, the (T_diag) form is also a Lean theorem.
- **(B) Edge universality for Q.**
  - Theorem 3.18 (`thm:edge_univ`), for a general T.
  - Corollary 3.19 (i) (`cor:TWA`) for β = 1, conditional on two external inputs (Section 3).
- **(C) Extensions in §11.2 and §12.**
  - §11.2 (`sec:Q_dot`): Theorems 11.2 (`thm:local_laws_dot`), 11.3 (`thm:rigidity_dot`) and 11.4, both under (T_diag) and for a general T.
  - §12 (`sec:Wig`), deformed Wigner matrices: Theorems 12.2 (`lem:general Wig`), 12.4 (`thm:wigner_rig`) and 12.5 (`lem:comp Wig`).
- **An extension beyond the paper.** Corollary 3.19 (ii) for real Q (β = 1) with l = 1, at a fixed regular edge k, conditional on external inputs (Sections 3 and 4). The paper states 3.19 (ii) only for β = 2.

Section 7 lists the intermediate results of the paper that are named Lean theorems.

**Not formalized.**
- **The complex Hermitian case (β = 2).** By §2.1, all results hold for complex X after minor changes, and §12.1 makes the same remark for W and A. The library works only with real X and real test vectors. So the following are not formalized:
  - Corollary 3.19 (ii) as stated (β = 2);
  - the β = 2 half of Corollary 3.19 (i).
- **The Tracy–Widom limit itself.** Two facts are explicit hypotheses, not theorems (Section 3):
  - the existence of the GOE edge limit law;
  - the comparison of the Gaussian case with the GOE.
- **Remarks and side statements:**
  - the joint distribution at several regular edges (after Theorem 3.18 and after Corollary 3.19), and the universality of the condition number;
  - Remark 3.8 (outliers);
  - Remark 3.10 (the R_N, R_M form of Theorem 3.7);
  - Remark 3.13 (delocalization);
  - Remark 3.17 (the smaller error outside the spectrum in Theorems 3.14 and 3.16);
  - the rigidity of all eigenvalues of W + A (after Theorem 12.4);
  - the relaxations of `(moments of X-1)` and `(MsimN)` mentioned in §2.1.

## 2. Endpoint table

**Form of the statements.** Every probabilistic statement is made at fixed N with explicit constants:

> for all parameters (τ, the moment bounds C_p, the bulk function c, ε, D, …) there is N₀ such that for every N ≥ N₀ and every model satisfying the hypotheses, each on its own probability space, the bad event has probability at most N^{−D}.

- N₀ depends only on the leading parameters. It is uniform in the model, in z, in the deterministic vectors, and in the edge index k.
- Stochastic domination ≺ (Definition 3.4) is a derived notion (`DomAt`, `HighProbAt`).
- A statement "X → x as N → ∞" in the paper becomes either a bound at fixed N ≥ N₀ that holds uniformly over all models, or a limit along an arbitrary sequence of models with N_n → ∞.

The model hypotheses are `IsModel` (Assumption 2.1 with (T_diag)) and `IsModelT` (Assumption 2.1 for a general M × K matrix T, K = M̂). Regularity is `RegularEdge` and `RegularBulk` (Definition 2.7).

| Paper result (TeX label) | Lean names | File (`Anisotropic/…`) | Form |
|---|---|---|---|
| Theorem 3.6 (`thm:LL_G`) | `LL_G` | `Endpoints/Main.lean` | fixed N; (T_diag); edge hypothesis in the τ/2 form (Section 4) |
| Theorem 3.7 (`thm:G_outside`) | `G_outside` | `Rigidity/Outside.lean` | fixed N; (T_diag); edge hypothesis in the τ/2 form; no bulk hypothesis |
| Corollary 3.9 (`cor:GM_GN`) | `cor_GM_GN_gen`; (T_diag): `cor_GM_GN` | `GeneralT/Main.lean`, `Endpoints/Main.lean` | fixed N; general T; `(R_M_edge)` with the pseudo-inverse |
| Theorem 3.12 (`thm:rigidity`) | `rigidity_gen`; (T_diag): `rigidity` | `GeneralT/Rigidity.lean`, `Rigidity/Main.lean` | fixed N; one event for all (k, i) |
| Theorem 3.14 (`thm:edge`) (i) | `edge_law_tauEdge`, `edge_law` | `Main.lean`, `Endpoints/Main.lean` | fixed N; (T_diag); explicit window `tauEdge` |
| Theorem 3.14 (ii) | `edge_law_R_gen_tauEdge`, `edge_law_R_gen`; (T_diag): `edge_law_R` | `Main.lean`, `GeneralT/Main.lean`, `Endpoints/Main.lean` | fixed N; general T |
| Theorem 3.14 (iii) | `rigidity_edge_gen_tauEdge`, `rigidity_edge_gen`; (T_diag): `rigidity_edge` | `Main.lean`, `GeneralT/Rigidity.lean`, `Rigidity/Main.lean` | fixed N; general T; one event |
| Theorem 3.15 (`thm:bulk`) (i) | `bulk_law` | `Endpoints/Main.lean` | fixed N; (T_diag) |
| Theorem 3.15 (ii) | `bulk_law_R_gen`; (T_diag): `bulk_law_R` | `GeneralT/Main.lean`, `Endpoints/Main.lean` | fixed N; general T |
| Theorem 3.15 (iii) | `rigidity_bulk_gen`; (T_diag): `rigidity_bulk` | `GeneralT/Rigidity.lean`, `Rigidity/Main.lean` | fixed N; general T; one event |
| Theorem 3.16 (`thm:outside`) (i) | `outside_law` | `Endpoints/Main.lean` | fixed N; (T_diag) |
| Theorem 3.16 (ii) | `outside_law_R_gen`; (T_diag): `outside_law_R` | `GeneralT/Main.lean`, `Endpoints/Main.lean` | fixed N; general T |
| Proposition 11.1 (no label, TeX line 3030) | `LL_G_gen` | `GeneralT/Main.lean` | fixed N; general T, no (T_diag); weighted `(edge_G_result)` for `blockG` |
| Theorem 3.18 (`thm:edge_univ`) | `edge_univT_lip`, `edge_univT`; (T_diag): `edge_univ_lip`, `edge_univ` | `EdgeUniv/GeneralT.lean`, `EdgeUniv/Main.lean` | `_lip`: \|E h(q_{k,l}) − b\| ≤ K(‖h‖_∞ + Lip h)N^{−1/(800(l+1))} at N ≥ N₀, for bounded Lipschitz h; otherwise ≤ ε at N ≥ N₀(h, ε), for bounded uniformly continuous h; b = `bRef` |
| Corollary 3.19 (`cor:TWA`) (i), β = 1 | `twaT_cmp`, `twaT_conv`; (T_diag): `twa_cmp`, `twa_conv` | `EdgeUniv/TWAT.lean`, `EdgeUniv/TWA.lean` | conditional on `HCmp1`, and on the GOE limit for `_conv`; `_cmp`: comparison with the GOE at N ≥ N₀; `_conv`: convergence in distribution along every model sequence |
| Theorem 11.2 (`thm:local_laws_dot`) | `local_laws_dot`, `local_laws_dot_gen` | `Qdot/LocalLaw.lean` | transfer statement: the laws for G at (ε₁, D₁) on a spectral domain give those for Ġ at (ε, D) |
| Theorem 11.3 (`thm:rigidity_dot`) | `rigidity_dot`, `rigidity_dot_gen`; also `rigidity_dot_N`, `rigidity_dot_literal_false` | `Qdot/Rigidity.lean`, `Instances/MarchenkoPasturTwo.lean` | fixed N; classical quantities of N − 1 samples (Section 4) |
| Theorem 11.4 (no label, TeX line 3123) | `edge_univ_dotT_lip`, `edge_univ_dotT`; (T_diag): `edge_univ_dot_lip`, `edge_univ_dot` | `Qdot/EdgeUniv.lean` | as Theorem 3.18, at the partner edge with N − 1 samples (Section 4) |
| Theorem 12.2 (`lem:general Wig`) (i) | `general_wig_aniso_class`, `general_wig_aniso`, `general_wig_aniso_lit` | `Wigner/Main.lean` | transfer statement: the entrywise law for (W^Gauss, D, S) at (ε₁, D₁) gives the anisotropic law for (W, A, S) at (ε, D) |
| Theorem 12.2 (ii) | `general_wig_avg`, `general_wig_avg_phi` | `Wigner/AvgMain.lean` | transfer statement, as (i) |
| Theorem 12.4 (`thm:wigner_rig`) | `wigner_rig_class`, `wigner_rig`, `wigner_rig_lit` | `Wigner/Rigid.lean` | ∃ τ ∈ (0, τ₀], ∃ (ε₁, D₁): the Gaussian-side hypotheses at (τ, ε₁, D₁) give rigid extremes of W + A at (ε, D) |
| Theorem 12.5 (`lem:comp Wig`) | `wigner_edge_univ_lip_class`, `wigner_edge_univ`, `wigner_edge_univ_left_lip_class`, `wigner_edge_univ_left` | `Wigner/EdgeUniv.lean` | as 12.4; rate K(‖f‖_∞ + Lip f)N^{−1/(800(l+1))}, or N^{−c₀} for C¹ f, with c₀ > 0 depending only on l (the proof takes c₀ = 1/(1600(l+1))); both edges |
| Corollary 3.19 (ii), β = 1, l = 1 (beyond the paper) | `twaET_cmp`, `twaET_conv`; (T_diag): `twaE_cmp`, `twaE_conv` | `EdgeUniv/TWAEdgeT.lean`, `EdgeUniv/TWAEdge.lean` | conditional on `HCmp1E`, and on the GOE limit at l = 1 for `_conv`; fixed edge k |

**Which form is the paper's.** For Corollary 3.9, Theorem 3.12, Theorems 3.14–3.16 (ii), (iii), Theorem 3.18 and Corollary 3.19, the general-T theorem is the paper's statement and the (T_diag) theorem is a special case. For §11.2 the paper works under (T_diag) and says the assumption can be removed as in §11.1; the library gives both forms.

**Variants that are corollaries.** `_class` is a statement over a class of entry laws. `_lit` adds the interval-support condition of §12.1 (Section 4).

**Non-vacuity.** The endpoint files contain compiled `example`s that instantiate the theorems along concrete families of models, for all large n. The families are:
- Marchenko–Pastur: Σ = I_n, N = 2n, Rademacher or Gaussian X;
- for general T, a padded T with K < M and singular Σ;
- Σ = I_{2n}, N = n;
- for §12, a Rademacher Wigner matrix with the rank-one, non-diagonal A = (4N)⁻¹𝟙𝟙ᵀ.

Two kinds of hypotheses stay as hypotheses of these examples:
- the external inputs of Corollary 3.19;
- the Gaussian-side premises of Theorems 12.2, 12.4 and 12.5 (Section 3).

## 3. External inputs

**None for (A), (C), and Theorem 3.18.** Every result that the paper cites is proved in the library, with one exception: the inputs of Corollary 3.19 listed below. This includes:
- Lemma 4.8 (`lem:norm_XX`, from [BEKYY, Theorem 2.10]): `norm_XtX_le`;
- the lower bound c ≤ E₁₁ used in the proof of Lemma 10.4;
- the large deviation estimates of [BEKYY, Lemma 3.1];
- Lemma 4.10 (`lem:gen_prop_m`, after [BaoPanZhou]): `gen_prop_m`;
- fluctuation averaging, Lemma 5.6 ([BEKYY, §4.2], [EKYY4, Appendix B]): `fluct_avg`;
- the moment bounds of Lemma 6.2 (the paper uses the polynomialization of [BEKYY, Section 5]; see Section 6);
- the counting arguments of §10 deferred to [EYY3, PY].

**The deformed-GOE premises of §12 are not external inputs.** In Theorems 12.2, 12.4 and 12.5, the following are the paper's own hypotheses:
- the entrywise and averaged laws for (W^Gauss, D);
- the rigidity of the extremes of W^Gauss + D.

They stay hypotheses of the Lean theorems, and the library does not prove them. The same holds for the premise of Theorem 11.2 (the laws for G), which the examples discharge with Theorem 3.6 (`LL_G`, `LL_G_gen`).

**The inputs of Corollary 3.19.** Each is a `Prop`-valued definition used as an explicit hypothesis of the theorem. None is an `axiom`.

- **The GOE side.**
  - `goeW` N is the GOE: symmetric, independent upper-triangular entries, off-diagonal variance 1/N, diagonal variance 2/N.
  - `goeEdge` N l is the vector N^{2/3}(μ₁ − 2, …, μ_l − 2) of the display before Corollary 3.19.
  - `goeEdgeLaw` N l is its law.
- **`HTW1` l** (for Corollary 3.19 (i) and its real extension). The law of the GOE edge vector converges weakly to a probability measure on ℝ^l; this measure plays the role of q_l^1. Basis: the display before Corollary 3.19 and [TW1, TW2]. The `_conv` theorems take the limit ν and the convergence `goeEdgeLaw` N l → ν as hypotheses; this is the witness form of `HTW1`.
- **`HCmp1` τ l** (for Corollary 3.19 (i)).
  - Statement: for every bounded Lipschitz h, the Gaussian reference value `bRef` N σ 1 l h and E h(`goeEdge` N l) differ by at most ε for N ≥ N₀. This holds uniformly over the reference class `RefClass` τ M N σ.
  - The reference class is: σ ≥ 0, σ ≤ τ⁻¹, `(Sigma_gap)`, τ ≤ M/N ≤ τ⁻¹, and the edge 1 regular.
  - Basis: the works on the Gaussian case cited before Corollary 3.19 ([HHN, ElK2, Ona, SL]). For l > 1, `HCmp1` is the joint form of these cited results.
  - The class allows singular Σ. The cited form with σ > 0 at parameter τ² gives this form at τ.
- **`HCmp1E` τ k** (for the real extension of Corollary 3.19 (ii), l = 1).
  - Statement: the same comparison at the edge k with l = 1, uniformly over `RefClassE` τ M N σ k (the reference class with the edge k regular).
  - At even k the statistic q_{k,1} carries the sign −1, so the lowest eigenvalue of the component is compared with μ₁.
  - Basis: Fan–Johnstone, arXiv:1707.02352, Theorem 2.9 (`thm:TW` in v4, a label of that paper, not of this one), together with the GOE Tracy–Widom theorem [TW1, TW2].
  - At k = 1 it is `HCmp1` with l = 1 (`hCmp1E_one_iff`).
  - The hypothesis is for one fixed k. A version for k = k_N would need a premise uniform in k; it is not formalized.

**Limit check (Σ = I, φ = M/N).** Here f(x) = −1/x + φ/(1 + x).
- **Top edge.** The critical point is x₁ = −1/(1 + √φ), so a₁ = (1 + √φ)², and ϖ₁ = (|f″(x₁)|/2)^{1/3} = (1 + √φ)(1 + φ^{−1/2})^{1/3}.
  - Johnstone's TW₁ scaling for N·XᵀX has centre (√N + √M)² = N a₁ and scale N^{1/3}(1 + √φ)(1 + φ^{−1/2})^{1/3} = N^{1/3} ϖ₁.
  - So q_{1,1} = N^{2/3}(λ₁ − a₁)/ϖ₁ has the same TW₁ limit as N^{2/3}(μ₁ − 2) for the GOE with semicircle on [−2, 2].
  - At φ = 1: a₁ = 4 and ϖ₁ = 2^{4/3} = 2.51984.
  - At φ = 1/2: a₁ = 2.91421, and ϖ₁ = 2.29009 from f″, which equals Johnstone's scale.
- **Lower edge, φ = 1/2 (k = 2).** a₂ = (1 − √φ)² = 0.08579, x₂ = −1/(1 − √φ), and ϖ₂ = 0.21833 = (1 − √φ)^{4/3} φ^{−1/6}, the smallest-eigenvalue TW₁ scale. The sign of q_{2,1} = −N^{2/3}(λ − a₂)/ϖ₂ matches `edgeSign` 2 = −1.

## 4. Statement differences

"Touches" says whether a difference changes a hypothesis (H) or a conclusion (C), and in which direction. "Form" means an equivalent reformulation.

| Paper location | Paper | Lean | Reason | Touches |
|---|---|---|---|---|
| Theorems 3.6, 3.7, Corollary 3.9, Theorem 3.12, Proposition 11.1 (also inherited by Theorem 11.3) | every edge k with a_k ≥ τ is regular (Definition 2.7 (i)) | every edge k with a_k ≥ τ/2 is regular with parameter τ/2; the domains of the conclusions are unchanged | z = τ + iN^{−1+τ} ∈ 𝐃 can lie within τ′ of an edge a_k ∈ (τ − τ′, τ), which the paper does not require to be regular, while the covering in the proof of Theorem 3.6 (TeX lines 2821–2823) uses regularity of all nearby edges | H: changed. It adds the edges with a_k ∈ [τ/2, τ) and relaxes the parameter for the others; in general neither form implies the other. Theorems 3.14–3.16 keep their own hypotheses (one edge regular at τ, one bulk component regular, or none) |
| Corollary 3.9 `(R_M_edge)`, Theorems 3.14–3.16 (ii), general T | Σ^{−1/2}(R_M + (z(1 + mΣ))⁻¹)Σ^{−1/2} = O_≺(Ψ) | `RMLawAt`: Σ^{−1/2} is the Moore–Penrose pseudo-inverse on ran Σ (`sigPow`), test vectors weighted \|v\|\|w\| | without (T_diag), Σ = TT\* can be singular (always when M > M̂), and Σ^{−1/2} is undefined; on ker Σ, R_M v = −v/z, so the bracket vanishes there | C: form; equal to the paper's when Σ > 0 |
| Proposition 11.1 `(edge_G_result)` | Σ̲⁻¹(G − Π)Σ̲⁻¹ = O_≺(Ψ) | `AnisotropicLawTAt`: \|⟨v, (G − Π)w⟩\| ≺ Ψ\|Σ̲v\|\|Σ̲w\| | Σ̲⁻¹ is undefined for singular Σ; this is the form the limit argument of §11.1 gives | C: form; equivalent for Σ > 0 |
| Proposition 11.1 | "Suppose that (T_diag) and Assumption 2.1 hold" | Assumption 2.1 for a general T (`IsModelT`) | the purpose of the proposition is to remove (T_diag); with it, the proposition restates Theorem 3.6 | H: typo; the condition is not part of the statement |
| `(def_block_G)` and the display of Ĝ before it | off-diagonal blocks T̂XR_N, TXR_N | Σ^{1/2}TXR_N and its transpose (`blockG`) | derived from ÛŜ^{1/2} = T̂ and ÛŜ^{1/2}Û\* = Σ̂^{1/2}; under (T_diag) it agrees with `(G=G)` | C of 11.1: typo |
| Theorem 3.15 | "the bulk component k = 1, …, 2p" | k = 1, …, p | bulk components are numbered 1, …, p | H: typo |
| Definition 3.4 (iii) | deterministic vectors | real deterministic vectors | complex vectors follow by linearity (constant factor 4) | C: form, all anisotropic statements |
| Definition 3.4 (i) | ≺ with N ≥ N₀(ε, D) | fixed-N form with explicit constants, uniform over all models (Section 2) | precision | form |
| `(moments of X-1)` | moments bounded for p ∈ ℕ | integrability of \|√N X_{iμ}\|^p stated, for all p ∈ ℕ including p = 0 (only C_0 ≥ 1) | implicit condition made explicit | H: form |
| `(decompfullG)` (§4) | G = −Σ̲ + Σ̲JG_NJ\*Σ̲ | −(Σ ⊕ 0) in place of −Σ̲ | at M = N = 1, Σ = 1, X = 0 the NN block is −1 − 1/z ≠ −1/z | intermediate identity only (Section 5) |
| Lemma 4.9 (`lem:opnorm`) | bounds C‖X\*X‖η⁻¹ and C‖X\*X‖η⁻² | ((1 + ‖XᵀX‖)/η + 1) and (1 + ‖XᵀX‖)/η² (`opnorm_G`, `opnorm_dG`) | the printed bounds fail at X = 0, z = i | intermediate lemma only (Section 5) |
| Definitions 5.4 (`def:stability`), A.2 (`def:strong_stab`) | one constant C in the one-step implication | two constants: C₀ when κ + η > K₀δ, C₁ otherwise (`StableOn`, `StronglyStableOn`) | the one-step implication with one constant is not established by the paper's argument (Section 5) | intermediate definitions only; no endpoint changes |
| `(MsimN)`, `(phi_bounded)` | M ≍ M̂ ≍ N; τ ≤ φ ≤ τ⁻¹ for small τ | τ ≤ M/N ≤ τ⁻¹ and τ ≤ M̂/N ≤ τ⁻¹ with the same τ | explicit form | H: form |
| Definition 2.7 (ii) | c = c_{τ,τ′} exists | the function c is a parameter (`RegularBulk` c) | explicit constants | H: form |
| Theorems 3.12, 3.14 (iii), 3.15 (iii) | ≺ for each (k, i) | one high-probability event for all (k, i) at once | — | C: stronger |
| Theorem 3.14 | ∃ τ′ depending only on τ | explicit τ′ = `tauEdge` τ for (i)–(iii); (i) holds for every τ″ ≤ `edgeTau'` τ, and (ii) for a general T for every τ″ ≤ `tauGen` τ | explicit constants | C: explicit, stronger |
| Theorem 3.12, general T | λ_{k,i}: eigenvalues of Q | eigenvalues of XᵀTᵀTX (`lamBandT`); the first M ∧ N agree with those of Q; Σ_k N_k = N ∧ rank Σ | — | form |
| Theorem 3.18 (`thm:edge_univ`), also general T and Theorem 11.4 | for every h ∈ C_b(ℝ^l) | for every bounded uniformly continuous h; and for bounded Lipschitz h with the rate K(‖h‖_∞ + Lip h)N^{−1/(800(l+1))}, K uniform in h | Green function comparison controls uniformly continuous h. All of C_b would need tightness of q_{k,l}, which the paper does not prove: the local law and rigidity give only \|q_{k,l}\| ≺ 1 | C: restricted to a smaller class of h |
| Theorem 3.18 | ∃ b(h, π) depending only on π, lim (E h(q_{k,l}) − b) = 0 | b = `bRef` N σ k l h, the value of E h(q_{k,l}) for Gaussian X and Σ = diag(σ), fixed before the model; \|E h − b\| ≤ ε at N ≥ N₀, uniformly over models and k; the paper's "∃ b, limit along sequences" form is a compiled `example` | `bRef` depends on N and on the nonzero eigenvalues of Σ with multiplicity (`bRef_nzEq`), hence on M through φ as well as on π | C: stronger (explicit b, uniform) |
| Theorem 3.18, Corollary 3.19 | l ∈ ℕ | l : ℕ, l = 0 allowed (trivial) | — | harmless generalization |
| Corollary 3.19 (i) (β = 1) | consequence of 3.18 and the cited Gaussian results | `HCmp1` τ l (and the GOE limit for convergence) are explicit hypotheses; convergence is `TendstoInDistribution` along every sequence of models with N_n → ∞ (Ω, M, N, Σ or T may vary); the comparison with the GOE at fixed N ≥ N₀ is a separate theorem; q_l^1 appears only as the weak limit of the GOE edge laws | the Tracy–Widom limit and the Gaussian comparison are external | H: external premises added (Section 3) |
| Corollary 3.19 (ii) | β = 2, any l, the edge k | new statement: β = 1, l = 1, at a fixed regular edge k, under `HCmp1E` τ k and the GOE limit at l = 1 | real case from Fan–Johnstone; l ≥ 2 has no cited result. The paper's convention (§2.1) lets non-constant quantities depend on N, so its k may be k_N; the Lean convergence statement is for a fixed k (a k depending on N would need a premise uniform in k). Theorem 3.18 itself is uniform in k | new statement beyond the paper |
| Theorem 11.2 | "the entrywise and averaged local laws hold for Ġ" | anisotropic and averaged laws for Ġ | typo: the conclusion is `(isotropic law dot)` | C: wording |
| Theorem 11.2 | Q̇ without the factor N/(N − 1) in the proof | Q̇ with the factor of `(def_Q)` (`QdotN`); m and Π at φ = M/N; the laws for G at (ε₁, D₁) give those for Ġ at (ε, D) | as stated in the paper ("provided they hold for G") | form |
| Theorems 11.3 (`thm:rigidity_dot`), 11.4 | "Theorem 3.12 (3.18) remains valid if λ is replaced with λ̇" | the classical quantities of Q̇ are those of N − 1 samples: φ̇ = M/(N − 1), Ṅ_k, γ̇_{k,i}, ȧ_k, ϖ̇_k; hypotheses unchanged (regularity at N) | rank Q̇ ≤ N − 1, so λ̇_N = 0. If rank Σ ≥ N and a_{2p} ≥ τ, the classical location γ_{p,N_p} ≥ a_{2p} ≥ τ. The literal Theorem 11.3 is false: `rigidity_dot_literal_false` at Σ = I_{2n}, N = n, Gaussian X, τ = 1/10, where every hypothesis holds and the event is empty for n ≥ 216. With the classical quantities of N, the bound holds at every index except (p, N_p) when M ≥ N (`rigidity_dot_N`) | C: changed |
| Theorem 11.4, read literally | as above | not stated | At k = 2p with rank Σ ≥ N, the first coordinate of q̇_{2p,l} is the deterministic N^{2/3}a_{2p}/ϖ_{2p} → ∞. So the literal statement fails if b is the reference value of Q, and holds only in a degenerate way if b may be any function of N and π | — |
| Theorem 11.4 | q̇_{k,l} at the edge k | q̇ centred and scaled at the partner k′ = `edgePartner` N σ k: the edge of the (N − 1)-sample data with the parity of k that is closest to a_k (within C₁/N and regular at parameter τ/2 for N − 1 samples, `edgePartner_spec`); reference `bRef` with N − 1 samples; hypotheses as in Theorem 3.18 (only the edge k regular at N) | a gap of width ~1/N above a_k can close at N − 1 and renumber the edges. Example: σ = (24/5)^{×10} ∪ 1^{×10}, M = 20, τ = 1/10, k = 4: at N = 40 there are 4 edges, at N = 39 there are 2, and k′ = 2. In most cases k′ = k. The reading with the quantities of N and the index k is not given for 11.4: it would require an edge comparison between two Gaussian ensembles | C: centring convention |
| Theorem 12.2 | "the Gaussian case" premise; W^Gauss a GOE; the support of ϱ^W is an interval [L₋, L₊] | transfer statement with the premise for (`goeW`, D) as hypothesis; GOE with diagonal variance 2/N (`IsGOE`), while W has diagonal variance 1/N; the primary version is for a class of entry laws with diagonal variance in [1/N, 2/N] (`WigClassEntries`); the interval-support condition is dropped, and the literal form is `general_wig_aniso_lit`; the standing assumption \|−m^W + a_i − z\| ≥ τ is `StandingBoundW`; (b) is assumed on all of S | the proof does not use the interval support | H: one hypothesis dropped (stronger) |
| Theorem 12.4 | "for any fixed and small enough τ" the laws for (W^Gauss, D, 𝐃^W(τ, N)) hold, and the extremes of W^Gauss + D are rigid | ∃ τ ∈ (0, τ₀], ∃ (ε₁, D₁): the laws at that τ and (ε₁, D₁), the standing bound at τ, and the rigid extremes at (ε₁, D₁) give rigid extremes at (ε, D); τ may depend on τ_A, τ₀, ε; ‖A‖ ≤ τ_A⁻¹ has its own τ_A; L± are the extreme points of supp ϱ^W (`LpW`, `LmW`, `tsupport_rhoW_extreme`), with no interval-support condition; literal form `wigner_rig_lit` | the premise is needed only at one τ | H: weaker, so the statement is stronger |
| Theorem 12.5 | "smooth f", f[…] − f[…] = O(N^{−c₀}) | f is C¹, bounded, with bounded derivative; the expectations E, missing in `(Wigner_edge_univ)`, are restored; some c₀ > 0 depending only on l is chosen before f (the proof takes c₀ = 1/(1600(l+1))), N₀ after f; a rate form for bounded Lipschitz f; the left edge ("a similar result") is a separate theorem | typo (missing E) and an implicit condition (bounded f) | C: form; stronger (c₀ uniform in f) |

## 5. Errors and gaps in the paper

In every case below, the statement is true after a correction, or the proof was repaired. The rows of Section 4 that are themselves corrections (Proposition 11.1, `(def_block_G)`, Theorem 3.15, `(decompfullG)`, Lemma 4.9, Definitions 5.4/A.2, Theorems 11.3, 11.4) are not repeated here, except where the proof issue needs a word.

**Statements that are false as printed (corrected).**

| Location | Issue | Correction |
|---|---|---|
| Lemma 4.9 (`lem:opnorm`) | at X = 0, z = i: ‖Σ̲⁻¹(G + Σ̲)Σ̲⁻¹‖ = √2, but the bound is 0 | bounds with 1 + ‖XᵀX‖ (Section 4); the uses in §7 need only a polynomial bound |
| `(decompfullG)` | −Σ̲ should be −(Σ ⊕ 0) | see Section 4 |
| Proof of Lemma 6.2, TeX lines 1633–1635 | the sub-claim (XG^{(iT)}X\*)_{ii} − m = O_≺(σ_i²Ψ) is false for small σ_i | it holds with O_≺(Ψ); the remainder of the geometric expansion is O_≺(σ_i^{L+1}Ψ^L), not O_≺(σ_i^{3L+1}Ψ^L) |
| Remark 3.11 | +((φ − 1)/φ)(1/z) | +((1 − φ)/φ)(1/z), since tr R_M = tr R_N − (M − N)/z |
| §5.2, TeX line 1522 | Z_s = (1 − 𝔼_s)G_ss⁻¹ | Z_s = −(1 − 𝔼_s)G_ss⁻¹ (only \|Z_s\| is used) |
| Proof of Lemma 2.4 (Appendix A) | the sign of (x²f′)′ on I₁ | reversed sign |
| Proof of Theorem 11.2 | the second form of `(G_M dot id)`, the upper-right block of Ġ and the formula for Ġ_N carry "+" | "−" (with the power of z in the upper-right block adjusted) |
| Lemma 7.16 (`lem:0_to_theta`) as used in §12.2 | stated for n ∈ [4, 4p]; without an upper bound on n it is false | used only for n ≤ 4p, with the tail of the expansion from n + 2 on |
| Proof of Theorem 12.2 (i), TeX lines 3398–3400 | \|Σ_i G_{si}Π_{ii}\| ≺ N^{1/2}Ψ fails for non-diagonal A | holds after averaging over s; the conclusion is unchanged |
| Lemma 8.11 (`lem:87`), `(im_BGB)`, `(moment_matching)`, §8.3 | missing factor N^{κ(k+d_X)} in 8.11; a dropped product term in `(im_BGB)`; per-entry error N^{−2} and E f(0) versus f(0) in `(moment_matching)`; exponents in §8.3 (N^{3δ} for N^{2δ}, (C₀/2 + 2)δ for (C₀/2 + 1)δ) | corrected statements; the conclusions of §§7–8 are unchanged |
| §7.2, TeX line 1717 | a net with \|Ŝ\| ≤ N^{20} | N^{21} (for N ≥ 10τ^{−2}) |

**Arguments that are not established as written (repaired; statements unchanged unless noted).**

| Location | Issue | Repair |
|---|---|---|
| Definitions 5.4, A.2, Lemma A.5 | the one-step implication with a single constant C is not established by the paper's argument when κ + η ≍ Cδ. A first-order counterexample to the one-step implication: the second root of the quadratic lies at distance ≍ √(κ + η) from m, of the same order as the bound | two-regime constants (Section 4); downstream only B ≤ C₁δ/(√(κ + η) + √δ) is used |
| Definition 5.4 | u must be the Stieltjes transform of a measure on [0, C]; the measure of m_N lies in [0, ‖XᵀΣX‖], which is ≤ C only with high probability | stability is applied on the event {‖XᵀX‖ ≤ C} |
| Proof of Theorem 3.6, TeX lines 2821–2823 | 𝐃 = ⋃𝐃^e_k ∪ ⋃𝐃^b_k ∪ 𝐃^o fails near 0 ∈ supp ϱ (for example z = i when φ < 1) and next to non-regular edges below τ | the region {η ≥ τ/2} is added, with a smaller window; together with the τ/2 edge hypothesis (Section 4) |
| Proof of Theorem 3.7 (TeX line 2958) | "an easy consequence of Theorems 3.6 and 3.12", but those assume bulk regularity and 3.7 does not | proved by localization: 3.14 (i), 3.16 (i), a localized gap lemma and 3.14 (iii); 3.7 keeps the paper's hypotheses |
| Lemma 4.10 (`lem:gen_prop_m`) | no argument for \|m\| ≤ C | supplied |
| Proof of Proposition 9.1, the case n = 3 | the replacement Σ_ν → Σ_{ν≠μ} is not trivial at ν = μ for the word μiiμ | a column expansion; two displays have typos (𝓘_M∖{μ} for 𝓘_N∖{μ}, a missing factor G_μμ) |
| After `(improved_avg_G)` (TeX line 2870) | "(κ + η)^{−1/2}Ψ² satisfies `(Phi_cond)`" fails on 𝐃^e_k when τ < 1/4 | used on the domain of Lemma 10.1, where it holds |
| §10 counting: Lemmas 10.1, 10.4, Proposition 10.2, Theorem 3.12 | Lemma 10.1 assumes all regularity, but Theorems 3.14 (iii) and 3.15 (iii) need a local form (TeX line 2960 says this without proof). In Lemma 10.4, Σ(t) need not stay regular along the deformation. At TeX line 2950, d_k ≤ (1 − c)N does not follow from "N_p ≥ cN". The conclusion of 3.12 is deferred to [EYY3, PY], and the bottom count at k = p is missing | localized gap lemmas (`gap_window`, `gap_edgeWin`, `gap_outside`); a gap-midpoint window in Lemma 10.4; d_k ≤ (1 − c)N from the critical-point equation; the counting is written out |
| §11.1, "a simple approximation argument in ε" (TeX lines 3027–3029) | under the hypotheses of Theorem 3.6: Assumption 2.1 for Ŝ + ε holds only at parameter τ³; bands tangent below τ/2 may merge; bulk regularity is not uniform in ε | the (T_diag) laws are applied region by region, with stability constants from the local data of Σ; the limit at fixed N uses Fatou on strict events |
| TeX line 632 and Remark A.7 (`rem:bulk_stab`) | the stability of bulk regularity under perturbation of π | holds only in windows; used only there |
| Proof of Theorem 11.3 ("follows that of Theorem 3.12 to the letter") | the hypotheses of 3.12 can fail at N − 1; regularity passes from N to N − 1 only edge by edge (partner edges), and bulk regularity can fail | interlacing with the N-sample model and a secular sign count |
| Proof of Theorem 12.4 (§12.4) | 𝐒_τ uses an undefined δ; "it is not hard to deduce" the averaged bound; repeating from `(tur1)`, `(tur2)` needs m^W = ∫ϱ^W(x)(x − z)⁻¹dx, which §12 does not state; square-root edges of ϱ^W are used | δ := τ_S; a general lemma for any random symmetric matrix with an averaged law and rigid extremes (`avg_law_outside`), by a weighted maximum-modulus argument; a difference-quotient bound through the continuation of m^W across (L₊, ∞) (`im_mW_tur_le`); the square-root edges are derived (no hypothesis added) |
| Proof of Theorem 12.5 (TeX line 3463) | Ψ ≤ N^{−1/3−c} | N^{−1/3+c} (Ψ ≥ (Nη)⁻¹); 12.2 (b) applies with c₀ = 1/12 − c |

**Typos and implicit conditions** (no effect on any endpoint statement):
- Lemma 4.4 (v): s, t ∈ 𝓘∖{k} should be 𝓘∖{r}.
- `(Gia3)`: (G^{(i)}X)_{μi} should be (G^{(i)}X\*)_{μi}.
- §7.1 and §7.3: X⁰ = G^Gauss should be X^Gauss.
- §5.1: \|1 + m_Nσ₁\| ≥ c should hold for all σ_i.
- §7.2: z ↦ Σ⁻¹(G − Π)Σ̲⁻¹ should be Σ̲⁻¹(G − Π)Σ̲⁻¹.
- Definition 7.19: the Leibniz coefficient should be n!.
- Proof of Lemma 7.12: I_N should be mI_N.
- Definition 8.6, Lemmas 8.5 and 8.10: small errors (zero brackets, a missing transposed term, the parity rule).
- Proof of Proposition 9.1 (TeX lines 2753, 2757): 𝓘_M∖{μ} should be 𝓘_N∖{μ}.
- Proof of Lemma 10.1: γ₊ (undefined) should be a₁.
- Lemma 10.3: X(t)ΣX(t)\* should be X(t)\*ΣX(t).
- Lemma 10.4: N^{−2/3+τ} should be N^{−2/3+ε}, and a_{2k} should be a_{2k}(t).
- Proofs of Lemmas A.6 and A.8: 𝐃^e_k should be 𝐃^b_k and 𝐃^o respectively.
- Example 2.8: i = 1, …, 2p should be 2p − 1.
- After Theorem 3.12: N_i should be N_k.
- Definition 2.7 (ii): "form below" should be "from below".
- §12.1: "H + A" should be "W + A".
- §12.2: a subscript in a five-factor product.
- Lemma 2.2: "probability measure on ℝ" should be "on [0, ∞)", which is needed for supp ϱ ⊂ [0, ∞).
- Theorem 3.21: the Gaussian matrix has independent N(0, 1/N) entries.

## 6. Differences in the proofs

These change no statement.
- **Lemma 6.2 and Proposition 6.1.** The moment bounds use the sign-flip symmetry of the Gaussian ensemble: odd fibres vanish, and a matching count gives E\|𝒵\|^p ≤ (2p − 1)!!2^pEΛ_o^p. The paper instead refers to the polynomialization of [BEKYY, Section 5].
- **Removing (T_diag) (§11.1).** A single reduction to (Ŝ + κP₀, X), with Ŝ = TᵀT and P₀ the projection onto ker Ŝ, followed by κ ↓ 0 at fixed N. The polar decomposition is written with the partial isometry TŜ^{+1/2}. No zero padding and no auxiliary matrix Y are needed; the same reduction covers M̂ < M. The same reduction gives Theorem 3.18 and Theorem 11.4 for a general T (`regS`).
- **Definitions.**
  - m(z) is defined as the unique root in ℂ₊ of z = f(m) (`mFun`).
  - ϱ is explicit: an atom at 0 plus the density π⁻¹ Im m(x + i0) on (0, ∞) (`varrho`). The identity "m is the Stieltjes transform of ϱ" is a theorem (`resolventTransform_varrho`).
  - The edges a_k are the critical values of f.
- **Theorem 3.7.** Proved by localization (Section 5), not as a consequence of Theorems 3.6 and 3.12.
- **Lemma 10.3.** Continuity of eigenvalues is replaced by norm continuity and a counting form of Weyl's inequality.
- **Theorem 11.3.** Secular-equation counting and interlacing with the N-sample model, not a rerun of the proof of Theorem 3.12.
- **Theorem 11.4.** For Gaussian X, Q̇ is exactly a sample covariance matrix with N − 1 samples (`integral_qDotVec_gauss`). This is why the reference value uses N − 1.
- **Edge universality.** One reduction (`edge_reduction`) is proved once and used for Theorems 3.18, 11.4 and 12.5. It turns the edge regime of both ensembles and the comparison of smooth functionals into the comparison of E h(q) for bounded Lipschitz h. Bounded uniformly continuous h follow by uniform approximation (`exists_lipschitz_approx`).
- **Corollary 3.19.** Convergence in distribution follows from the bounded Lipschitz comparison and the GOE limit (`tendstoInDistribution_of_goeCmp`). No separate tightness argument is needed, because the limit is a probability measure.
- **Theorem 12.4.** A weighted maximum-modulus argument (`avg_law_outside`) and an explicit constant in `(tur1)`.

## 7. Intermediate results

**Paper results that exist as named Lean theorems or definitions** (beyond the endpoints of Section 2):

- **§2.**
  - Lemma 2.2 and Definition 2.3, for π the empirical spectral measure of Σ (the only case used): `mFun`, `varrho`, `resolventTransform_varrho`.
  - Lemmas 2.4 (`existsUnique_yEdge`), 2.5 (`edgeVal_mem_Icc`, `edgeVal_succ_le`, `mExt_edgeVal`) and 2.6 (`mem_support_varrho_iff`).
  - Definition 2.7 (`RegularEdge`, `RegularBulk`).
- **§3.**
  - Definition 3.4 (`DomAt`, `ODomAt`, `ODomMatAt`).
  - Definition 3.20 (`SpectralDomain`, `EntrywiseLawAt`, `AnisotropicLawAt`, `AveragedLawAt`).
  - Theorem 3.21 (`gen_iso_aniso`, `gen_iso_avg`, `anisoAll_of_gauss`), a transfer statement at fixed N of the same form as Theorem 11.2, with the constant of `(1+xm)` as a parameter; Theorem 3.22 (`diag_gen`, `gauss_avg_input`), with `(1+xm)` and the stability of Definition 5.4 on S as hypotheses.
- **§4.**
  - Lemma 4.8 (`norm_XtX_le`).
  - Lemma 4.9 with corrected bounds (`opnorm_G`, `opnorm_dG`).
  - Lemma 4.10 (`gen_prop_m`).
  - Definition 4.7 (`HighProbAt`).
- **§5.**
  - Proposition 5.1 (`weak_law`).
  - Lemmas 5.2 (`lambdaO_Z_bound`), 5.3 (`calD_bound`), 5.5 (`initial_bound`) and 5.6 (`fluct_avg`).
  - Definition 5.4 (`StableOn`).
- **§6.** Proposition 6.1, in its general and Gaussian forms: `gauss_aniso`, `gauss_gen_iso`, `aniso_of_diag`, `gauss_averaged`, `gauss_averaged'`, `gauss_aniso_gaussX`, `gauss_averaged_gaussX`.
- **§7.**
  - Lemmas 7.3 (`propA_zero`), 7.7 (`integral_le_of_domAt`), 7.8 (`comparison_zero`), 7.9 (`interpol`) and 7.12 (`rough_bound`).
  - Lemmas 7.4, 7.5, 7.10, 7.11, 7.13, 7.14, 7.15 and 7.17, in forms with a general constant C₀ (the paper uses one C₀ depending only on τ): `propC_of_propA_gen`, `moment_bound_gen`, `main_comparison_gen`, `main_comparison2_gen`, `cor_rough_bound'`, `rough_bound_upd'`, `taylor_exp'`, `sc_step3'`.
  - Lemma 7.16, in the forms used in §§7–9 and §12: `avg_zero_to_theta`, `zero_to_theta3`, `wig_zero_to_theta`.
  - Definition 7.19 (`Word`).
- **§8.**
  - Proposition 8.1 (`prop_comparison_two`).
  - Lemmas 8.3 (`sc_step3_three`), 8.4 (`sc_step5_three`), 8.5 (`hatA_replace`), 8.8 (`lem82`), 8.10 (`tagDeg_parity`, `dX_odd`) and 8.11 (`colPoly_bound`, `lem87`).
- **§9.** Proposition 9.1 (`prop_gen_avg`).
- **§10.**
  - Lemma 10.1 (`gap_window`, `gap_edgeWin`, `gap_outside`).
  - Proposition 10.2 (`prop_counting`).
  - Lemmas 10.3 (`interp_count`) and 10.4 (`lambdaMin_ge`, `gauss_count`).
- **§12.**
  - Definitions 12.1 (`SpectralDomainW`, `EntrywiseLawWAt`, `AnisotropicLawWAt`, `AveragedLawWAt`) and 12.3 (`RigidExtremesWAt`).
  - Lemmas 12.6 (`wig_rough_bound`), 12.7 (`wig_coeff_high`, `wig_coeff_three`) and 12.8 (`wig_avg_coeff`).
- **Appendix A.**
  - Lemmas A.1 (`Ni_sum`), A.3 (`xCrit_bounds`, `edgeScale_bounds`), A.4 (`m_sq_root_edge`, `mz_reg_edge`), A.5 (`stab_edge2`), A.6 (`m_sq_root_bulk`, `stab_bulk_weak`) and A.8 (`m_sq_root_outside`, `stab_outside`).
  - Definition A.2 (`StronglyStableOn`).

**Paper results that are not separate Lean theorems.**
- **Proposition 7.1** (`prop:comparison_1`). It is the case E X³ = 0 of Proposition 8.1 (`prop:comparison_2`), which has the same remaining hypotheses. So Proposition 8.1 (`prop_comparison_two`) contains it.
- **Lemma 8.2** (`lem:71`). It is proved inside the proof of Proposition 8.1, as non-public steps.
- **Two pieces of Appendix A.** The labelled display `(E-a_exp)` of Lemma A.4 and the real-axis form of `(mz_reg)` outside the spectrum. Neither is needed for the endpoints. Lemma A.4 is used through `m_sq_root_edge` and `mz_reg_edge`, and the complex form of `(mz_reg)` outside the spectrum through `mz_reg_outside`.
- **Part of Lemma 2.5.** The statement 1/m(z) → 0 as z → 0 when x_{2p} = ∞ (the convention m(0) = ∞) is not a Lean theorem. It is not needed.

## 8. Constants

All constants are explicit, but the library does not optimize them. The paper allows constants "depending only on τ", and the library meets that requirement with explicit functions of τ that are tiny.
- **The window of Theorem 3.14.**
  - τ′(τ) = `tauEdge` τ = min(`edgeTau'` τ/2, `tauGen` τ). Here `tauGen` τ = `edgeTau'`(min(τ³, τ/4))/4 comes from the §11.1 reduction (parameter τ³), and `edgeTau'` comes from the constants of Lemma A.3.
  - At τ = 1/5: log₁₀ `tauGen`(1/5) ≈ −116.3 and log₁₀(`edgeTau'`(1/5)/2) ≈ −48.7. So `tauEdge`(1/5) = `tauGen`(1/5) ≈ 10^{−116}.
  - Theorem 3.14 (iii) has an index in its window only once N^{−2/3} ≲ τ′, that is, N ≳ 10^{174} at τ = 1/5.
- **N₀.** It is explicit in principle but is never computed. Since it follows the windows and the high-moment steps, it is astronomically large.
- **Comparison constants.** In §8, C₀ = ⌈2400/τ⌉ (`czero`) and δ = min(ε, τ)/(4C₀) (`deltaTwo`); the comparison lemmas are stated for a general C₀: `cor_rough_bound'`, `rough_bound_upd'`, `taylor_exp'` and `sc_step3'` for C₀ ≥ 25 with C₀δ ≤ τ/4, and `propC_of_propA_gen`, `moment_bound_gen`, `main_comparison_gen` and `main_comparison2_gen` for C₀ ≥ `czero` τ.
- **Rates.**
  - Theorems 3.18 and 11.4: K(‖h‖_∞ + Lip h)N^{−1/(800(l+1))}, from ε = 1/200 and the rate ε/(4(l + 1)).
  - Theorem 12.5: the same rate in the Lipschitz form, and, for C¹ f, N^{−c₀} with the proof's value c₀ = 1/(1600(l + 1)) (the statement asserts some c₀ > 0 depending only on l). The bound N^{−c₀} holds once N^{1/(1600(l+1))} ≥ K(B + L), where B = ‖f‖_∞ and L bounds the derivative.
- **The choice of τ in Theorem 12.4.** τ = min(τ₀, τ_S/4) with τ_S = min(ε, 1/24, (C_W + 2τ_A⁻¹)⁻¹), where C_W bounds ‖W‖ with high probability (`wig_norm_le`).
