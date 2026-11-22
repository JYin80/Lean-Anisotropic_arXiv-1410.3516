# Lean formalization of Knowles–Yin, "Anisotropic local laws for random matrices"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Antti Knowles and Jun Yin, *Anisotropic local laws for random matrices*,
> [arXiv:1410.3516](https://arxiv.org/abs/1410.3516).

The version of the paper that the Lean code follows is
[`paper/KnowlesYin_Anisotropic_Lean_version.pdf`](paper/KnowlesYin_Anisotropic_Lean_version.pdf) (LaTeX source in
`paper/tex/`). It is arXiv:1410.3516v4 with the corrections found during the formalization; theorem and equation
numbers are unchanged. Numbers in [`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) refer to this version.

Sister projects: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718) (Yau–Yin, arXiv:2501.01718) and
[RBM2D](https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606) (Dubova–Yang–Yau–Yin, arXiv:2503.07606).

## Main results

All results are for real matrices (β = 1) and real deterministic vectors. Every Lean name below is in the namespace
`Anisotropic`. The sample covariance matrix is `Q = T X X* T*` with `X` an `M̂ × N` matrix of independent centred
entries of variance `1/N` (Assumption 2.1); `(T_diag)` is the special case `T = Σ^{1/2}` diagonal.

| Paper | Lean theorem(s) | File (`Anisotropic/…`) |
|---|---|---|
| Theorem 3.6, anisotropic local law | `LL_G` | `Endpoints/Main.lean` |
| Theorem 3.7, outside the spectrum | `G_outside` | `Rigidity/Outside.lean` |
| Corollary 3.9 | `cor_GM_GN_gen`; `(T_diag)`: `cor_GM_GN` | `GeneralT/Main.lean`, `Endpoints/Main.lean` |
| Theorem 3.12, rigidity | `rigidity_gen`; `(T_diag)`: `rigidity` | `GeneralT/Rigidity.lean`, `Rigidity/Main.lean` |
| Theorem 3.14 (edges) | `edge_law`, `edge_law_R_gen`, `rigidity_edge_gen` (and the `_tauEdge` forms) | `Endpoints/Main.lean`, `GeneralT/`, `Main.lean` |
| Theorem 3.15 (bulk) | `bulk_law`, `bulk_law_R_gen`, `rigidity_bulk_gen` | `Endpoints/Main.lean`, `GeneralT/` |
| Theorem 3.16 (outside) | `outside_law`, `outside_law_R_gen` | `Endpoints/Main.lean`, `GeneralT/Main.lean` |
| Proposition 11.1, general `T` | `LL_G_gen` | `GeneralT/Main.lean` |
| Theorem 3.18, edge universality | `edge_univT_lip`, `edge_univT`; `(T_diag)`: `edge_univ_lip`, `edge_univ` | `EdgeUniv/GeneralT.lean`, `EdgeUniv/Main.lean` |
| Corollary 3.19 (i), β = 1 | `twaT_cmp`, `twaT_conv`; `(T_diag)`: `twa_cmp`, `twa_conv` | `EdgeUniv/TWAT.lean`, `EdgeUniv/TWA.lean` |
| Theorems 11.2–11.4, the centred matrix `Q̇` | `local_laws_dot(_gen)`, `rigidity_dot(_gen)`, `edge_univ_dotT(_lip)`, `edge_univ_dot(_lip)` | `Qdot/` |
| Theorem 12.2, deformed Wigner matrices | `general_wig_aniso`, `general_wig_avg` (and `general_wig_aniso_class`) | `Wigner/Main.lean`, `Wigner/AvgMain.lean` |
| Theorem 12.4, rigidity of the extremes | `wigner_rig` (and `wigner_rig_class`) | `Wigner/Rigid.lean` |
| Theorem 12.5, edge universality | `wigner_edge_univ`, `wigner_edge_univ_left` (and `_lip_class` forms) | `Wigner/EdgeUniv.lean` |
| Corollary 3.19 (ii) for β = 1, l = 1 (beyond the paper) | `twaET_cmp`, `twaET_conv`; `(T_diag)`: `twaE_cmp`, `twaE_conv` | `EdgeUniv/TWAEdgeT.lean`, `EdgeUniv/TWAEdge.lean` |

Every probabilistic statement is made at fixed `N ≥ N₀` with explicit constants, uniformly over all models that
satisfy the hypotheses; stochastic domination (Definition 3.4) is a derived notion. `docs/PAPER-VS-LEAN.md` §2
gives the form of each statement and §4 every difference from the printed one. The main ones:
- the edge regularity hypotheses of Theorems 3.6, 3.7, Corollary 3.9, Theorem 3.12 and Proposition 11.1 are imposed
  on the edges with `a_k ≥ τ/2`, at parameter `τ/2` (the paper's covering argument needs the edges just below `τ`);
- Theorem 3.18 is for bounded uniformly continuous test functions (with an explicit rate for bounded Lipschitz
  ones), since the paper's `C_b` would need a tightness statement that is not proved;
- Theorems 11.3 and 11.4 use the classical quantities of `N − 1` samples (Theorem 11.3 as printed is false, and the
  library proves this: `rigidity_dot_literal_false`);
- Theorems 11.2, 12.2, 12.4 and 12.5 are transfer statements: the paper's hypotheses on the Gaussian (or GOE) side
  stay hypotheses.

## External inputs

Theorems 3.6–3.18, §11 and §12 use no result of another paper: everything the paper cites (the norm bound of
[BEKYY], the large deviation estimates, fluctuation averaging, the counting arguments of §10, …) is proved here.

Corollary 3.19 depends on the Tracy–Widom theory for the Gaussian case, which enters as explicit hypotheses
(`Prop`-valued definitions, not axioms):
- `HTW1` (the GOE edge vector converges in law; the `_conv` theorems take the limit and the convergence as
  hypotheses);
- `HCmp1` (comparison of the Gaussian reference value with the GOE, after the works cited before Corollary 3.19)
  for part (i), and `HCmp1E` (the same at a fixed edge `k`, l = 1, after Z. Fan and I. M. Johnstone,
  [arXiv:1707.02352](https://arxiv.org/abs/1707.02352)) for the real form of part (ii).

`docs/PAPER-VS-LEAN.md` §3 states them precisely, with the limit check of the scaling.

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There
is no `sorry` and no declared `axiom`. The files contain `#print axioms` commands for the main theorems and their
ingredients, which print only these axioms when the library is built.

## Build

The toolchain is `leanprover/lean4:v4.36.0-rc1` (file `lean-toolchain`) with Mathlib `v4.36.0-rc1`.

```
lake exe cache get
lake build
```

The hypotheses of the theorems can be satisfied: the files with the main theorems contain compiled examples that
apply them to concrete families of models for all large `n` (Marchenko–Pastur with `Σ = I_n`, `N = 2n` and
Rademacher or Gaussian entries; a general `T` with singular `Σ`; `Σ = I_{2n}`, `N = n`; and, for §12, a Rademacher
Wigner matrix with a rank-one non-diagonal `A`). The families themselves are in `Instances/` (the Gaussian matrix `gaussX` is in
`Probability/NormBound/GaussianLower.lean`, and the Wigner family `wigRad`, `aEx` in `Wigner/Model.lean`).

## Map of the library

Section numbers refer to the paper in `paper/`.

- `Framework/`: the model (Assumption 2.1) and stochastic domination (Definition 3.4).
- `LinAlg/`: block matrices, resolvent identities, minors, the Ward identity and operator norm bounds (§4).
- `Probability/`: large deviation estimates, the norm bound of Lemma 4.8 (truncation and closed walks), a net of
  the unit sphere, and the Gaussian lower bound used in Lemma 10.4.
- `Density/`: the measure `ϱ`, the function `f`, its critical points and edges (§2.2, Appendix A.1), and the
  stability of the self-consistent equation (Definitions 5.4, A.2, Appendix A).
- `Entrywise/`: the entrywise local law for `Σ = diag(σ)` and fluctuation averaging (§5).
- `Gaussian/`: the Gaussian case, Proposition 6.1 and Lemma 6.2 (§6).
- `Comparison/`: the self-consistent comparison argument (§7, §8).
- `Averaged/`: the averaged local law (§9).
- `Rigidity/`: eigenvalue counting and rigidity (§10).
- `Endpoints/`: the statements of §3 under `(T_diag)` and their assembly; `Main.lean`: the common window
  `tauEdge` of Theorem 3.14 and the main theorems instantiated at the model families.
- `GeneralT/`: general `T` (§11.1).
- `EdgeUniv/`: edge universality (Theorem 3.18) and Corollary 3.19.
- `Qdot/`: the centred matrix `Q̇` (§11.2).
- `Wigner/`: deformed Wigner matrices (§12).
- `Instances/`: the concrete model families used in the examples.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, the external inputs of Corollary 3.19, the
errors found in the paper, and where the Lean proof takes a different route.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Antti Knowles and Jun Yin. Lean formalization: Jun Yin.

## Palomar

The repository is laid out for the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics.
All source files use Lean's module system. [`Anisotropic/MainDefs.lean`](Anisotropic/MainDefs.lean) holds every
definition used by the statements of Theorems 3.6, 3.7, 3.12, 3.18, Corollary 3.9, Proposition 11.1 and
Theorems 12.2, 12.4, 12.5, and depends on Mathlib only; [`Challenge.lean`](Challenge.lean) is the statement to audit
(it imports Mathlib only and repeats the definitions of `Anisotropic/MainDefs.lean`),
[`Solution.lean`](Solution.lean) proves it from the library, [`comparator.json`](comparator.json) names the compared
theorems and [`formalization.yaml`](formalization.yaml) holds the metadata. `lake build` also builds `Challenge.lean`
(ten `sorry` warnings, by design) and `Solution.lean`. `python3 scripts/check-lean-sources.py` and
`./scripts/verify-comparator.sh` (Linux, needs `bwrap`) run the checks locally; submissions go to
<https://submit.palomar-registry.org/>.
