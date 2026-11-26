# Disproof of the Pierce-Birkhoff Conjecture

This repository packages a Lean 4 / Mathlib disproof of the **Pierce-Birkhoff conjecture**
for the [Palomar Registry](https://palomar-registry.org/), directly refuting the exact
declaration `PierceBirkhoff.pierce_birkhoff_conjecture` in
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/PierceBirkhoff.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Mathematical Source and Closing Issue #5602

Following **Zehua Lai, Lek-Heng Lim, and Junyu Ren**, *Pierce-Birkhoff conjecture is false*,
[arXiv:2609.10420](https://arxiv.org/abs/2609.10420) (September 2026), we construct a
30-dimensional piecewise-quadratic function on $\mathbb{R}^{30} \simeq S^2(\mathbb{R}^5) \times S^2(\mathbb{R}^5)$:
for symmetric $5 \times 5$ real matrices $(X, Y)$ with $P = X Y$, set
$q_{ij,\pm}(X, Y) = P_{ii} \pm 4 P_{ij}$ ($i \ne j$), $h(X, Y) = \min q_{ij,\pm}(X, Y)$,
and $f(X, Y) = h(X, Y)$ if $h(X, Y) > 0$ and $\det X > 0$, else $0$.

As documented in `google-deepmind/formal-conjectures` Issue #5602, two gaps remained between
existing claims and `FormalConjectures/Wikipedia/PierceBirkhoff.lean`:
1. The paper's 30-dimensional theorem was stated over a semi-algebraic partition rather than
   a finite **closed** semi-algebraic covering (`IsPiecewiseMvPolynomial`).
2. The authors' separate $n=8$ Lean development proved `¬ IsPolynomialLattice f` rather than
   refuting the explicit max-of-min normal form `⨆ i, ⨅ j, MvPolynomial.eval x (g i j)`.

Our Lean 4 proof closes both gaps directly:
- **Parts 1-3 (`isPiecewiseMvPolynomial_fFn`):** Constructs explicit closed semi-algebraic
  pieces covering $\mathbb{R}^{30}$ on each of which `fFn` agrees with either `0` or one of
  the quadratic polynomials $q_{ij,\pm}$.
- **Parts 4-5:** Establishes homogeneous-component degree-0, degree-1, and degree-2 identities
  for polynomials bounding `fFn` along positive rays.
- **Parts 6-7 (`fFn_pertPt_pos`, `fFn_pertPt_neg`, generic orbit point):** Analyzes two-sided
  perturbations along the determinant-zero boundary orbit $O$ and uses column-permutation
  invariance to refute every finite max-of-min representation (including empty index types via
  `fFn_toVec_one_one : fFn (toVec 1 1) = 1`).

## Scope and Verification

- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
