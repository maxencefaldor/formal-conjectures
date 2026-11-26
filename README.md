# Ben Green's Open Problem 40: $f(2) = 1$

This repository packages a Lean 4 / Mathlib formalization of the radius-2 case of **Ben Green's
Open Problem 40** (`Green40.green_40.f_two_eq_one : f 2 = 1`) for the
[Palomar Registry](https://palomar-registry.org/), matching
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/GreensOpenProblems/40.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Theorem

Let $f(r) = \liminf_{n \to \infty} \min_{V \le \mathbb{F}_2^n:\, V + H(r) = \mathbb{F}_2^n} \frac{|V|\,|H(r)|}{2^n}$
be the asymptotic linear covering density of radius-$r$ Hamming balls in $\mathbb{F}_2^n$.
Then $f(2) = 1$.

## Mathematical Source and Proof Architecture

This formalization implements the proof of **Jensen Kohlmeyer and Liam Kruer**,
*Asymptotically optimal binary linear covering codes of radius two* (September 15, 2026 draft,
[PDF](https://liamkruer.com/assets/work/conjectures/problems/green-40/paper/proof.pdf)):

1. **Lower bound (`one_le_f_two`):** Every covering subspace $V$ satisfies
   $|V|\,|H(2)| \ge 2^n$, so `minDensity n 2 >= 1` for all $n$ and hence `1 <= f 2`.
2. **Upper bound (`f_two_le_one`):** Constructs admissible binary quadratic maps
   `AdmissibleQuad n (2 * t)` for arbitrarily large powers of two $2^r = 2t$
   (`exists_admissibleQuad_pow_two`), producing covering subspaces of arbitrarily large ambient
   length $N$ with covering density at most $1 + 12 / 2^t$
   (`exists_minDensity_le_of_admissibleQuad`). Taking $t \to \infty$ gives `f 2 <= 1`.

## Scope and Verification

- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
