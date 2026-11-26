# Disproof of Firoozbakht's Conjecture on OEIS A086766

This repository packages a Lean 4 / Mathlib disproof of **Farideh Firoozbakht's conjecture on
OEIS A086766** (`OeisA86766.conjecture2`) for the [Palomar Registry](https://palomar-registry.org/),
matching [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/OEIS/86766.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Result

For $n \ge 1$ with $d$ decimal digits, let $a(n)$ be the least $r \ge 1$ such that the
$r$-fold decimal concatenation of $n$ followed by the digit $1$,
$$P_n(r) = 10 n \sum_{i=0}^{r-1} (10^d)^i + 1,$$
is prime, or $0$ if no such $r$ exists. Farideh Firoozbakht (Jan 7, 2015, OEIS A086766)
conjectured that $a(n) \ne 0$ whenever $n$ is not a power of $10$.

We disprove this conjecture with two explicit 6-digit counterexamples ($d = 6$, neither a power
of $10$):

1. **$n = 104040$ (`a_104040_eq_zero`):** Setting $K = 10^{3r}$,
   $$999999 \cdot P_{104040}(r) = 1040400 (K^2 - 1) + 999999 = (1020 K - 201)(1020 K + 201).$$
   For every $r \ge 1$, $K \ge 1000$, so $1020 K - 201 > 999999$. If $P_{104040}(r)$ were
   prime, it would divide one of the two factors, forcing $P_{104040}(r) \le 1020 K + 201$
   and hence $999999 \cdot P_{104040}(r) \le 999999 (1020 K + 201) < (1020 K - 201)(1020 K + 201)$,
   a contradiction.
2. **$n = 750760$ (`a_750760_eq_zero`):** Setting $K = 10^{3r}$,
   $$999999 \cdot P_{750760}(r) = (2740 K - 2551)(2740 K + 2551).$$
   Using $10^6 \equiv 1 \pmod m$ for the divisors of $999999 = 189 \cdot 5291 = 3861 \cdot 259$,
   we obtain explicit nontrivial factorizations of $P_{750760}(r)$ for both even and odd $r \ge 1$.

## Scope and Verification

- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
