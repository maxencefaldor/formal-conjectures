# OEIS A092243 (`conjecture1`): Prime-Gap Tug-of-War Positivity Beyond $250000$

This repository packages a pure-kernel Lean 4 / Mathlib proof of `OeisA92243.conjecture1`
for the [Palomar Registry](https://palomar-registry.org/), matching
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/OEIS/92243.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Result

Let $a(n) = \sum_{k=2}^n \operatorname{sign}(g_k - g_{k-1})$ be the tug-of-war score
between consecutive prime-gap increases and decreases (OEIS A092243), where $g_k = p_k - p_{k-1}$
(0-indexed primes $p_0 = 2, p_1 = 3, \dots$). We prove that there exists $n > 250000$ with
$a(n) > 0$, explicitly witnessing $n = 261150$ with $a(261150) = 1$.

## Prior Computational Knowledge and Proof Architecture

The zero-crossing at $n = 261149$ (giving $a(261150) = 1 > 0$) is known computationally via
[OEIS A175102](https://oeis.org/A175102). Our Lean 4 proof certifies this computation purely
inside the Lean kernel with **zero `native_decide`** and **zero `Lean.ofReduceBool`**:

1. **Part 1 (Sieve Bitmask Correctness):** Encodes odd primes up to $2 M + 1 = 3666583$
   ($M = 1833290$) in a single `Nat` bitmask `sieveS` generated from a binary tree of odd primes
   up to $1913$, proving exact primality membership (`sieveS_testBit_iff`).
2. **Part 2 (Gap Bitmasks):** Runs `gapLoop` over step sizes $d = 1, \dots, 74$ to compute
   exact bitmasks `inc` and `dec` of prime-gap increases and decreases.
3. **Part 3 (SWAR Popcount Correctness):** Proves correctness of a 21-round SWAR parallel
   popcount (`swarApply`) on $2^{21}$-bit integers.
4. **Part 4 (`conjecture1_witness`):** Evaluates `computeAll = (0, 1, 261150, 126043, 126043)`
   by `rfl` in the kernel (`computeAll_eq`), establishing that `a 261150 = 1`.

## Scope and Verification

- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
