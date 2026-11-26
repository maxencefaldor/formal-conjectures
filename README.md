# Erdős Problem 14 (Parts (i) and (ii))

This repository packages an independent Lean 4 / Mathlib formalization resolving **both parts
of Erdős Problem 14** (`Erdos14.erdos_14.parts.i` affirmatively and `Erdos14.erdos_14.parts.ii`
negatively) for the [Palomar Registry](https://palomar-registry.org/), matching
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/14.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Result

For any $A \subseteq \mathbb{N}$, let $B = \text{allUniqueSums}(A)$ be the set of natural
numbers representable in exactly one way as an unordered sum of two elements of $A$, and let
$E_A(N) = |\{1, \dots, N\} \setminus B|$. We prove the uniform lower bound
(`uniform_sqrt_lower_bound`):
$$E_A(N) \ge \frac{\sqrt{N}}{6000} \qquad \text{for all } N \ge 2 \cdot 10000^4,$$
which immediately implies:
- **Part (i) (`erdos_14.parts.i`):** $E_A(N) \gg_\varepsilon N^{1/2 - \varepsilon}$ for all
  $A \subseteq \mathbb{N}$ and $\varepsilon > 0$.
- **Part (ii) (`erdos_14.parts.ii`):** There is no $A \subseteq \mathbb{N}$ with
  $E_A(N) = o(\sqrt{N})$.

## Mathematical Source and Proof Architecture

This formalization implements the proof of **Liam Kruer and Jensen Kohlmeyer**, *A uniform
square-root lower bound for non-unique sums and a resolution of Erdős problem 14* (September 13,
2026 draft, [PDF](https://liamkruer.com/assets/work/conjectures/problems/erdos-14/paper/proof.pdf)),
via pair-counting fiber bounds (`pair_fiber_card_le_two_of_unique`), quadratic incidence bounds
(`quad_bound`), a finite scale lower bound (`finite_lower_bound` for $T \ge 10000$), and dyadic
monotonicity (`nonUniqueSumCount_mono`, `uniform_sqrt_lower_bound`).

## Scope and Verification

- Proves both Part (i) and Part (ii) in a single Palomar entry (unlike open PR #8214, which
  currently links only an external non-Palomar proof of Part (ii) with the Palomar linter
  disabled and has no formal proof link for Part (i)).
- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
