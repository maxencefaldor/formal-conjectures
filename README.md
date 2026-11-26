# Ben Green's Open Problem 51 at Density One Half

This repository packages an independent Lean 4 / Mathlib formalization of **Sanders' Question
5.1** (`Green51.green_51.one_half` in **Ben Green's Open Problem 51**) for the
[Palomar Registry](https://palomar-registry.org/), matching
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/GreensOpenProblems/51.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Theorem

For every $k > 0$, there exists $c \in \mathbb{N}$ (explicitly $c = \lceil 1 + 256 e k^2 \rceil$)
such that for all sufficiently large $n$ and every $A \subseteq \mathbb{F}_2^n$ of density
$\alpha > 1/2 - k / \sqrt{n}$, the sumset $A + A$ contains a linear subspace (hence a coset)
of dimension at least $n - c$.

## Mathematical Source and Proof Architecture

This formalization implements the proof of **Jensen Kohlmeyer and Liam Kruer**,
*Green's Open Problem 51 at Density One Half: Bounded Codimension in Binary Sumsets*
(September 2026 draft,
[PDF](https://liamkruer.com/assets/work/conjectures/problems/green-51/paper/proof.pdf)),
structured in five parts inside `Solution.lean`:

1. **Part 1:** Boolean cube variance and elementary ternary separator estimate.
2. **Part 2:** Walsh-Fourier analysis and the face variance identity.
3. **Part 3:** Bernoulli face averaging to extract a large low-degree Walsh coefficient.
4. **Part 4:** Fourier analysis on $\mathbb{F}_2^n$ and good linear functionals.
5. **Part 5 (`g51_subspace_codim_bound`):** Minimal covering obstruction and polynomial
   interpolation, yielding a subspace $H \subseteq A + A$ of codimension at most
   $1 + 256 e n \varepsilon^2$ whenever $|A| / 2^n \ge 1/2 - \varepsilon$ ($0 \le \varepsilon \le 1/4$).

## Scope and Verification

- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Independent Lean code written from scratch (not copied from the unchecked Lean file in
  `green-51-source.zip`).
- Licensed under Apache-2.0.
