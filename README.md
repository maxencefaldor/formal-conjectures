# Erdős Problem 14 (Parts (i) and (ii))

This repository packages an independent Lean 4 / Mathlib formalization resolving **both parts
of Erdős Problem 14**, proving the affirmative Part (i) declaration (`Erdos14.erdos_14.parts.i`)
and the negative Part (ii) declaration (`Erdos14.erdos_14.parts.ii`, stating the negation of the
open existential question) for the [Palomar Registry](https://palomar-registry.org/), based on
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/14.lean`, commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`).

## Result

For any $A \subseteq \mathbb{N}$, let $B = \text{allUniqueSums}(A)$ be the set of natural
numbers representable in exactly one way as an unordered sum of two elements of $A$, and let
$E_A(N) = |\{1, \dots, N\} \setminus B|$. In `Solution.lean`, `uniform_sqrt_lower_bound`
establishes the uniform lower bound
$$E_A(N) \ge \frac{\sqrt{N}}{6000} \qquad \text{for all } N \ge 2 \cdot 10000^4,$$
which immediately implies the two compared theorems in `Challenge.lean`:
- **Part (i) (`erdos_14.parts.i`):** $E_A(N) \gg_\varepsilon N^{1/2 - \varepsilon}$ for all
  $A \subseteq \mathbb{N}$ and $\varepsilon > 0$.
- **Part (ii) (`erdos_14.parts.ii`):** There is no $A \subseteq \mathbb{N}$ with
  $E_A(N) = o(\sqrt{N})$.

## Mathematical Source and Proof Architecture

This formalization implements the informal proof of **Liam Kruer and Jensen Kohlmeyer**,
*A uniform square-root lower bound for non-unique sums and a resolution of Erdős problem 14*
(September 13, 2026 draft,
[PDF](https://liamkruer.com/assets/work/conjectures/problems/erdos-14/paper/proof.pdf)).
In `Solution.lean`, the argument proceeds in three stages:

1. **Finite-scale lower bound (`finite_lower_bound`):** For every integer $T \ge 10000$, set
   $X = T^4$, $S = A \cap [0, X]$, and $E = |\{1, \dots, 2X\} \setminus B|$. Assuming for
   contradiction that $1000 E \le T^2$:
   - *Pair-counting and prefix bounds:* Counting ordered pairs in $S \times S$ by sum fiber
     (`ordered_pair_counting`, `pair_fiber_card_le_one_of_zero`,
     `pair_fiber_card_le_two_of_unique`, `pair_fiber_card_le_card`) and solving the resulting
     quadratic inequality (`quad_bound`) gives $10 |S| \le 21 T^2$. Conversely, for every
     $n \in [M_0, X]$ with $M_0 = \lfloor X / 100 \rfloor$, the prefix $P_n = A \cap [0, n)$
     satisfies $n - 1 \le |P_n|^2 + E$ (`prefix_card_sq_ge`), yielding $T^2 \le 11 |P_n|$
     (`arith_prefix_lb`).
   - *Triple-sum identity and bad-target count:* For any $n \notin A$ that is clean (meaning
     $n - a \in B$ for all $a \in A$ with $a < n$), counting ordered triples $(a, b, c) \in P_n^3$
     with $a + b + c = n$ together with $W_n = \{(a, b) \in P_n^2 : a + 2b = n\}$ yields the
     exact identity (`triple_sum_identity`)
     $$n(|P_n| + |W_n|) = 3 \sum_{a \in P_n} a + 3 \sum_{(a, b) \in W_n} b.$$
     Grouping $n \in [M_0, X]$ by the maximum element $m \in S$ of its prefix
     $P_n = Q_m = A \cap [0, m]$, this identity allows at most $1$ clean target with $|W_n| = 0$
     per $m$, and constrains the $b$-coordinates of clean targets with $|W_n| = 1$ to a single
     residue class modulo $d$ (where $d = (|Q_m| + 1)/3$ if $3 \mid (|Q_m| + 1)$ and
     $d = |Q_m| + 1$ otherwise, so $T^2 \le 33 d$). Applying `div_class_card_le`,
     `ordered_pair_counting`, and `quad_bound` bounds the $|W_n| = 1$ family by $9T + E$ per $m$.
     Combining $n < M_0$, $n \in A$, non-clean targets $a + e$ ($a \in S$,
     $e \in [1, X] \setminus B$), and the $|W_n| \in \{0, 1\}$ families shows that at most
     $X / 50$ targets $n \in [1, X]$ have fewer than $2$ representations $a + 2b = n$ with
     $a, b \in S$ (`arith_bad_50`).
   - *Weighted generating-function contradiction (`gen_poly_contradiction`):* Let
     $z = 1 - 4 / X \in (0, 1)$ and $F(y) = \sum_{a \in S} y^a$. Fiberwise bounding of $F(y)^2$
     (`gen_poly_sq_ub`) gives $F(y)^2 \le 2 / (1 - y) + |S| E$, whence
     $F(z)^2 \le \frac{51}{100} X$, $F(z^2)^2 \le \frac{27}{100} X$, and
     $F(z) F(z^2) < \frac{38}{100} X$. On the other hand, expanding
     $F(z) F(z^2) = \sum_{a, b \in S} z^{a + 2b}$, using that all but at most $X / 50$ targets
     $n \in [1, X]$ have at least $2$ representations $a + 2b = n$, and applying $z^X \le 1/16$
     (`one_sub_four_div_pow_le`) yields $F(z) F(z^2) \ge \frac{42}{100} X$, contradicting the
     upper bound. Hence $T^2 < 1000 E$.

2. **Fourth-power scale transfer (`uniform_sqrt_lower_bound`):** For any $N \ge 2 \cdot 10000^4$,
   set $s = \lfloor \sqrt{\lfloor N / 2 \rfloor} \rfloor$ and $T = \lfloor \sqrt{s} \rfloor$.
   Then $T \ge 10000$ and $2 T^4 \le N < 2 (T + 1)^4 \le 36 T^4$, so $\sqrt{N} \le 6 T^2$.
   Combining `finite_lower_bound` at scale $2 T^4$ with monotonicity of `nonUniqueSumCount`
   (`nonUniqueSumCount_mono`) gives
   $$E_A(N) \ge E_A(2 T^4) \ge \frac{T^2}{1000} \ge \frac{\sqrt{N}}{6000}.$$

3. **Deduction of Parts (i) and (ii):** `erdos_14.parts.i` follows immediately from
   `uniform_sqrt_lower_bound` and $N^{1/2 - \varepsilon} \le \sqrt{N}$ for $N \ge 1$,
   $\varepsilon > 0$; `erdos_14.parts.ii` follows by contradicting `IsLittleO` at threshold
   $1 / 12000$.

## Scope and Verification

- Proves both the affirmative Part (i) declaration and the negative Part (ii) declaration in a single Palomar entry (unlike open PR #8214, which
  currently links only an external non-Palomar proof of Part (ii) with the Palomar linter
  disabled and has no formal proof link for Part (i)).
- Zero `sorry`, zero `native_decide`, standard axioms only (`propext`, `Classical.choice`,
  `Quot.sound`).
- Licensed under Apache-2.0.
