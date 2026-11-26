/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Erdős Problem 14 (Parts (i) and (ii))

The definition `allUniqueSums` and notation `≫` are copied verbatim from
`FormalConjecturesForMathlib`; `nonUniqueSumCount`, `almostSquareRoot`, `squareRoot`,
`erdos_14.parts.i`, and the negated `erdos_14.parts.ii` match
`FormalConjectures/ErdosProblems/14.lean` in `google-deepmind/formal-conjectures` at commit
`5bd8bfb9def462c19a87d2d275af3db3341dc727`.

*References:*
- [erdosproblems.com/14](https://www.erdosproblems.com/14)
- [KK26] Liam Kruer and Jensen Kohlmeyer, *A uniform square-root lower bound for non-unique
  sums and a resolution of Erdős problem 14*, September 13, 2026
  ([PDF](https://liamkruer.com/assets/work/conjectures/problems/erdos-14/paper/proof.pdf)).
-/

@[expose] public section

/--
`allUniqueSums A` is the set of elements in `α` that can be written as the sum of exactly one
unordered pair of elements from `A`.
-/
def allUniqueSums {α : Type*} [AddCommMonoid α] (A : Set α) : Set α :=
  { n | ∃ p : α × α, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
      ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n → (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1) }

notation f " ≫ " g => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

namespace Erdos14

open Asymptotics Filter

/--
The number of integers in $\{1,\ldots,N\}$ which are not representable in exactly one way
as the sum of two elements from $A$ (either because they are not representable at all, or
because they are representable in more than one way).
-/
noncomputable def nonUniqueSumCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ (allUniqueSums A)).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  N ^ (1/2 - ε)

noncomputable def squareRoot (N : ℕ) : ℝ :=
  Real.sqrt N

/--
Erdős Problem 14, Part (i) (answer: yes): for every $A \subseteq \mathbb{N}$ and $\varepsilon > 0$,
$|\{1,\ldots,N\} \setminus B| \gg_\varepsilon N^{1/2 - \varepsilon}$.
-/
theorem erdos_14.parts.i :
    ∀ A, ∀ ε > 0, nonUniqueSumCount A ≫ almostSquareRoot ε := by
  sorry

/--
Erdős Problem 14, Part (ii) (answer: no): there is no $A \subseteq \mathbb{N}$ such that
$|\{1,\ldots,N\} \setminus B| = o(N^{1/2})$.
-/
theorem erdos_14.parts.ii :
    ¬ ∃ (A : Set ℕ), IsLittleO atTop (nonUniqueSumCount A) squareRoot := by
  sorry

end Erdos14
