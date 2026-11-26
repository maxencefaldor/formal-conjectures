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
# Disproof of the Pierce-Birkhoff Conjecture

The definitions `IsSemiAlgebraic` and `IsPiecewiseMvPolynomial` and the negated statement of
`pierce_birkhoff_conjecture` match `FormalConjectures/Wikipedia/PierceBirkhoff.lean` in
`google-deepmind/formal-conjectures` at commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Pierce%E2%80%93Birkhoff_conjecture)
- [LLR26] Zehua Lai, Lek-Heng Lim, and Junyu Ren, *Pierce-Birkhoff conjecture is false*,
  [arXiv:2609.10420](https://arxiv.org/abs/2609.10420) (2026).
-/

@[expose] public section

namespace PierceBirkhoff

/--
A set is semi-algebraic in `ℝⁿ` if it can be described by a finite union of sets, each defined by
finitely many simultaneous multivariate polynomial equations and strict inequalities.
-/
def IsSemiAlgebraic {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (p₀ p₁ : ι → Finset (MvPolynomial (Fin n) ℝ)), Finite ι ∧
    S = ⋃ i, {x | (∀ p ∈ p₀ i, MvPolynomial.eval x p = 0) ∧
      ∀ p ∈ p₁ i, MvPolynomial.eval x p > 0}

open scoped Polynomial

/--
A function `f : ℝⁿ → ℝ` is piecewise polynomial if there exists a finite covering of `ℝⁿ` by
closed semi-algebraic sets such that the restriction of `f` to each set in the covering is
polynomial.
-/
def IsPiecewiseMvPolynomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set (Fin n → ℝ))
    (g : ι → MvPolynomial (Fin n) ℝ),
    Finite ι ∧
    (∀ i, IsClosed (P i)) ∧
    (∀ i, IsSemiAlgebraic (P i)) ∧
    (⋃ i, P i) = Set.univ ∧
    ∀ (i : ι), ∀ x ∈ P i, f x = MvPolynomial.eval x (g i)

/--
Disproof of the Pierce-Birkhoff conjecture: there exists `n` and a real piecewise-polynomial
function `f : ℝⁿ → ℝ` (covered by finitely many closed semi-algebraic sets on each of which `f`
agrees with a polynomial) that cannot be expressed in the finite max-of-min polynomial form
`f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j)`.
-/
theorem pierce_birkhoff_conjecture :
    ¬ ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
      IsPiecewiseMvPolynomial f →
      ∃ (ι κ : Type) (g : ι → κ → MvPolynomial (Fin n) ℝ), Finite ι ∧ Finite κ ∧
        ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j) := by
  sorry

end PierceBirkhoff
