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
# Disproof of Firoozbakht's Conjecture on OEIS A086766

The definition `a` and the negated statement of `conjecture2` match
`FormalConjectures/OEIS/86766.lean` in `google-deepmind/formal-conjectures` at commit
`5bd8bfb9def462c19a87d2d275af3db3341dc727`. We also state the two explicit 6-digit counterexamples `a 104040 = 0` and
`a 750760 = 0`.

*Reference:* [OEIS A086766](https://oeis.org/A086766)
-/

@[expose] public section

namespace OeisA86766

/-- Sequence $a(n)$ is the smallest $r > 0$ such that the concatenation of $n$, $r$ times
with itself, multiplied by $10$ plus $1$, is prime, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let repCatVal (r : ℕ) : ℕ := n * ∑ i ∈ Finset.range r, M ^ i
    let primeCandidate (r : ℕ) : ℕ := repCatVal r * 10 + 1
    sInf {r : ℕ | 0 < r ∧ (primeCandidate r).Prime}

/-- Explicit 6-digit counterexample $n = 104040$ (not a power of $10$): $a(104040) = 0$. -/
theorem a_104040_eq_zero : a 104040 = 0 := by
  sorry

/-- Explicit 6-digit counterexample $n = 750760$ (not a power of $10$): $a(750760) = 0$. -/
theorem a_750760_eq_zero : a 750760 = 0 := by
  sorry

/--
Disproof of Farideh Firoozbakht's conjecture (OEIS A086766, Jan 7 2015): there exists a
positive integer $n$ not of the form $10^m$ with $a(n) = 0$.
-/
theorem conjecture2 :
    ¬ ∀ (n : ℕ), 0 < n → (∀ m : ℕ, n ≠ 10 ^ m) → a n ≠ 0 := by
  sorry

end OeisA86766
