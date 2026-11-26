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
# OEIS A092243: Prime-Gap Tug-of-War Positivity Beyond $250000$

The definitions `primeGap` and `a` and theorem `conjecture1` are copied verbatim from
`FormalConjectures/OEIS/92243.lean` in `google-deepmind/formal-conjectures` at commit
`5bd8bfb9def462c19a87d2d275af3db3341dc727`.

*References:*
- [OEIS A092243](https://oeis.org/A092243)
- [OEIS A175102](https://oeis.org/A175102)
-/

@[expose] public section

namespace OeisA92243

/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \ge 1$,
where $p_i$ is the $i$-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

/--
There exists $n > 250000$ with $a(n) > 0$ (explicitly $n = 261150$, where $a(261150) = 1$).
-/
theorem conjecture1 : ∃ n > 250000, a n > 0 := by
  sorry

end OeisA92243
