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
# Ben Green's Open Problem 40: $f(2) = 1$

The notation `𝔽₂` (from `FormalConjecturesForMathlib/Data/ZMod/Fp.lean`) and the definitions
`hammingBall`, `IsCoveringSubspace`, `minDensity`, `f`, and theorem `green_40.f_two_eq_one`
are copied verbatim from `FormalConjectures/GreensOpenProblems/40.lean` in
`google-deepmind/formal-conjectures` at commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`.

*References:*
- [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)
- [KK26] Jensen Kohlmeyer and Liam Kruer, *Asymptotically optimal binary linear covering
  codes of radius two*, September 15, 2026
  ([PDF](https://liamkruer.com/assets/work/conjectures/problems/green-40/paper/proof.pdf)).
-/

@[expose] public section

/-- `𝔽 p n` is the vector space `(Z/pZ)^n`. When `p` is prime, this is $\mathbb{F}_p^n$. -/
abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p

/-- `𝔽₂ n` is the vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40

/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- The asymptotic binary linear covering density at radius $2$ satisfies $f(2) = 1$. -/
theorem green_40.f_two_eq_one : f 2 = 1 := by
  sorry

end Green40
