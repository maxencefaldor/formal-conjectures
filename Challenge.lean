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
# Ben Green's Open Problem 51 at Density One Half (Sanders' Question 5.1)

The definitions `𝔽`, `𝔽₂`, and `maxCosetDim` are copied verbatim from
`FormalConjecturesForMathlib`; `guaranteedMaxCosetDim` and `green_51.one_half` are copied
verbatim from `FormalConjectures/GreensOpenProblems/51.lean` in
`google-deepmind/formal-conjectures` at commit `5bd8bfb9def462c19a87d2d275af3db3341dc727`.

*References:*
- [Gr24] [Ben Green's Open Problem 51](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.51)
- [Sa11] Tom Sanders, *Green's sumset problem at density one half*, Acta Arith. 146.1 (2011),
  91-101, Question 5.1.
- [KK26] Jensen Kohlmeyer and Liam Kruer, *Green's Open Problem 51 at Density One Half:
  Bounded Codimension in Binary Sumsets*, September 2026
  ([PDF](https://liamkruer.com/assets/work/conjectures/problems/green-51/paper/proof.pdf)).
-/

@[expose] public section

/-- `𝔽 p n` is the vector space `(Z/pZ)^n`. When `p` is prime, this is $\mathbb{F}_p^n$. -/
abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p

/-- `𝔽₂ n` is the vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

/-- The largest dimension of an affine subspace (coset) of $V$ contained in $A$. -/
noncomputable def maxCosetDim (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Set V) : ℕ :=
  sSup { Module.finrank K S.direction | (S : AffineSubspace K V) (_h : (S : Set V) ⊆ A) }

open Filter Real
open scoped Pointwise

namespace Green51

/-- The largest dimension of a coset guaranteed to be contained in $2A$ for
$A \subseteq \mathbb{F}_2^n$ with density $\alpha$. -/
noncomputable def guaranteedMaxCosetDim (n : ℕ) (α : ℝ) : ℕ :=
  sInf { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) | (A : Finset (𝔽₂ n)) (_h : A.dens ≥ α) }

/--
If $A \subset \mathbb{F}_2^n$ has density $\alpha > 1/2 - k/\sqrt{n}$, then $A + A$ contains a
coset (in fact a linear subspace) of co-dimension $O_k(1)$, answering [Sa11, Question 5.1].
-/
theorem green_51.one_half :
    ∀ (k : ℝ), 0 < k →
      ∃ (c : ℕ), ∀ᶠ (n : ℕ) in atTop,
        ∀ (α : ℝ), α > (1/2 : ℝ) - k / sqrt (n : ℝ) → α ≤ 1 →
          n ≤ guaranteedMaxCosetDim n α + c := by
  sorry

end Green51
