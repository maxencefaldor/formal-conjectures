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
# Proof of Erdős Problem 14 (Parts (i) and (ii))

Independent Lean 4 formalization of the uniform square-root lower bound of Liam Kruer and
Jensen Kohlmeyer (2026), resolving both `Erdos14.erdos_14.parts.i` (affirmatively) and
`Erdos14.erdos_14.parts.ii` (negatively).
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

section Erdos14ProofHelpers

open Classical in
private lemma ncard_diff_eq_excCard (A : Set ℕ) (M : ℕ) :
    ((Set.Icc 1 M) \ allUniqueSums A).ncard =
      ((Finset.Icc 1 M).filter (· ∉ allUniqueSums A)).card := by
  have h : (Set.Icc 1 M \ allUniqueSums A) =
      (((Finset.Icc 1 M).filter (· ∉ allUniqueSums A)) : Set ℕ) := by
    ext x
    simp
  rw [h, Set.ncard_coe_finset]

private lemma pair_fiber_card_le_one_of_zero (B : Finset ℕ) :
    ((B ×ˢ B).filter (fun p => p.1 + p.2 = 0)).card ≤ 1 := by
  have hsub : (B ×ˢ B).filter (fun p => p.1 + p.2 = 0) ⊆ {(0, 0)} := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_singleton, Prod.ext_iff]
    omega
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma pair_fiber_card_le_two_of_unique {A : Set ℕ} {B : Finset ℕ}
    (hBA : ∀ x ∈ B, x ∈ A) {s : ℕ} (hs : s ∈ allUniqueSums A) :
    ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card ≤ 2 := by
  obtain ⟨p, -, -, -, huniq⟩ := hs
  have hsub : (B ×ˢ B).filter (fun q => q.1 + q.2 = s) ⊆ {(p.1, p.2), (p.2, p.1)} := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    have hq' := huniq q.1 (hBA _ hq.1.1) q.2 (hBA _ hq.1.2) hq.2
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    exact hq'
  calc
    ((B ×ˢ B).filter (fun q => q.1 + q.2 = s)).card
        ≤ ({(p.1, p.2), (p.2, p.1)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

private lemma pair_fiber_card_le_card (B : Finset ℕ) (s : ℕ) :
    ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card ≤ B.card := by
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_coe.mpr hp.1.1
  · intro p hp q hq heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    exact Prod.ext heq (by omega)

open Classical in
private lemma ordered_pair_counting {A : Set ℕ} {X : ℕ} {B L : Finset ℕ}
    (hBA : ∀ x ∈ B, x ∈ A)
    (hL_sub : L ⊆ Finset.Icc 1 (2 * X))
    (hmaps : ∀ a ∈ B, ∀ b ∈ B, 1 ≤ a + b → a + b ∈ L) :
    B.card ^ 2 ≤
      1 + 2 * L.card +
        B.card * ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card := by
  have hcard_sq : B.card ^ 2 = (B ×ˢ B).card := by
    rw [sq, Finset.card_product]
  rw [hcard_sq]
  have hmaps' : ∀ p ∈ B ×ˢ B, p.1 + p.2 ∈ insert 0 L := by
    intro p hp
    simp only [Finset.mem_product] at hp
    by_cases h0 : p.1 + p.2 = 0
    · simp [h0]
    · exact Finset.mem_insert_of_mem (hmaps p.1 hp.1 p.2 hp.2 (by omega))
  rw [Finset.card_eq_sum_card_fiberwise hmaps']
  have h0_not_mem : (0 : ℕ) ∉ L := by
    intro h0
    have := hL_sub h0
    simp at this
  rw [Finset.sum_insert h0_not_mem]
  have hzero : ((B ×ˢ B).filter (fun p => p.1 + p.2 = 0)).card ≤ 1 :=
    pair_fiber_card_le_one_of_zero B
  rw [← Finset.sum_filter_add_sum_filter_not L (· ∈ allUniqueSums A)]
  have hU : ∑ s ∈ L.filter (· ∈ allUniqueSums A),
      ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card ≤ 2 * L.card := by
    calc
      ∑ s ∈ L.filter (· ∈ allUniqueSums A), ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card
          ≤ ∑ _s ∈ L.filter (· ∈ allUniqueSums A), 2 := by
            refine Finset.sum_le_sum fun s hs => ?_
            exact pair_fiber_card_le_two_of_unique hBA (Finset.mem_filter.mp hs).2
      _ = (L.filter (· ∈ allUniqueSums A)).card * 2 := by simp
      _ ≤ L.card * 2 := Nat.mul_le_mul_right 2 (Finset.card_filter_le _ _)
      _ = 2 * L.card := mul_comm _ _
  have hNU : ∑ s ∈ L.filter (· ∉ allUniqueSums A),
      ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card ≤
      B.card * ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card := by
    calc
      ∑ s ∈ L.filter (· ∉ allUniqueSums A), ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card
          ≤ ∑ _s ∈ L.filter (· ∉ allUniqueSums A), B.card :=
            Finset.sum_le_sum fun s _ => pair_fiber_card_le_card B s
      _ = (L.filter (· ∉ allUniqueSums A)).card * B.card := by simp
      _ ≤ ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card * B.card := by
            refine Nat.mul_le_mul_right B.card (Finset.card_le_card ?_)
            intro s hs
            simp only [Finset.mem_filter] at hs ⊢
            exact ⟨hL_sub hs.1, hs.2⟩
      _ = B.card * ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card := mul_comm _ _
  omega

private lemma quad_bound {m D E C : ℕ} (h1 : m ^ 2 ≤ C + m * E) (h2 : C ≤ D ^ 2) :
    m ≤ D + E := by
  by_contra h
  push Not at h
  have hm : D + E + 1 ≤ m := h
  have hmul : m * (D + E + 1) ≤ m * m := Nat.mul_le_mul_left m hm
  nlinarith

open Classical in
private lemma prefix_card_sq_ge (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    n - 1 ≤
      ((Finset.range n).filter (· ∈ A)).card ^ 2 +
        ((Finset.Icc 1 (n - 1)).filter (· ∉ allUniqueSums A)).card := by
  set P := (Finset.range n).filter (· ∈ A)
  have hsplit : ((Finset.Icc 1 (n - 1)).filter (· ∈ allUniqueSums A)).card +
      ((Finset.Icc 1 (n - 1)).filter (· ∉ allUniqueSums A)).card =
      (Finset.Icc 1 (n - 1)).card := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (n - 1))
      (· ∈ allUniqueSums A) (fun _ => (1 : ℕ))
    simpa using h
  have hIcc : (Finset.Icc 1 (n - 1)).card = n - 1 := by
    simp [Nat.card_Icc]
  have hsub : (Finset.Icc 1 (n - 1)).filter (· ∈ allUniqueSums A) ⊆
      (P ×ˢ P).image (fun p => p.1 + p.2) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨p, hp1, hp2, hsum, -⟩ := hm.2
    refine Finset.mem_image.mpr ⟨p, ?_, hsum⟩
    simp only [P, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, hp1⟩, ⟨by omega, hp2⟩⟩
  have hle : ((Finset.Icc 1 (n - 1)).filter (· ∈ allUniqueSums A)).card ≤ P.card ^ 2 := by
    calc
      ((Finset.Icc 1 (n - 1)).filter (· ∈ allUniqueSums A)).card
          ≤ ((P ×ˢ P).image (fun p => p.1 + p.2)).card := Finset.card_le_card hsub
      _ ≤ (P ×ˢ P).card := Finset.card_image_le
      _ = P.card ^ 2 := by rw [Finset.card_product, sq]
  omega

open Classical in
private lemma triple_sum_identity {A : Set ℕ} {n : ℕ} (hnA : n ∉ A)
    (hclean : ∀ a ∈ A, a < n → n - a ∈ allUniqueSums A) :
    let P := (Finset.range n).filter (· ∈ A)
    let W := (P ×ˢ P).filter (fun p => p.1 + 2 * p.2 = n)
    n * (P.card + W.card) = 3 * (∑ a ∈ P, a) + 3 * (∑ p ∈ W, p.2) := by
  intro P W
  set T := ((P ×ˢ P) ×ˢ P).filter (fun t => t.1.1 + t.1.2 + t.2 = n)
  have h12 : ∑ t ∈ T, t.1.1 = ∑ t ∈ T, t.1.2 := by
    refine Finset.sum_bij (fun t _ => ((t.1.2, t.1.1), t.2)) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [T, Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨⟨⟨ht.1.1.2, ht.1.1.1⟩, ht.1.2⟩, by omega⟩
    · intro t₁ _ t₂ _ heq
      cases t₁ with | mk ab₁ c₁ =>
      cases ab₁ with | mk a₁ b₁ =>
      cases t₂ with | mk ab₂ c₂ =>
      cases ab₂ with | mk a₂ b₂ =>
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
    · intro t ht
      refine ⟨((t.1.2, t.1.1), t.2), ?_, by rfl⟩
      simp only [T, Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨⟨⟨ht.1.1.2, ht.1.1.1⟩, ht.1.2⟩, by omega⟩
    · intro t _; rfl
  have h13 : ∑ t ∈ T, t.1.1 = ∑ t ∈ T, t.2 := by
    refine Finset.sum_bij (fun t _ => ((t.2, t.1.2), t.1.1)) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [T, Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨⟨⟨ht.1.2, ht.1.1.2⟩, ht.1.1.1⟩, by omega⟩
    · intro t₁ _ t₂ _ heq
      cases t₁ with | mk ab₁ c₁ =>
      cases ab₁ with | mk a₁ b₁ =>
      cases t₂ with | mk ab₂ c₂ =>
      cases ab₂ with | mk a₂ b₂ =>
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
    · intro t ht
      refine ⟨((t.2, t.1.2), t.1.1), ?_, by rfl⟩
      simp only [T, Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨⟨⟨ht.1.2, ht.1.1.2⟩, ht.1.1.1⟩, by omega⟩
    · intro t _; rfl
  have h3T : 3 * ∑ t ∈ T, t.1.1 = n * T.card := by
    have hsum : ∑ t ∈ T, (t.1.1 + t.1.2 + t.2) = ∑ _t ∈ T, n := by
      refine Finset.sum_congr rfl fun t ht => ?_
      exact (Finset.mem_filter.mp ht).2
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← h12, ← h13] at hsum
    simp only [Finset.sum_const, smul_eq_mul] at hsum
    linarith
  let r : ℕ → ℕ := fun a => ((P ×ˢ P).filter (fun bc => a + bc.1 + bc.2 = n)).card
  let w : ℕ → ℕ := fun a => (P.filter (fun b => a + 2 * b = n)).card
  have hrw : ∀ a ∈ P, r a + w a = 2 := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have ha_lt : a < n := Finset.mem_range.mp ha'.1
    have haA : a ∈ A := ha'.2
    obtain ⟨p, hp1, hp2, hsum, huniq⟩ := hclean a haA ha_lt
    have hp1P : p.1 ∈ P := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp1⟩
      by_contra hge
      have : p.1 = n := by omega
      exact hnA (this ▸ hp1)
    have hp2P : p.2 ∈ P := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp2⟩
      by_contra hge
      have : p.2 = n := by omega
      exact hnA (this ▸ hp2)
    by_cases hpeq : p.1 = p.2
    · have hr1 : (P ×ˢ P).filter (fun bc => a + bc.1 + bc.2 = n) = {(p.1, p.1)} := by
        ext ⟨b, c⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hb, hc⟩, hbc⟩
          have hbA := (Finset.mem_filter.mp hb).2
          have hcA := (Finset.mem_filter.mp hc).2
          have := huniq b hbA c hcA (by omega)
          rw [← hpeq] at this
          rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩
          exact ⟨⟨hp1P, hp1P⟩, by omega⟩
      have hw1 : P.filter (fun b => a + 2 * b = n) = {p.1} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, hbn⟩
          have hbA := (Finset.mem_filter.mp hb).2
          have := huniq b hbA b hbA (by omega)
          rw [← hpeq] at this
          rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
        · rintro rfl
          exact ⟨hp1P, by omega⟩
      simp [r, w, hr1, hw1]
    · have hr2 : (P ×ˢ P).filter (fun bc => a + bc.1 + bc.2 = n) =
          {(p.1, p.2), (p.2, p.1)} := by
        ext ⟨b, c⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hb, hc⟩, hbc⟩
          have hbA := (Finset.mem_filter.mp hb).2
          have hcA := (Finset.mem_filter.mp hc).2
          exact huniq b hbA c hcA (by omega)
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨⟨hp1P, hp2P⟩, by omega⟩
          · exact ⟨⟨hp2P, hp1P⟩, by omega⟩
      have hw0 : P.filter (fun b => a + 2 * b = n) = ∅ := by
        ext b
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hb hbn
        have hbA := (Finset.mem_filter.mp hb).2
        have := huniq b hbA b hbA (by omega)
        rcases this with ⟨rfl, h2⟩ | ⟨h1, rfl⟩
        · exact hpeq h2
        · exact hpeq h1
      have hne : (p.1, p.2) ≠ (p.2, p.1) := by
        intro heq
        exact hpeq (Prod.mk.inj heq).1
      simp [r, w, hr2, hw0, hne]
  have hT_card : T.card = ∑ a ∈ P, r a := by
    have h1 : T.card = ∑ t ∈ (P ×ˢ P) ×ˢ P, if t.1.1 + t.1.2 + t.2 = n then 1 else 0 := by
      dsimp only [T]
      rw [Finset.card_filter]
    rw [h1, Finset.sum_product, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [r]
    rw [Finset.card_filter, Finset.sum_product]
  have hT_sum : ∑ t ∈ T, t.1.1 = ∑ a ∈ P, a * r a := by
    have h1 : ∑ t ∈ T, t.1.1 =
        ∑ t ∈ (P ×ˢ P) ×ˢ P, if t.1.1 + t.1.2 + t.2 = n then t.1.1 else 0 := by
      rw [Finset.sum_filter]
    rw [h1, Finset.sum_product, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [r]
    rw [Finset.card_filter, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  have hW_card : W.card = ∑ a ∈ P, w a := by
    have h1 : W.card = ∑ p ∈ P ×ˢ P, if p.1 + 2 * p.2 = n then 1 else 0 := by
      dsimp only [W]
      rw [Finset.card_filter]
    rw [h1, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [w]
    rw [Finset.card_filter]
  have hW_sum1 : ∑ p ∈ W, p.1 = ∑ a ∈ P, a * w a := by
    have h1 : ∑ p ∈ W, p.1 = ∑ p ∈ P ×ˢ P, if p.1 + 2 * p.2 = n then p.1 else 0 := by
      rw [Finset.sum_filter]
    rw [h1, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [w]
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hW_ab : (∑ p ∈ W, p.1) + 2 * (∑ p ∈ W, p.2) = n * W.card := by
    have h1 : ∑ p ∈ W, (p.1 + 2 * p.2) = ∑ _p ∈ W, n :=
      Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    simp only [Finset.sum_const, smul_eq_mul] at h1
    linarith
  have hsum_rw : T.card + W.card = 2 * P.card := by
    rw [hT_card, hW_card, ← Finset.sum_add_distrib]
    calc
      ∑ a ∈ P, (r a + w a) = ∑ _a ∈ P, 2 := Finset.sum_congr rfl hrw
      _ = 2 * P.card := by simp [mul_comm]
  have hsum_arw : (∑ t ∈ T, t.1.1) + (∑ p ∈ W, p.1) = 2 * ∑ a ∈ P, a := by
    rw [hT_sum, hW_sum1, ← Finset.sum_add_distrib]
    calc
      ∑ a ∈ P, (a * r a + a * w a) = ∑ a ∈ P, a * (r a + w a) := by
        refine Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a ∈ P, 2 * a := by
        refine Finset.sum_congr rfl fun a ha => by rw [hrw a ha]; ring
      _ = 2 * ∑ a ∈ P, a := by rw [← Finset.mul_sum]
  have hA : n * T.card + n * W.card = 2 * n * P.card := by nlinarith
  have hB : n * T.card + 3 * (∑ p ∈ W, p.1) = 6 * (∑ a ∈ P, a) := by linarith
  linarith

private lemma div_class_card_le (X d c : ℕ) (_hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun s => d ∣ s + c)).card ≤ X / d + 1 := by
  calc
    ((Finset.Icc 1 X).filter (fun s => d ∣ s + c)).card
        ≤ (Finset.range (X / d + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun s => s / d) ?_ ?_
          · intro s hs
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hs
            exact Finset.mem_coe.mpr (Finset.mem_range.mpr
              (Nat.lt_succ_of_le (Nat.div_le_div_right hs.1.2)))
          · intro s₁ hs₁ s₂ hs₂ hdiv
            simp only [Finset.mem_coe, Finset.mem_filter] at hs₁ hs₂
            have hmod : s₁ ≡ s₂ [MOD d] :=
              Nat.ModEq.add_right_cancel' c (by
                rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hs₁.2, Nat.mod_eq_zero_of_dvd hs₂.2])
            have h1 := Nat.div_add_mod s₁ d
            have h2 := Nat.div_add_mod s₂ d
            dsimp only at hdiv
            change s₁ % d = s₂ % d at hmod
            rw [← h1, ← h2, hdiv, hmod]
    _ = X / d + 1 := Finset.card_range _

open Classical in
private lemma gen_poly_sq_ub {A : Set ℕ} {X : ℕ} {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    let S := (Finset.Icc 0 X).filter (· ∈ A)
    let E := ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card
    (∑ a ∈ S, y ^ a) ^ 2 ≤ 2 / (1 - y) + (S.card : ℝ) * (E : ℝ) := by
  intro S E
  have hS_sub : ∀ x ∈ S, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).2
  have hsq : (∑ a ∈ S, y ^ a) ^ 2 = ∑ p ∈ S ×ˢ S, y ^ (p.1 + p.2) := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => (pow_add y p.1 p.2).symm
  rw [hsq]
  have hmaps : ∀ p ∈ S ×ˢ S, p.1 + p.2 ∈ Finset.Icc 0 (2 * X) := by
    intro p hp
    simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ s ∈ Finset.Icc 0 (2 * X),
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = s), y ^ (p.1 + p.2) =
        (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s := by
    intro s _
    calc
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = s), y ^ (p.1 + p.2)
          = ∑ _p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = s), y ^ s :=
            Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      _ = (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s := by
            simp
  rw [Finset.sum_congr rfl hfib]
  have hIcc_split : Finset.Icc 0 (2 * X) = insert 0 (Finset.Icc 1 (2 * X)) := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h0_not_mem : (0 : ℕ) ∉ Finset.Icc 1 (2 * X) := by simp
  rw [hIcc_split, Finset.sum_insert h0_not_mem]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (2 * X)) (· ∈ allUniqueSums A)]
  have hzero_le :
      (((S ×ˢ S).filter (fun p => p.1 + p.2 = 0)).card : ℝ) * y ^ 0 ≤ 2 * y ^ 0 := by
    have hc : (((S ×ˢ S).filter (fun p => p.1 + p.2 = 0)).card : ℝ) ≤ 1 := by
      exact_mod_cast pair_fiber_card_le_one_of_zero S
    nlinarith
  have hU_le :
      ∑ s ∈ (Finset.Icc 1 (2 * X)).filter (· ∈ allUniqueSums A),
        (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s ≤
      ∑ s ∈ Finset.Icc 1 (2 * X), 2 * y ^ s := by
    calc
      ∑ s ∈ (Finset.Icc 1 (2 * X)).filter (· ∈ allUniqueSums A),
          (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s
          ≤ ∑ s ∈ (Finset.Icc 1 (2 * X)).filter (· ∈ allUniqueSums A), 2 * y ^ s := by
            refine Finset.sum_le_sum fun s hs => ?_
            have hc : (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) ≤ 2 := by
              exact_mod_cast pair_fiber_card_le_two_of_unique hS_sub (Finset.mem_filter.mp hs).2
            exact mul_le_mul_of_nonneg_right hc (pow_nonneg hy0.le s)
      _ ≤ ∑ s ∈ Finset.Icc 1 (2 * X), 2 * y ^ s := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro s _ _
            positivity
  have hgeom : 2 * y ^ 0 + ∑ s ∈ Finset.Icc 1 (2 * X), 2 * y ^ s ≤ 2 / (1 - y) := by
    have hcombine : 2 * y ^ 0 + ∑ s ∈ Finset.Icc 1 (2 * X), 2 * y ^ s =
        2 * ∑ s ∈ Finset.range (2 * X + 1), y ^ s := by
      have hins := Finset.sum_insert (f := fun s : ℕ => 2 * y ^ s) h0_not_mem
      rw [← hins, ← hIcc_split, ← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext s; simp only [Finset.mem_Icc, Finset.mem_range]; omega
    rw [hcombine, geom_sum_eq hy1.ne]
    have h1my : 0 < 1 - y := sub_pos.mpr hy1
    have hpow : 0 ≤ y ^ (2 * X + 1) := pow_nonneg hy0.le _
    have hneg : (y ^ (2 * X + 1) - 1) / (y - 1) = (1 - y ^ (2 * X + 1)) / (1 - y) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hneg, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ h1my.le
    linarith
  have hNU_le :
      ∑ s ∈ (Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A),
        (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s ≤
      (S.card : ℝ) * (E : ℝ) := by
    calc
      ∑ s ∈ (Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A),
          (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s
          ≤ ∑ _s ∈ (Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A), (S.card : ℝ) := by
            refine Finset.sum_le_sum fun s _ => ?_
            have hc : (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) ≤ (S.card : ℝ) := by
              exact_mod_cast pair_fiber_card_le_card S s
            have hpow : y ^ s ≤ 1 := pow_le_one₀ hy0.le hy1.le
            calc
              (((S ×ˢ S).filter (fun p => p.1 + p.2 = s)).card : ℝ) * y ^ s
                  ≤ (S.card : ℝ) * 1 := mul_le_mul hc hpow (pow_nonneg hy0.le s) (Nat.cast_nonneg _)
              _ = (S.card : ℝ) := mul_one _
      _ = (E : ℝ) * (S.card : ℝ) := by simp [E]
      _ = (S.card : ℝ) * (E : ℝ) := mul_comm _ _
  linarith

private lemma one_sub_four_div_pow_le {X : ℕ} (hX : 4 ≤ X) :
    ((1 : ℝ) - 4 / (X : ℝ)) ^ X ≤ 1 / 16 := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have h1 : (1 : ℝ) - 4 / (X : ℝ) ≤ Real.exp (-(4 / (X : ℝ))) := by
    have := Real.add_one_le_exp (-(4 / (X : ℝ)))
    linarith
  have h0 : 0 ≤ (1 : ℝ) - 4 / (X : ℝ) := by
    rw [sub_nonneg, div_le_one hXpos]
    exact_mod_cast hX
  have hpow : ((1 : ℝ) - 4 / (X : ℝ)) ^ X ≤ Real.exp (-4) := by
    calc
      ((1 : ℝ) - 4 / (X : ℝ)) ^ X ≤ (Real.exp (-(4 / (X : ℝ)))) ^ X :=
        pow_le_pow_left₀ h0 h1 X
      _ = Real.exp ((X : ℝ) * (-(4 / (X : ℝ)))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-4) := by
        congr 1
        field_simp
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he 4
      _ = Real.exp ((4 : ℕ) * (1 : ℝ)) := (Real.exp_nat_mul 1 4).symm
      _ = Real.exp 4 := by norm_num
  have hinv : Real.exp (-4) ≤ 1 / 16 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) he4
  exact hpow.trans hinv

private lemma arith_prefix_lb {T M₀ n E p : ℕ} (hT : 10000 ≤ T)
    (hE : 1000 * E ≤ T ^ 2) (hM0 : T ^ 4 ≤ 100 * M₀ + 99) (hn : M₀ ≤ n)
    (hsq : n - 1 ≤ p ^ 2 + E) : T ^ 2 ≤ 11 * p := by
  have hT2 : 10000 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT 2
  have hT4 : T ^ 4 = T ^ 2 * T ^ 2 := by ring
  have h1 : 100 * (p ^ 2 + E) + 199 ≥ T ^ 4 := by omega
  have h2 : T ^ 4 ≤ 121 * p ^ 2 := by nlinarith
  have h3 : (T ^ 2) ^ 2 ≤ (11 * p) ^ 2 := by nlinarith
  nlinarith

private lemma arith_bad_50 {T M₀ s E b : ℕ} (hT : 10000 ≤ T)
    (hE : 1000 * E ≤ T ^ 2) (hS : 10 * s ≤ 21 * T ^ 2)
    (hM0 : 100 * M₀ ≤ T ^ 4) (hb : b ≤ M₀ + 2 * s + s * (9 * T + 2 * E)) :
    50 * b ≤ T ^ 4 := by
  have hT2 : 10000 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT 2
  have hT3 : 10000 * T ^ 3 ≤ T ^ 4 := by
    have : T ^ 4 = T * T ^ 3 := by ring
    nlinarith
  have hT4 : T ^ 4 = T ^ 2 * T ^ 2 := by ring
  have hSE : 10000 * (s * E) ≤ 21 * T ^ 4 := by
    have : (10 * s) * (1000 * E) ≤ (21 * T ^ 2) * T ^ 2 := Nat.mul_le_mul hS hE
    nlinarith
  have hST : 10 * (s * T) ≤ 21 * T ^ 3 := by
    have : (10 * s) * T ≤ (21 * T ^ 2) * T := Nat.mul_le_mul_right T hS
    nlinarith
  nlinarith

open Classical in
private lemma gen_poly_contradiction (A : Set ℕ) {T : ℕ} (hT : 10000 ≤ T)
    (hE_le : 1000 * ((Finset.Icc 1 (2 * T ^ 4)).filter (· ∉ allUniqueSums A)).card ≤ T ^ 2)
    (hS_21 : 10 * ((Finset.Icc 0 (T ^ 4)).filter (· ∈ A)).card ≤ 21 * T ^ 2)
    (hBad_50 :
      50 * ((Finset.Icc 1 (T ^ 4)).filter (fun n =>
        ((((Finset.Icc 0 (T ^ 4)).filter (· ∈ A)) ×ˢ
          ((Finset.Icc 0 (T ^ 4)).filter (· ∈ A))).filter (fun p => p.1 + 2 * p.2 = n)).card < 2)).card
        ≤ T ^ 4) : False := by
  set X : ℕ := T ^ 4
  set S : Finset ℕ := (Finset.Icc 0 X).filter (· ∈ A)
  set E : ℕ := ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card
  let W_S : ℕ → Finset (ℕ × ℕ) := fun n => (S ×ˢ S).filter (fun p => p.1 + 2 * p.2 = n)
  set Bad := (Finset.Icc 1 X).filter (fun n => (W_S n).card < 2)
  set Good := (Finset.Icc 1 X).filter (fun n => 2 ≤ (W_S n).card)
  have hX_ge : 10000 ^ 4 ≤ X := Nat.pow_le_pow_left hT 4
  set z : ℝ := 1 - 4 / (X : ℝ)
  have hXR_ge : (10000 ^ 4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge
  have hXR_pos : (0 : ℝ) < (X : ℝ) := by linarith
  have hz0 : 0 < z := by
    dsimp only [z]
    rw [sub_pos, div_lt_one hXR_pos]
    linarith
  have hz1 : z < 1 := by
    dsimp only [z]
    have : (0 : ℝ) < 4 / (X : ℝ) := by positivity
    linarith
  have hz2_0 : 0 < z ^ 2 := sq_pos_of_pos hz0
  have hz2_1 : z ^ 2 < 1 := by nlinarith
  have hSE_real : (S.card : ℝ) * (E : ℝ) ≤ 1 / 100 * (X : ℝ) := by
    have hSE_nat : 100 * (S.card * E) ≤ X := by
      have hmul : (10 * S.card) * (1000 * E) ≤ (21 * T ^ 2) * T ^ 2 :=
        Nat.mul_le_mul hS_21 hE_le
      have hX_eq : T ^ 2 * T ^ 2 = X := by simp [X]; ring
      have h1 : 10000 * (S.card * E) ≤ 21 * X := by
        calc
          10000 * (S.card * E) = (10 * S.card) * (1000 * E) := by ring
          _ ≤ (21 * T ^ 2) * T ^ 2 := hmul
          _ = 21 * (T ^ 2 * T ^ 2) := by ring
          _ = 21 * X := by rw [hX_eq]
      omega
    have hSE_r : (100 : ℝ) * ((S.card : ℝ) * (E : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hSE_nat
    linarith
  have hFz_sq : (∑ a ∈ S, z ^ a) ^ 2 ≤ 51 / 100 * (X : ℝ) := by
    have h := gen_poly_sq_ub (A := A) (X := X) hz0 hz1
    change (∑ a ∈ S, z ^ a) ^ 2 ≤ 2 / (1 - z) + (S.card : ℝ) * (E : ℝ) at h
    have h1mz : 2 / (1 - z) = (X : ℝ) / 2 := by
      dsimp only [z]
      field_simp
      ring
    rw [h1mz] at h
    linarith
  have hFz2_sq : (∑ a ∈ S, (z ^ 2) ^ a) ^ 2 ≤ 27 / 100 * (X : ℝ) := by
    have h := gen_poly_sq_ub (A := A) (X := X) hz2_0 hz2_1
    change (∑ a ∈ S, (z ^ 2) ^ a) ^ 2 ≤ 2 / (1 - z ^ 2) + (S.card : ℝ) * (E : ℝ) at h
    have h1mz2 : 2 / (1 - z ^ 2) ≤ 26 / 100 * (X : ℝ) := by
      have hden_pos : 0 < 1 - z ^ 2 := sub_pos.mpr hz2_1
      rw [div_le_iff₀ hden_pos]
      have hden_eq : 1 - z ^ 2 = (8 * (X : ℝ) - 16) / (X : ℝ) ^ 2 := by
        dsimp only [z]
        field_simp
        ring
      rw [hden_eq]
      have hstep : 2 * (X : ℝ) ^ 2 ≤ 26 / 100 * (X : ℝ) * (8 * (X : ℝ) - 16) := by nlinarith
      have hX2_pos : (0 : ℝ) < (X : ℝ) ^ 2 := sq_pos_of_pos hXR_pos
      rw [← mul_div_assoc, le_div_iff₀ hX2_pos]
      linarith
    linarith
  have hProd_nonneg : 0 ≤ (∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a) :=
    mul_nonneg (Finset.sum_nonneg fun a _ => pow_nonneg hz0.le a)
      (Finset.sum_nonneg fun a _ => pow_nonneg hz2_0.le a)
  have hProd_ub : (∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a) < 38 / 100 * (X : ℝ) := by
    have hsq_ub : ((∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a)) ^ 2 <
        (38 / 100 * (X : ℝ)) ^ 2 := by
      rw [mul_pow]
      have h1 : (∑ a ∈ S, z ^ a) ^ 2 * (∑ a ∈ S, (z ^ 2) ^ a) ^ 2 ≤
          (51 / 100 * (X : ℝ)) * (27 / 100 * (X : ℝ)) :=
        mul_le_mul hFz_sq hFz2_sq (sq_nonneg _) (by positivity)
      nlinarith
    nlinarith
  have hProd_expand : (∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a) =
      ∑ p ∈ S ×ˢ S, z ^ (p.1 + 2 * p.2) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add]
  have hProd_maps : ∀ p ∈ S ×ˢ S, p.1 + 2 * p.2 ∈ Finset.Icc 0 (3 * X) := by
    intro p hp
    simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    omega
  have hProd_ge_Good : 2 * ∑ n ∈ Good, z ^ n ≤ (∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a) := by
    rw [hProd_expand, ← Finset.sum_fiberwise_of_maps_to hProd_maps]
    have hGood_sub : Good ⊆ Finset.Icc 0 (3 * X) := by
      intro n hn
      simp only [Good, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    calc
      2 * ∑ n ∈ Good, z ^ n = ∑ n ∈ Good, 2 * z ^ n := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ Good, ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + 2 * p.2 = n), z ^ (p.1 + 2 * p.2) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hge2 : (2 : ℝ) ≤ ((W_S n).card : ℝ) := by
              exact_mod_cast (Finset.mem_filter.mp hn).2
            have hfib : ∑ p ∈ W_S n, z ^ (p.1 + 2 * p.2) = ((W_S n).card : ℝ) * z ^ n := by
              calc
                ∑ p ∈ W_S n, z ^ (p.1 + 2 * p.2) = ∑ _p ∈ W_S n, z ^ n :=
                  Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
                _ = ((W_S n).card : ℝ) * z ^ n := by simp
            change 2 * z ^ n ≤ ∑ p ∈ W_S n, z ^ (p.1 + 2 * p.2)
            rw [hfib]
            exact mul_le_mul_of_nonneg_right hge2 (pow_nonneg hz0.le n)
      _ ≤ ∑ n ∈ Finset.Icc 0 (3 * X),
            ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + 2 * p.2 = n), z ^ (p.1 + 2 * p.2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hGood_sub ?_
            intro n _ _
            exact Finset.sum_nonneg fun p _ => pow_nonneg hz0.le _
  have hIcc_split_good : ∑ n ∈ Finset.Icc 1 X, z ^ n =
      (∑ n ∈ Good, z ^ n) + (∑ n ∈ Bad, z ^ n) := by
    have hBad_eq : Bad = (Finset.Icc 1 X).filter (fun n => ¬ 2 ≤ (W_S n).card) := by
      ext n; simp only [Bad, Finset.mem_filter, not_le]
    rw [hBad_eq, Finset.sum_filter_add_sum_filter_not]
  have hBad_sum_le : ∑ n ∈ Bad, z ^ n ≤ (Bad.card : ℝ) := by
    calc
      ∑ n ∈ Bad, z ^ n ≤ ∑ _n ∈ Bad, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => pow_le_one₀ hz0.le hz1.le
      _ = (Bad.card : ℝ) := by simp
  have hGeom_Icc : ∑ n ∈ Finset.Icc 1 X, z ^ n = z * (1 - z ^ X) / (1 - z) := by
    have hshift : ∑ n ∈ Finset.Icc 1 X, z ^ n = ∑ k ∈ Finset.range X, z ^ (k + 1) := by
      refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ heq
        simp only [Finset.mem_Icc] at hn₁ hn₂
        omega
      · intro k hk
        refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩,
          by omega⟩
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        congr 1; omega
    rw [hshift]
    have hmul : ∑ k ∈ Finset.range X, z ^ (k + 1) = z * ∑ k ∈ Finset.range X, z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by rw [pow_succ']
    rw [hmul, geom_sum_eq hz1.ne]
    have hneg : (z ^ X - 1) / (z - 1) = (1 - z ^ X) / (1 - z) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hneg, mul_div_assoc]
  have hzX_le : z ^ X ≤ 1 / 16 := one_sub_four_div_pow_le (by omega)
  have hGeom_lb : 46 / 100 * (X : ℝ) ≤ 2 * ∑ n ∈ Finset.Icc 1 X, z ^ n := by
    rw [hGeom_Icc]
    have hdiv : 2 * (z * (1 - z ^ X) / (1 - z)) = (X : ℝ) / 2 * z * (1 - z ^ X) := by
      dsimp only [z]
      field_simp
      ring
    rw [hdiv]
    have hz_ge : 99 / 100 ≤ z := by
      dsimp only [z]
      have : 4 / (X : ℝ) ≤ 1 / 100 := by
        rw [div_le_div_iff₀ hXR_pos (by norm_num)]
        linarith
      linarith
    have h1mzX : 15 / 16 ≤ 1 - z ^ X := by linarith
    have hstep1 : (X : ℝ) / 2 * (99 / 100) ≤ (X : ℝ) / 2 * z := by nlinarith
    have hstep2 : (X : ℝ) / 2 * (99 / 100) * (15 / 16) ≤ (X : ℝ) / 2 * z * (1 - z ^ X) := by
      nlinarith
    linarith
  have hBad_real : (Bad.card : ℝ) ≤ 2 / 100 * (X : ℝ) := by
    have h50 : (50 : ℝ) * (Bad.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hBad_50
    linarith
  have hProd_lb : 42 / 100 * (X : ℝ) ≤ (∑ a ∈ S, z ^ a) * (∑ a ∈ S, (z ^ 2) ^ a) := by
    linarith
  linarith

open Classical in
private lemma finite_lower_bound (A : Set ℕ) {T : ℕ} (hT : 10000 ≤ T) :
    T ^ 2 < 1000 * ((Finset.Icc 1 (2 * T ^ 4)).filter (· ∉ allUniqueSums A)).card := by
  by_contra hE_le
  push Not at hE_le
  set X : ℕ := T ^ 4
  set E : ℕ := ((Finset.Icc 1 (2 * X)).filter (· ∉ allUniqueSums A)).card
  set S : Finset ℕ := (Finset.Icc 0 X).filter (· ∈ A)
  have hS_sub : ∀ x ∈ S, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).2
  have hX_ge : 10000 ^ 4 ≤ X := Nat.pow_le_pow_left hT 4
  -- Step 1: Upper bound on |S|
  have hS_sq : S.card ^ 2 ≤ 1 + 4 * X + S.card * E := by
    have h := ordered_pair_counting (A := A) (X := X) (B := S) (L := Finset.Icc 1 (2 * X))
      hS_sub (Finset.Subset.refl _) (by
        intro a ha b hb hab
        simp only [S, Finset.mem_filter, Finset.mem_Icc] at ha hb ⊢
        omega)
    have hIcc : (Finset.Icc 1 (2 * X)).card = 2 * X := by simp [Nat.card_Icc]
    rw [hIcc] at h
    change S.card ^ 2 ≤ 1 + 2 * (2 * X) + S.card * E at h
    omega
  have hS_le : S.card ≤ 2 * T ^ 2 + 1 + E :=
    quad_bound hS_sq (by
      have hX_eq : X = (T ^ 2) ^ 2 := by simp [X]; ring
      nlinarith)
  have hS_21 : 10 * S.card ≤ 21 * T ^ 2 := by
    have hT2 : 10000 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT 2
    omega
  -- Step 2: Lower bound on prefix size for n ∈ [M₀, X]
  set M₀ : ℕ := X / 100
  let P : ℕ → Finset ℕ := fun n => (Finset.range n).filter (· ∈ A)
  let W : ℕ → Finset (ℕ × ℕ) := fun n => (P n ×ˢ P n).filter (fun p => p.1 + 2 * p.2 = n)
  let Clean : ℕ → Prop := fun n => ∀ a ∈ A, a < n → n - a ∈ allUniqueSums A
  have hP_ge : ∀ n ∈ Finset.Icc M₀ X, T ^ 2 ≤ 11 * (P n).card := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hsq := prefix_card_sq_ge A hn1
    change n - 1 ≤ (P n).card ^ 2 + ((Finset.Icc 1 (n - 1)).filter (· ∉ allUniqueSums A)).card at hsq
    have hEn_le : ((Finset.Icc 1 (n - 1)).filter (· ∉ allUniqueSums A)).card ≤ E := by
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
    have hM0 : T ^ 4 ≤ 100 * M₀ + 99 := by
      have := Nat.div_add_mod (T ^ 4) 100
      have := Nat.mod_lt (T ^ 4) (by norm_num : 0 < 100)
      omega
    exact arith_prefix_lb hT hE_le hM0 hn.1 (by omega)
  -- Step 3: Prefix max decomposition and bounds on F₀, F₁
  let Q : ℕ → Finset ℕ := fun m => (Finset.Icc 0 m).filter (· ∈ A)
  let F₀ : ℕ → Finset ℕ := fun m =>
    (Finset.Icc M₀ X).filter (fun n => n ∉ A ∧ Clean n ∧ P n = Q m ∧ (W n).card = 0)
  let F₁ : ℕ → Finset ℕ := fun m =>
    (Finset.Icc M₀ X).filter (fun n => n ∉ A ∧ Clean n ∧ P n = Q m ∧ (W n).card = 1)
  have hP_eq_Q : ∀ n ∈ Finset.Icc M₀ X, ∃ m ∈ S, P n = Q m := by
    intro n hn
    have hPpos : 0 < (P n).card := by
      have := hP_ge n hn
      have hT2 : 0 < T ^ 2 := by positivity
      omega
    have hne : (P n).Nonempty := Finset.card_pos.mp hPpos
    set m := (P n).max' hne
    have hmP : m ∈ P n := Finset.max'_mem (P n) hne
    have hmP' := Finset.mem_filter.mp hmP
    have hm_lt : m < n := Finset.mem_range.mp hmP'.1
    have hn_le : n ≤ X := (Finset.mem_Icc.mp hn).2
    refine ⟨m, ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le m, by omega⟩, hmP'.2⟩
    · ext x
      simp only [P, Q, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · intro hx
        have hxP : x ∈ P n := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hx.2⟩
        exact ⟨⟨Nat.zero_le x, Finset.le_max' (P n) x hxP⟩, hx.2⟩
      · intro hx
        exact ⟨by omega, hx.2⟩
  have hF0_card : ∀ m ∈ S, (F₀ m).card ≤ 1 := by
    intro m _
    refine Finset.card_le_one.mpr fun n₁ hn₁ n₂ hn₂ => ?_
    simp only [F₀, Finset.mem_filter] at hn₁ hn₂
    have hKpos : 0 < (Q m).card := by
      have hge := hP_ge n₁ hn₁.1
      rw [hn₁.2.2.2.1] at hge
      have hT2 : 0 < T ^ 2 := by positivity
      omega
    have hid₁ := triple_sum_identity hn₁.2.1 hn₁.2.2.1
    have hid₂ := triple_sum_identity hn₂.2.1 hn₂.2.2.1
    change n₁ * ((P n₁).card + (W n₁).card) =
      3 * (∑ a ∈ P n₁, a) + 3 * (∑ p ∈ W n₁, p.2) at hid₁
    change n₂ * ((P n₂).card + (W n₂).card) =
      3 * (∑ a ∈ P n₂, a) + 3 * (∑ p ∈ W n₂, p.2) at hid₂
    have hW₁ : W n₁ = ∅ := Finset.card_eq_zero.mp hn₁.2.2.2.2
    have hW₂ : W n₂ = ∅ := Finset.card_eq_zero.mp hn₂.2.2.2.2
    rw [hn₁.2.2.2.1, hW₁] at hid₁
    rw [hn₂.2.2.2.1, hW₂] at hid₂
    simp only [Finset.card_empty, add_zero, Finset.sum_empty, mul_zero] at hid₁ hid₂
    exact Nat.eq_of_mul_eq_mul_right hKpos (hid₁.trans hid₂.symm)
  have hF1_card : ∀ m ∈ S, (F₁ m).card ≤ 9 * T + E := by
    intro m _
    by_cases hne : (F₁ m).Nonempty
    · obtain ⟨n₀, hn₀⟩ := hne
      have hn₀' := Finset.mem_filter.mp hn₀
      have hK_ge : T ^ 2 ≤ 11 * (Q m).card := by
        have := hP_ge n₀ hn₀'.1
        rwa [hn₀'.2.2.2.1] at this
      set q : ℕ := (Q m).card + 1
      set H : ℕ := ∑ x ∈ Q m, x
      set d : ℕ := if 3 ∣ q then q / 3 else q
      have h3d_ge : q ≤ 3 * d := by
        dsimp only [d]
        split_ifs with h3
        · exact (Nat.mul_div_cancel' h3).ge
        · omega
      have h33d_ge : T ^ 2 ≤ 33 * d := by omega
      have hd_pos : 0 < d := by
        have hT2 : 0 < T ^ 2 := by positivity
        omega
      have hX_div_d : X / d ≤ 33 * T ^ 2 := by
        have hmul : d * (X / d) ≤ X := Nat.mul_div_le X d
        have h1 : T ^ 2 * (X / d) ≤ (33 * d) * (X / d) := Nat.mul_le_mul_right _ h33d_ge
        have h2 : (33 * d) * (X / d) ≤ 33 * X := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left 33 hmul
        have h3 : T ^ 2 * (X / d) ≤ T ^ 2 * (33 * T ^ 2) := by
          have hX_eq : 33 * X = T ^ 2 * (33 * T ^ 2) := by simp [X]; ring
          omega
        exact Nat.le_of_mul_le_mul_left h3 (by positivity)
      let bOf : ℕ → ℕ := fun n => ∑ p ∈ W n, p.2
      have hb_prop : ∀ n ∈ F₁ m,
          bOf n ∈ A ∧ 2 * bOf n ≤ X ∧ n * q = 3 * H + 3 * bOf n ∧ d ∣ H + bOf n := by
        intro n hn
        simp only [F₁, Finset.mem_filter] at hn
        obtain ⟨hnIcc, hnA, hcl, hPQ, hWcard⟩ := hn
        obtain ⟨ab, hab⟩ := Finset.card_eq_one.mp hWcard
        have hab_mem : ab ∈ W n := hab ▸ Finset.mem_singleton_self ab
        simp only [W, Finset.mem_filter, Finset.mem_product] at hab_mem
        have hbOf_eq : bOf n = ab.2 := by simp [bOf, hab]
        have hbA : bOf n ∈ A := by
          rw [hbOf_eq]
          exact (Finset.mem_filter.mp hab_mem.1.2).2
        have h2b : 2 * bOf n ≤ X := by
          rw [hbOf_eq]
          have hnX : n ≤ X := (Finset.mem_Icc.mp hnIcc).2
          omega
        have hid := triple_sum_identity hnA hcl
        have hnq : n * q = 3 * H + 3 * bOf n := by
          change n * ((P n).card + (W n).card) =
            3 * (∑ a ∈ P n, a) + 3 * (∑ p ∈ W n, p.2) at hid
          rw [hPQ, hWcard] at hid
          exact hid
        have hdvd : d ∣ H + bOf n := by
          dsimp only [d]
          split_ifs with h3
          · have hq3 : q = 3 * (q / 3) := (Nat.mul_div_cancel' h3).symm
            have h3eq : 3 * (H + bOf n) = 3 * (n * (q / 3)) := by
              rw [hq3] at hnq
              ring_nf at hnq ⊢
              omega
            have heq : H + bOf n = n * (q / 3) := Nat.eq_of_mul_eq_mul_left (by norm_num) h3eq
            exact ⟨n, by rw [heq, mul_comm]⟩
          · have hq_dvd : q ∣ 3 * (H + bOf n) := ⟨n, by linarith⟩
            have hcop : Nat.Coprime q 3 :=
              ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
            exact hcop.dvd_of_dvd_mul_left hq_dvd
        exact ⟨hbA, h2b, hnq, hdvd⟩
      have hinj : Set.InjOn bOf (F₁ m) := by
        intro n₁ hn₁ n₂ hn₂ heq
        have hp₁ := hb_prop n₁ hn₁
        have hp₂ := hb_prop n₂ hn₂
        have hqpos : 0 < q := by omega
        have hmul : n₁ * q = n₂ * q := by rw [hp₁.2.2.1, hp₂.2.2.1, heq]
        exact Nat.eq_of_mul_eq_mul_right hqpos hmul
      set B_m := (F₁ m).image bOf
      set L_m := (Finset.Icc 1 X).filter (fun s => d ∣ s + 2 * H)
      have hcard_eq : (F₁ m).card = B_m.card := (Finset.card_image_of_injOn hinj).symm
      have hL_sub : L_m ⊆ Finset.Icc 1 (2 * X) := by
        intro s hs
        simp only [L_m, Finset.mem_filter, Finset.mem_Icc] at hs ⊢
        omega
      have hB_maps : ∀ a ∈ B_m, ∀ b ∈ B_m, 1 ≤ a + b → a + b ∈ L_m := by
        intro a ha b hb hab
        obtain ⟨n₁, hn₁, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨n₂, hn₂, rfl⟩ := Finset.mem_image.mp hb
        have hp₁ := hb_prop n₁ hn₁
        have hp₂ := hb_prop n₂ hn₂
        simp only [L_m, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hab, by omega⟩, ?_⟩
        have hadd := Nat.dvd_add hp₁.2.2.2 hp₂.2.2.2
        have heq : (H + bOf n₁) + (H + bOf n₂) = bOf n₁ + bOf n₂ + 2 * H := by ring
        rwa [heq] at hadd
      have hB_sub : ∀ x ∈ B_m, x ∈ A := by
        intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        exact (hb_prop n hn).1
      have hB_sq := ordered_pair_counting hB_sub hL_sub hB_maps
      have hL_card : L_m.card ≤ 33 * T ^ 2 + 1 :=
        (div_class_card_le X d (2 * H) hd_pos).trans (by omega)
      have hB_le : B_m.card ≤ 9 * T + E := by
        refine quad_bound hB_sq ?_
        have hT1 : 1 ≤ T := by omega
        nlinarith
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  -- Step 4: Bound all bad targets n ∈ [1, X] with g_S(n) < 2
  let W_S : ℕ → Finset (ℕ × ℕ) := fun n => (S ×ˢ S).filter (fun p => p.1 + 2 * p.2 = n)
  set Bad := (Finset.Icc 1 X).filter (fun n => (W_S n).card < 2)
  set ExcX := (Finset.Icc 1 X).filter (· ∉ allUniqueSums A)
  set Dirty := (S ×ˢ ExcX).image (fun p => p.1 + p.2)
  set Bad0 := S.biUnion F₀
  set Bad1 := S.biUnion F₁
  have hBad_sub : Bad ⊆ (((Finset.Icc 1 (M₀ - 1) ∪ S) ∪ Dirty) ∪ Bad0) ∪ Bad1 := by
    intro n hn
    simp only [Bad, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hWS⟩ := hn
    by_cases hlt : n < M₀
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ ?_)))
      simp only [Finset.mem_Icc]; omega
    · have hnIcc : n ∈ Finset.Icc M₀ X := Finset.mem_Icc.mpr ⟨by omega, hnX⟩
      by_cases hnA : n ∈ A
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ ?_)))
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.zero_le n, hnX⟩, hnA⟩
      · by_cases hcl : Clean n
        · have hPsub : P n ⊆ S := by
            intro x hx
            simp only [P, S, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hx ⊢
            exact ⟨⟨Nat.zero_le x, by omega⟩, hx.2⟩
          have hWsub : W n ⊆ W_S n := by
            intro p hp
            simp only [W, W_S, Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨⟨hPsub hp.1.1, hPsub hp.1.2⟩, hp.2⟩
          have hWlt : (W n).card < 2 := lt_of_le_of_lt (Finset.card_le_card hWsub) hWS
          obtain ⟨m, hmS, hPQ⟩ := hP_eq_Q n hnIcc
          have h01 : (W n).card = 0 ∨ (W n).card = 1 := by omega
          rcases h01 with h0 | h1
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_biUnion.mpr ⟨m, hmS, ?_⟩
            simp only [F₀, Finset.mem_filter]
            exact ⟨hnIcc, hnA, hcl, hPQ, h0⟩
          · refine Finset.mem_union_right _ ?_
            refine Finset.mem_biUnion.mpr ⟨m, hmS, ?_⟩
            simp only [F₁, Finset.mem_filter]
            exact ⟨hnIcc, hnA, hcl, hPQ, h1⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
          simp only [Clean, not_forall] at hcl
          obtain ⟨a, haA, ha_lt, hna_notU⟩ := hcl
          refine Finset.mem_image.mpr ⟨(a, n - a), ?_, by omega⟩
          simp only [Finset.mem_product, S, ExcX, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨⟨Nat.zero_le a, by omega⟩, haA⟩, ⟨⟨by omega, by omega⟩, hna_notU⟩⟩
  have hExcX_le : ExcX.card ≤ E := by
    refine Finset.card_le_card fun x hx => ?_
    simp only [ExcX, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
  have hDirty_le : Dirty.card ≤ S.card * E := by
    calc
      Dirty.card ≤ (S ×ˢ ExcX).card := Finset.card_image_le
      _ = S.card * ExcX.card := Finset.card_product _ _
      _ ≤ S.card * E := Nat.mul_le_mul_left _ hExcX_le
  have hBad0_le : Bad0.card ≤ S.card := by
    calc
      Bad0.card ≤ ∑ m ∈ S, (F₀ m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ S, 1 := Finset.sum_le_sum hF0_card
      _ = S.card := by simp
  have hBad1_le : Bad1.card ≤ S.card * (9 * T + E) := by
    calc
      Bad1.card ≤ ∑ m ∈ S, (F₁ m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ S, (9 * T + E) := Finset.sum_le_sum hF1_card
      _ = S.card * (9 * T + E) := by simp
  have hBad_card : Bad.card ≤ M₀ + 2 * S.card + S.card * (9 * T + 2 * E) := by
    have h1 := Finset.card_le_card hBad_sub
    have h2 := Finset.card_union_le (((Finset.Icc 1 (M₀ - 1) ∪ S) ∪ Dirty) ∪ Bad0) Bad1
    have h3 := Finset.card_union_le ((Finset.Icc 1 (M₀ - 1) ∪ S) ∪ Dirty) Bad0
    have h4 := Finset.card_union_le (Finset.Icc 1 (M₀ - 1) ∪ S) Dirty
    have h5 := Finset.card_union_le (Finset.Icc 1 (M₀ - 1)) S
    have hIccM0 : (Finset.Icc 1 (M₀ - 1)).card ≤ M₀ := by simp [Nat.card_Icc]
    have hlin : S.card * E + S.card * (9 * T + E) = S.card * (9 * T + 2 * E) := by ring
    omega
  have hBad_50 : 50 * Bad.card ≤ T ^ 4 :=
    arith_bad_50 hT hE_le hS_21 (Nat.mul_div_le (T ^ 4) 100) hBad_card
  exact gen_poly_contradiction A hT hE_le hS_21 hBad_50

private lemma nonUniqueSumCount_mono {A : Set ℕ} {M N : ℕ} (hMN : M ≤ N) :
    nonUniqueSumCount A M ≤ nonUniqueSumCount A N := by
  unfold nonUniqueSumCount
  exact_mod_cast Set.ncard_le_ncard
    (Set.sdiff_subset_sdiff_left (Set.Icc_subset_Icc_right hMN))
    ((Set.finite_Icc 1 N).sdiff)

private lemma uniform_sqrt_lower_bound (A : Set ℕ) {N : ℕ} (hN : 2 * 10000 ^ 4 ≤ N) :
    (1 / 6000 : ℝ) * Real.sqrt N ≤ nonUniqueSumCount A N := by
  set s := Nat.sqrt (N / 2)
  set T := Nat.sqrt s
  have hT2_le : T ^ 2 ≤ s := by simpa [sq] using Nat.sqrt_le s
  have hs2_le : s ^ 2 ≤ N / 2 := by simpa [sq] using Nat.sqrt_le (N / 2)
  have h2T4_le : 2 * T ^ 4 ≤ N := by
    have hT4_le : T ^ 4 ≤ s ^ 2 := by
      have : T ^ 4 = (T ^ 2) ^ 2 := by ring
      rw [this]
      exact Nat.pow_le_pow_left hT2_le 2
    omega
  have hs_lt : s < (T + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt s
  have hN2_lt : N / 2 < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt (N / 2)
  have hN_lt : N < 2 * (T + 1) ^ 4 := by
    have h1 : (s + 1) ^ 2 ≤ (T + 1) ^ 4 := by
      have : (T + 1) ^ 4 = ((T + 1) ^ 2) ^ 2 := by ring
      rw [this]
      exact Nat.pow_le_pow_left (Nat.succ_le_of_lt hs_lt) 2
    omega
  have hT_ge : 10000 ≤ T := by
    by_contra hlt
    push Not at hlt
    have hle : T + 1 ≤ 10000 := hlt
    have h4 : (T + 1) ^ 4 ≤ 10000 ^ 4 := Nat.pow_le_pow_left hle 4
    omega
  have hN_le_36 : (N : ℝ) ≤ (6 * (T : ℝ) ^ 2) ^ 2 := by
    have hnat : N ≤ 36 * T ^ 4 := by
      have hTp1 : T + 1 ≤ 2 * T := by omega
      have h4 : (T + 1) ^ 4 ≤ (2 * T) ^ 4 := Nat.pow_le_pow_left hTp1 4
      have h24 : (2 * T) ^ 4 = 16 * T ^ 4 := by ring
      omega
    have hr : (N : ℝ) ≤ 36 * (T : ℝ) ^ 4 := by exact_mod_cast hnat
    linarith
  have hsqrt_le : Real.sqrt N ≤ 6 * (T : ℝ) ^ 2 := by
    calc
      Real.sqrt N ≤ Real.sqrt ((6 * (T : ℝ) ^ 2) ^ 2) := Real.sqrt_le_sqrt hN_le_36
      _ = 6 * (T : ℝ) ^ 2 := Real.sqrt_sq (by positivity)
  classical
  have hfin := finite_lower_bound A hT_ge
  have hE_eq : nonUniqueSumCount A (2 * T ^ 4) =
      (((Finset.Icc 1 (2 * T ^ 4)).filter (· ∉ allUniqueSums A)).card : ℝ) := by
    unfold nonUniqueSumCount
    rw [ncard_diff_eq_excCard]
  have hfin_r : (T : ℝ) ^ 2 ≤ 1000 * nonUniqueSumCount A (2 * T ^ 4) := by
    rw [hE_eq]
    exact_mod_cast hfin.le
  have hmono : nonUniqueSumCount A (2 * T ^ 4) ≤ nonUniqueSumCount A N :=
    nonUniqueSumCount_mono h2T4_le
  linarith

end Erdos14ProofHelpers

/--
Erdős Problem 14, Part (i) (answer: yes): for every $A \subseteq \mathbb{N}$ and $\varepsilon > 0$,
$|\{1,\ldots,N\} \setminus B| \gg_\varepsilon N^{1/2 - \varepsilon}$.
-/
theorem erdos_14.parts.i :
    ∀ A, ∀ ε > 0, nonUniqueSumCount A ≫ almostSquareRoot ε := by
  intro A ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨6000, Filter.eventually_atTop.mpr ⟨2 * 10000 ^ 4, fun N hN => ?_⟩⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlb := uniform_sqrt_lower_bound A hN
  have hnonneg_E : 0 ≤ nonUniqueSumCount A N := by
    unfold nonUniqueSumCount
    exact Nat.cast_nonneg _
  have hnonneg_a : 0 ≤ almostSquareRoot ε N := by
    unfold almostSquareRoot
    exact Real.rpow_nonneg hpos.le _
  rw [Real.norm_of_nonneg hnonneg_a, Real.norm_of_nonneg hnonneg_E]
  have hrpow : almostSquareRoot ε N ≤ Real.sqrt N := by
    unfold almostSquareRoot
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  linarith


/--
Erdős Problem 14, Part (ii) (answer: no): there is no $A \subseteq \mathbb{N}$ such that
$|\{1,\ldots,N\} \setminus B| = o(N^{1/2})$.
-/
theorem erdos_14.parts.ii :
    ¬ ∃ (A : Set ℕ), IsLittleO atTop (nonUniqueSumCount A) squareRoot := by
  rintro ⟨A, hA⟩
  have hbd := hA.bound (show (0 : ℝ) < 1 / 12000 by norm_num)
  rw [Filter.eventually_atTop] at hbd
  obtain ⟨N₁, hN₁⟩ := hbd
  set N := max (2 * 10000 ^ 4) N₁
  have hN_ge : 2 * 10000 ^ 4 ≤ N := le_max_left _ _
  have hN_ge1 : N₁ ≤ N := le_max_right _ _
  have hlb := uniform_sqrt_lower_bound A hN_ge
  have hub := hN₁ N hN_ge1
  have hnonneg_E : 0 ≤ nonUniqueSumCount A N := by
    unfold nonUniqueSumCount
    exact Nat.cast_nonneg _
  have hsqrt_pos : 0 < Real.sqrt N := by
    apply Real.sqrt_pos.mpr
    have : 0 < N := by omega
    exact_mod_cast this
  unfold squareRoot at hub
  rw [Real.norm_of_nonneg hnonneg_E, Real.norm_of_nonneg hsqrt_pos.le] at hub
  linarith


end Erdos14
