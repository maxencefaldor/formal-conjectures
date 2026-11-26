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

Disproves Farideh Firoozbakht's conjecture on OEIS A086766 using two explicit 6-digit
difference-of-squares counterexamples:
- $n = 104040$: $999999 \cdot P_r = (1020 \cdot 10^{3r} - 201)(1020 \cdot 10^{3r} + 201)$.
- $n = 750760$: $999999 \cdot P_r = (2740 \cdot 10^{3r} - 2551)(2740 \cdot 10^{3r} + 2551)$,
  with $189 \mid u, 5291 \mid v$ for even $r$ and $3861 \mid u, 259 \mid v$ for odd $r$.
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

private lemma geom_sum_999999 (r : ℕ) :
    999999 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) + 1 = (10 ^ (3 * r)) ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hpow : (10 ^ 6) ^ r = (10 ^ (3 * r)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; congr 1; omega
    have hpow2 : (10 ^ (3 * (r + 1))) ^ 2 = 10 ^ 6 * (10 ^ (3 * r)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    rw [hpow, hpow2]
    omega

/-- Explicit 6-digit counterexample $n = 104040$: $a(104040) = 0$. -/
theorem a_104040_eq_zero : a 104040 = 0 := by
  have hdig : (Nat.digits 10 104040).length = 6 := by decide
  have hset : {r : ℕ | 0 < r ∧ ((104040 * ∑ i ∈ Finset.range r,
      (10 ^ (Nat.digits 10 104040).length) ^ i) * 10 + 1).Prime} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hr hprime
    rw [hdig] at hprime
    set S := ∑ i ∈ Finset.range r, (10 ^ 6) ^ i
    set p := (104040 * S) * 10 + 1
    set K := 10 ^ (3 * r)
    have hK : 1000 ≤ K := by
      calc 1000 = 10 ^ 3 := by norm_num
        _ ≤ 10 ^ (3 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hgeom : 999999 * S + 1 = K ^ 2 := geom_sum_999999 r
    have hfac : 999999 * p = (1020 * K - 201) * (1020 * K + 201) := by
      zify [show 201 ≤ 1020 * K by omega]
      have hgeomz : (999999 : ℤ) * S + 1 = (K : ℤ) ^ 2 := by exact_mod_cast hgeom
      have hpz : (p : ℤ) = 1040400 * S + 1 := by
        change (((104040 * S) * 10 + 1 : ℕ) : ℤ) = 1040400 * S + 1
        push_cast; ring
      nlinarith
    have hdvd : p ∣ (1020 * K - 201) * (1020 * K + 201) := ⟨999999, by rw [← hfac, mul_comm]⟩
    have hle : p ≤ 1020 * K + 201 := by
      rcases hprime.dvd_mul.mp hdvd with h1 | h2
      · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
      · exact Nat.le_of_dvd (by omega) h2
    have hbig : 999999 < 1020 * K - 201 := by omega
    have hlt : 999999 * (1020 * K + 201) < (1020 * K - 201) * (1020 * K + 201) :=
      Nat.mul_lt_mul_of_pos_right hbig (by omega)
    have hle2 : 999999 * p ≤ 999999 * (1020 * K + 201) := Nat.mul_le_mul_left 999999 hle
    omega
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [hset, Nat.sInf_empty]

private lemma geom_sum_mil (r : ℕ) :
    999999 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) + 1 = (10 ^ 6) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc 999999 * (∑ i ∈ Finset.range (r + 1), (10 ^ 6) ^ i) + 1
        = (999999 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) + 1) + 999999 * (10 ^ 6) ^ r := by
          rw [Finset.sum_range_succ]; ring
      _ = (10 ^ 6) ^ r + 999999 * (10 ^ 6) ^ r := by rw [ih]
      _ = (10 ^ 6) ^ (r + 1) := by rw [pow_succ]; ring

private lemma pow_mil_modEq_one (m : ℕ) (hm : (10 ^ 6) % m = 1) (k : ℕ) :
    (10 ^ 6) ^ k ≡ 1 [MOD m] := by
  have hm1 : 1 < m := by
    rcases m with _ | _ | m
    · simp at hm
    · simp at hm
    · omega
  have h1 : 10 ^ 6 ≡ 1 [MOD m] := by
    change (10 ^ 6) % m = 1 % m
    rw [hm, Nat.mod_eq_of_lt hm1]
  simpa using h1.pow k

private lemma not_prime_750760_cand (r : ℕ) (hr : 0 < r) :
    ¬ (750760 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) * 10 + 1).Prime := by
  set P := 750760 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) * 10 + 1 with hPdef
  have h10 : 10 ^ 3 ≤ 10 ^ (3 * r) := Nat.pow_le_pow_right (by omega) (by omega)
  have hge : 2551 ≤ 2740 * 10 ^ (3 * r) := by omega
  have hsq : (10 ^ 6) ^ r = (10 ^ (3 * r)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1; ring
  have hgeom := geom_sum_mil r
  have hmul : 999999 * P = (2740 * 10 ^ (3 * r) - 2551) * (2740 * 10 ^ (3 * r) + 2551) := by
    have hmul_z : (999999 : ℤ) * (P : ℤ) =
        ((2740 * (10 : ℤ) ^ (3 * r) - 2551) * (2740 * (10 : ℤ) ^ (3 * r) + 2551)) := by
      have hg : (999999 : ℤ) * ((∑ i ∈ Finset.range r, (10 ^ 6) ^ i : ℕ) : ℤ) =
          ((10 : ℤ) ^ (3 * r)) ^ 2 - 1 := by
        have h1 : (999999 : ℤ) * ((∑ i ∈ Finset.range r, (10 ^ 6) ^ i : ℕ) : ℤ) + 1 =
            ((10 : ℤ) ^ (3 * r)) ^ 2 := by
          exact_mod_cast (hsq ▸ hgeom)
        linarith
      have hPz : (P : ℤ) = 7507600 * ((∑ i ∈ Finset.range r, (10 ^ 6) ^ i : ℕ) : ℤ) + 1 := by
        rw [hPdef]; push_cast; ring
      linear_combination 7507600 * hg + 999999 * hPz
    zify [hge]
    exact hmul_z
  set u := 2740 * 10 ^ (3 * r) - 2551
  set v := 2740 * 10 ^ (3 * r) + 2551
  have hu_ge : 2737449 ≤ u := by omega
  have hv_ge : 2742551 ≤ v := by omega
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hpow : 10 ^ (3 * (k + k)) = (10 ^ 6) ^ k := by
      rw [← pow_mul]; congr 1; ring
    have hu_dvd : 189 ∣ u := by
      have hm : (10 ^ 6) ^ k ≡ 1 [MOD 189] := pow_mil_modEq_one 189 (by decide) k
      have hm2 : 2740 * 10 ^ (3 * (k + k)) ≡ 2740 * 1 [MOD 189] := by
        rw [hpow]; exact hm.mul_left 2740
      have hsub : 2740 * 10 ^ (3 * (k + k)) ≡ 2551 [MOD 189] :=
        hm2.trans (by decide : 2740 * 1 ≡ 2551 [MOD 189])
      exact (Nat.modEq_iff_dvd' hge).mp hsub.symm
    have hv_dvd : 5291 ∣ v := by
      have hm : (10 ^ 6) ^ k ≡ 1 [MOD 5291] := pow_mil_modEq_one 5291 (by decide) k
      have hm2 : 2740 * 10 ^ (3 * (k + k)) + 2551 ≡ 2740 * 1 + 2551 [MOD 5291] := by
        rw [hpow]; exact (hm.mul_left 2740).add_right 2551
      exact Nat.dvd_of_mod_eq_zero (hm2.trans (by decide : 2740 * 1 + 2551 ≡ 0 [MOD 5291]))
    obtain ⟨f1, hf1⟩ := hu_dvd
    obtain ⟨f2, hf2⟩ := hv_dvd
    have hPeq : P = f1 * f2 := by
      have : 999999 * P = 999999 * (f1 * f2) := by
        rw [hmul, hf1, hf2]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    rw [hPeq]
    exact Nat.not_prime_mul (by omega) (by omega)
  · have hpow : 10 ^ (3 * (2 * k + 1)) = 1000 * (10 ^ 6) ^ k := by
      rw [← pow_mul, show 3 * (2 * k + 1) = 3 + 6 * k by ring, pow_add]
      rfl
    have hu_dvd : 3861 ∣ u := by
      have hm : (10 ^ 6) ^ k ≡ 1 [MOD 3861] := pow_mil_modEq_one 3861 (by decide) k
      have hm2 : 2740 * 10 ^ (3 * (2 * k + 1)) ≡ 2740 * 1000 * 1 [MOD 3861] := by
        rw [hpow, ← mul_assoc]; exact hm.mul_left (2740 * 1000)
      have hsub : 2740 * 10 ^ (3 * (2 * k + 1)) ≡ 2551 [MOD 3861] :=
        hm2.trans (by decide : 2740 * 1000 * 1 ≡ 2551 [MOD 3861])
      exact (Nat.modEq_iff_dvd' hge).mp hsub.symm
    have hv_dvd : 259 ∣ v := by
      have hm : (10 ^ 6) ^ k ≡ 1 [MOD 259] := pow_mil_modEq_one 259 (by decide) k
      have hm2 : 2740 * 10 ^ (3 * (2 * k + 1)) + 2551 ≡ 2740 * 1000 * 1 + 2551 [MOD 259] := by
        rw [hpow, ← mul_assoc]; exact (hm.mul_left (2740 * 1000)).add_right 2551
      exact Nat.dvd_of_mod_eq_zero (hm2.trans (by decide : 2740 * 1000 * 1 + 2551 ≡ 0 [MOD 259]))
    obtain ⟨f1, hf1⟩ := hu_dvd
    obtain ⟨f2, hf2⟩ := hv_dvd
    have hPeq : P = f1 * f2 := by
      have : 999999 * P = 999999 * (f1 * f2) := by
        rw [hmul, hf1, hf2]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    rw [hPeq]
    exact Nat.not_prime_mul (by omega) (by omega)

/-- Explicit 6-digit counterexample $n = 750760$: $a(750760) = 0$. -/
theorem a_750760_eq_zero : a 750760 = 0 := by
  unfold a
  rw [ite_eq_right (by omega)]
  have hlen : (Nat.digits 10 750760).length = 6 := by decide
  dsimp only
  rw [hlen]
  have hempty : {r : ℕ | 0 < r ∧ (750760 * (∑ i ∈ Finset.range r, (10 ^ 6) ^ i) * 10 + 1).Prime} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact not_prime_750760_cand r
  rw [hempty, Nat.sInf_empty]

/--
Disproof of Farideh Firoozbakht's conjecture (OEIS A086766, Jan 7 2015): $n = 104040$ is
positive, not a power of $10$, and satisfies $a(104040) = 0$.
-/
theorem conjecture2 :
    ¬ ∀ (n : ℕ), 0 < n → (∀ m : ℕ, n ≠ 10 ^ m) → a n ≠ 0 := by
  intro hconj
  have hnotpow : ∀ m : ℕ, 104040 ≠ 10 ^ m := by
    intro m
    by_cases hm : m ≤ 5
    · interval_cases m <;> norm_num
    · have hge : 10 ^ 6 ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact hconj 104040 (by norm_num) hnotpow a_104040_eq_zero

end OeisA86766
