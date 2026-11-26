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
# Proof of OEIS A092243 (`conjecture1`)

Pure kernel-verified Lean 4 proof (zero `native_decide`) showing `a 261150 = 1 > 0` via a
bitmask Eratosthenes sieve up to $M = 1833290$ and SWAR popcount evaluation checked by `rfl`.
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

namespace Conjecture1Proof

noncomputable def M : ℕ := 1833290
noncomputable def allMask : ℕ := (1 <<< (M + 1)) - 1

inductive PrimeTree where
  | leaf (p : ℕ)
  | node (l r : PrimeTree)

noncomputable def repBits (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, k =>
    if k == 0 then 0
    else
      let half := k / 2
      let x := repBits p fuel half
      let y := x ||| (x <<< (half * p))
      if k % 2 == 0 then y else 1 ||| (y <<< p)

noncomputable def primeMask (p : ℕ) : ℕ :=
  let start := (3 * p - 1) / 2
  let k := (M - start) / p + 1
  (repBits p 22 k) <<< start

noncomputable def PrimeTree.keepMask : PrimeTree → ℕ
  | .leaf p => allMask ^^^ primeMask p
  | .node l r => l.keepMask &&& r.keepMask

noncomputable def PrimeTree.toList : PrimeTree → List ℕ
  | .leaf p => [p]
  | .node l r => l.toList ++ r.toList

noncomputable def PrimeTree.bitmask : PrimeTree → ℕ
  | .leaf p => 1 <<< p
  | .node l r => l.bitmask ||| r.bitmask

noncomputable def PrimeTree.allValid : PrimeTree → Bool
  | .leaf p => decide (3 ≤ p ∧ p % 2 = 1 ∧ 3 * p ≤ 2 * M + 1)
  | .node l r => l.allValid && r.allValid

noncomputable def primeTree : PrimeTree :=
  .node (.node (.node (.node (.node (.node (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 7) (.leaf 11))) (.node (.node (.leaf 13) (.leaf 17)) (.node (.leaf 19) (.node (.leaf 23) (.leaf 29))))) (.node (.node (.node (.leaf 31) (.leaf 37)) (.node (.leaf 41) (.leaf 43))) (.node (.node (.leaf 47) (.leaf 53)) (.node (.leaf 59) (.node (.leaf 61) (.leaf 67)))))) (.node (.node (.node (.node (.leaf 71) (.leaf 73)) (.node (.leaf 79) (.leaf 83))) (.node (.node (.leaf 89) (.leaf 97)) (.node (.leaf 101) (.node (.leaf 103) (.leaf 107))))) (.node (.node (.node (.leaf 109) (.leaf 113)) (.node (.leaf 127) (.leaf 131))) (.node (.node (.leaf 137) (.leaf 139)) (.node (.leaf 149) (.node (.leaf 151) (.leaf 157))))))) (.node (.node (.node (.node (.node (.leaf 163) (.leaf 167)) (.node (.leaf 173) (.leaf 179))) (.node (.node (.leaf 181) (.leaf 191)) (.node (.leaf 193) (.node (.leaf 197) (.leaf 199))))) (.node (.node (.node (.leaf 211) (.leaf 223)) (.node (.leaf 227) (.leaf 229))) (.node (.node (.leaf 233) (.leaf 239)) (.node (.leaf 241) (.node (.leaf 251) (.leaf 257)))))) (.node (.node (.node (.node (.leaf 263) (.leaf 269)) (.node (.leaf 271) (.leaf 277))) (.node (.node (.leaf 281) (.leaf 283)) (.node (.leaf 293) (.node (.leaf 307) (.leaf 311))))) (.node (.node (.node (.leaf 313) (.leaf 317)) (.node (.leaf 331) (.node (.leaf 337) (.leaf 347)))) (.node (.node (.leaf 349) (.leaf 353)) (.node (.leaf 359) (.node (.leaf 367) (.leaf 373)))))))) (.node (.node (.node (.node (.node (.node (.leaf 379) (.leaf 383)) (.node (.leaf 389) (.leaf 397))) (.node (.node (.leaf 401) (.leaf 409)) (.node (.leaf 419) (.node (.leaf 421) (.leaf 431))))) (.node (.node (.node (.leaf 433) (.leaf 439)) (.node (.leaf 443) (.leaf 449))) (.node (.node (.leaf 457) (.leaf 461)) (.node (.leaf 463) (.node (.leaf 467) (.leaf 479)))))) (.node (.node (.node (.node (.leaf 487) (.leaf 491)) (.node (.leaf 499) (.leaf 503))) (.node (.node (.leaf 509) (.leaf 521)) (.node (.leaf 523) (.node (.leaf 541) (.leaf 547))))) (.node (.node (.node (.leaf 557) (.leaf 563)) (.node (.leaf 569) (.leaf 571))) (.node (.node (.leaf 577) (.leaf 587)) (.node (.leaf 593) (.node (.leaf 599) (.leaf 601))))))) (.node (.node (.node (.node (.node (.leaf 607) (.leaf 613)) (.node (.leaf 617) (.leaf 619))) (.node (.node (.leaf 631) (.leaf 641)) (.node (.leaf 643) (.node (.leaf 647) (.leaf 653))))) (.node (.node (.node (.leaf 659) (.leaf 661)) (.node (.leaf 673) (.leaf 677))) (.node (.node (.leaf 683) (.leaf 691)) (.node (.leaf 701) (.node (.leaf 709) (.leaf 719)))))) (.node (.node (.node (.node (.leaf 727) (.leaf 733)) (.node (.leaf 739) (.leaf 743))) (.node (.node (.leaf 751) (.leaf 757)) (.node (.leaf 761) (.node (.leaf 769) (.leaf 773))))) (.node (.node (.node (.leaf 787) (.leaf 797)) (.node (.leaf 809) (.node (.leaf 811) (.leaf 821)))) (.node (.node (.leaf 823) (.leaf 827)) (.node (.leaf 829) (.node (.leaf 839) (.leaf 853))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 857) (.leaf 859)) (.node (.leaf 863) (.leaf 877))) (.node (.node (.leaf 881) (.leaf 883)) (.node (.leaf 887) (.node (.leaf 907) (.leaf 911))))) (.node (.node (.node (.leaf 919) (.leaf 929)) (.node (.leaf 937) (.leaf 941))) (.node (.node (.leaf 947) (.leaf 953)) (.node (.leaf 967) (.node (.leaf 971) (.leaf 977)))))) (.node (.node (.node (.node (.leaf 983) (.leaf 991)) (.node (.leaf 997) (.leaf 1009))) (.node (.node (.leaf 1013) (.leaf 1019)) (.node (.leaf 1021) (.node (.leaf 1031) (.leaf 1033))))) (.node (.node (.node (.leaf 1039) (.leaf 1049)) (.node (.leaf 1051) (.leaf 1061))) (.node (.node (.leaf 1063) (.leaf 1069)) (.node (.leaf 1087) (.node (.leaf 1091) (.leaf 1093))))))) (.node (.node (.node (.node (.node (.leaf 1097) (.leaf 1103)) (.node (.leaf 1109) (.leaf 1117))) (.node (.node (.leaf 1123) (.leaf 1129)) (.node (.leaf 1151) (.node (.leaf 1153) (.leaf 1163))))) (.node (.node (.node (.leaf 1171) (.leaf 1181)) (.node (.leaf 1187) (.leaf 1193))) (.node (.node (.leaf 1201) (.leaf 1213)) (.node (.leaf 1217) (.node (.leaf 1223) (.leaf 1229)))))) (.node (.node (.node (.node (.leaf 1231) (.leaf 1237)) (.node (.leaf 1249) (.leaf 1259))) (.node (.node (.leaf 1277) (.leaf 1279)) (.node (.leaf 1283) (.node (.leaf 1289) (.leaf 1291))))) (.node (.node (.node (.leaf 1297) (.leaf 1301)) (.node (.leaf 1303) (.node (.leaf 1307) (.leaf 1319)))) (.node (.node (.leaf 1321) (.leaf 1327)) (.node (.leaf 1361) (.node (.leaf 1367) (.leaf 1373)))))))) (.node (.node (.node (.node (.node (.node (.leaf 1381) (.leaf 1399)) (.node (.leaf 1409) (.leaf 1423))) (.node (.node (.leaf 1427) (.leaf 1429)) (.node (.leaf 1433) (.node (.leaf 1439) (.leaf 1447))))) (.node (.node (.node (.leaf 1451) (.leaf 1453)) (.node (.leaf 1459) (.leaf 1471))) (.node (.node (.leaf 1481) (.leaf 1483)) (.node (.leaf 1487) (.node (.leaf 1489) (.leaf 1493)))))) (.node (.node (.node (.node (.leaf 1499) (.leaf 1511)) (.node (.leaf 1523) (.leaf 1531))) (.node (.node (.leaf 1543) (.leaf 1549)) (.node (.leaf 1553) (.node (.leaf 1559) (.leaf 1567))))) (.node (.node (.node (.leaf 1571) (.leaf 1579)) (.node (.leaf 1583) (.leaf 1597))) (.node (.node (.leaf 1601) (.leaf 1607)) (.node (.leaf 1609) (.node (.leaf 1613) (.leaf 1619))))))) (.node (.node (.node (.node (.node (.leaf 1621) (.leaf 1627)) (.node (.leaf 1637) (.leaf 1657))) (.node (.node (.leaf 1663) (.leaf 1667)) (.node (.leaf 1669) (.node (.leaf 1693) (.leaf 1697))))) (.node (.node (.node (.leaf 1699) (.leaf 1709)) (.node (.leaf 1721) (.leaf 1723))) (.node (.node (.leaf 1733) (.leaf 1741)) (.node (.leaf 1747) (.node (.leaf 1753) (.leaf 1759)))))) (.node (.node (.node (.node (.leaf 1777) (.leaf 1783)) (.node (.leaf 1787) (.leaf 1789))) (.node (.node (.leaf 1801) (.leaf 1811)) (.node (.leaf 1823) (.node (.leaf 1831) (.leaf 1847))))) (.node (.node (.node (.leaf 1861) (.leaf 1867)) (.node (.leaf 1871) (.node (.leaf 1873) (.leaf 1877)))) (.node (.node (.leaf 1879) (.leaf 1889)) (.node (.leaf 1901) (.node (.leaf 1907) (.leaf 1913)))))))))

noncomputable def sieveS : ℕ :=
  (allMask - 1) &&& primeTree.keepMask

noncomputable def tinyPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

noncomputable def hasTinyDivisor (q : ℕ) : Bool :=
  tinyPrimes.any fun d => decide (d < q) && (q % d == 0)

noncomputable def checkInterval (mask : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, lo, hi => decide (hi ≤ lo)
  | fuel + 1, lo, hi =>
    if hi ≤ lo then true
    else if lo + 1 == hi then mask.testBit lo || hasTinyDivisor lo
    else
      let mid := (lo + hi) / 2
      checkInterval mask fuel lo mid && checkInterval mask fuel mid hi

structure GapState where
  rem : ℕ
  bLt : ℕ
  gLt : ℕ
  inc : ℕ
  dec : ℕ

noncomputable def gapStep (S : ℕ) (st : GapState) (d : ℕ) : GapState :=
  let gd := st.rem &&& (S >>> d)
  let bd := gd <<< d
  { rem := st.rem ^^^ gd,
     bLt := st.bLt ||| bd,
     gLt := st.gLt ||| gd,
     inc := st.inc ||| (gd &&& st.bLt),
     dec := st.dec ||| (bd &&& st.gLt) }

noncomputable def gapLoop (S : ℕ) (st : GapState) : ℕ → ℕ → GapState
  | 0, _ => st
  | fuel + 1, d => gapLoop S (gapStep S st d) fuel (d + 1)

noncomputable def swarMaskLoop (cur : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => cur
  | r + 1, span => swarMaskLoop (cur ||| (cur <<< span)) r (2 * span)

noncomputable def swarMasks : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, w => (w, swarMaskLoop ((1 <<< w) - 1) k (2 * w)) :: swarMasks k (2 * w)

noncomputable def swarApply (masks : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  masks.foldl (fun acc wm => (acc &&& wm.2) + ((acc >>> wm.1) &&& wm.2)) x

noncomputable def swarLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | r + 1, w, x =>
    let mask := swarMaskLoop ((1 <<< w) - 1) r (2 * w)
    swarLoop r (2 * w) ((x &&& mask) + ((x >>> w) &&& mask))

noncomputable def computeAll : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let S := sieveS
  let st0 : GapState := { rem := S ^^^ (1 <<< M), bLt := 0, gLt := 0, inc := 0, dec := 0 }
  let st := gapLoop S st0 74 1
  let masks := swarMasks 21 1
  (st.rem, S >>> M, swarApply masks S, swarApply masks st.inc, swarApply masks st.dec)

-- Pure kernel-evaluated computational facts (zero native_decide!)
theorem primeTree_allValid : primeTree.allValid = true := by rfl
theorem primeTree_complete_check : checkInterval primeTree.bitmask 12 3 1915 = true := by rfl
set_option maxRecDepth 2000 in
theorem computeAll_eq : computeAll = (0, 1, 261150, 126043, 126043) := by rfl

/-! ### Part 1: Sieve Bitmask Correctness -/

lemma lt_two_pow_of_testBit {x n : ℕ} (h : ∀ i, n ≤ i → x.testBit i = false) : x < 2 ^ n := by
  have heq : x % 2 ^ n = x := Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · simp [hi]
    · simp [hi, h i (by omega)]
  rw [← heq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma testBit_add_mul_two_pow {a b n : ℕ} (ha : a < 2 ^ n) (i : ℕ) :
    (a + b * 2 ^ n).testBit i = if i < n then a.testBit i else b.testBit (i - n) := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ ha]

noncomputable def geomSum (p k : ℕ) : ℕ := ∑ j ∈ Finset.range k, 2 ^ (j * p)

lemma geomSum_mul (p : ℕ) (hp : 0 < p) (k : ℕ) :
    (2 ^ p - 1) * geomSum p k = 2 ^ (k * p) - 1 := by
  induction k with
  | zero => simp [geomSum]
  | succ k ih =>
    rw [geomSum, Finset.sum_range_succ]
    change (2 ^ p - 1) * (geomSum p k + 2 ^ (k * p)) = 2 ^ ((k + 1) * p) - 1
    rw [Nat.mul_add, ih, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add]
    have h1 : 1 ≤ 2 ^ (k * p) := Nat.one_le_two_pow
    have h2 : 2 ^ (k * p) ≤ 2 ^ (p + k * p) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : p + k * p = (k + 1) * p := by ring
    rw [h3] at h2 ⊢
    omega

lemma geom_div (p : ℕ) (hp : 0 < p) (k : ℕ) :
    (2 ^ (k * p) - 1) / (2 ^ p - 1) = geomSum p k := by
  have hpos : 0 < 2 ^ p - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  rw [← geomSum_mul p hp k, Nat.mul_div_cancel_left _ hpos]

lemma geomSum_lt (p : ℕ) (hp : 0 < p) (k : ℕ) : geomSum p k < 2 ^ (k * p) := by
  have h1 : 1 ≤ 2 ^ p - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have h2 : geomSum p k ≤ (2 ^ p - 1) * geomSum p k := Nat.le_mul_of_pos_left _ h1
  rw [geomSum_mul p hp k] at h2
  have h3 : 0 < 2 ^ (k * p) := Nat.two_pow_pos _
  omega

lemma testBit_geomSum (p : ℕ) (hp : 0 < p) (k m : ℕ) :
    (geomSum p k).testBit m = decide (m < k * p ∧ p ∣ m) := by
  induction k with
  | zero => simp [geomSum]
  | succ k ih =>
    have hstep : geomSum p (k + 1) = geomSum p k + 1 * 2 ^ (k * p) := by
      simp [geomSum, Finset.sum_range_succ]
    rw [hstep, testBit_add_mul_two_pow (geomSum_lt p hp k)]
    by_cases hm : m < k * p
    · rw [ite_eq_left hm, ih]
      have hlt : m < (k + 1) * p := by
        have : k * p + p = (k + 1) * p := by ring
        omega
      simp [hm, hlt]
    · rw [ite_eq_right hm]
      have h1 : (1 : ℕ).testBit (m - k * p) = decide (m = k * p) := by
        rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
        by_cases heq : m = k * p
        · simp [heq]
        · simp only [heq, decide_false, decide_eq_false_iff_not]; omega
      rw [h1]
      by_cases heq : m = k * p
      · subst heq
        have hlt : k * p < (k + 1) * p := by
          have : (k + 1) * p = k * p + p := by ring
          omega
        simp [hlt, dvd_mul_left]
      · rw [decide_eq_false heq, eq_comm, decide_eq_false_iff_not]
        rintro ⟨hlt, hdvd⟩
        rcases hdvd with ⟨q, rfl⟩
        have h1' : k * p < p * q := by omega
        have h2' : p * q < (k + 1) * p := hlt
        have hq1 : k < q := by nlinarith
        have hq2 : q < k + 1 := by nlinarith
        omega

lemma repBits_eq_geomSum (p : ℕ) (hp : 0 < p) :
    ∀ fuel k, k < 2 ^ fuel → repBits p fuel k = geomSum p k
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp [repBits, geomSum]
  | fuel + 1, k, hk => by
    unfold repBits
    by_cases hk0 : k = 0
    · subst hk0
      simp [geomSum]
    · have hk_beq : (k == 0) = false := beq_false_of_ne hk0
      rw [hk_beq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hhalf_lt : k / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have hx : repBits p fuel (k / 2) = geomSum p (k / 2) :=
        repBits_eq_geomSum p hp fuel (k / 2) hhalf_lt
      rw [hx]
      have hy : (geomSum p (k / 2) ||| (geomSum p (k / 2) <<< (k / 2 * p))) =
          geomSum p (2 * (k / 2)) := by
        apply Nat.eq_of_testBit_eq
        intro m
        rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_geomSum p hp, testBit_geomSum p hp,
          testBit_geomSum p hp]
        have hmul2 : 2 * (k / 2) * p = k / 2 * p + k / 2 * p := by ring
        by_cases hlow : m < k / 2 * p
        · have hge : ¬ (k / 2 * p ≤ m) := by omega
          have hlt2 : m < 2 * (k / 2) * p := by omega
          simp [hlow, hge, hlt2]
        · have hge : k / 2 * p ≤ m := by omega
          have hdvd_iff : p ∣ (m - k / 2 * p) ↔ p ∣ m := by
            have hkp : p ∣ k / 2 * p := dvd_mul_left p (k / 2)
            constructor
            · intro hd
              have hadd : m = (m - k / 2 * p) + k / 2 * p := by omega
              rw [hadd]
              exact dvd_add hd hkp
            · intro hd
              exact Nat.dvd_sub hd hkp
          have hlt_iff : m - k / 2 * p < k / 2 * p ↔ m < 2 * (k / 2) * p := by omega
          simp [hlow, hge, hlt_iff, hdvd_iff]
      rw [hy]
      by_cases heven : k % 2 = 0
      · have hmod_beq : (k % 2 == 0) = true := beq_iff_eq.mpr heven
        rw [hmod_beq]
        simp only [↓reduceIte]
        have h2 : 2 * (k / 2) = k := by omega
        rw [h2]
      · have hmod_beq : (k % 2 == 0) = false := beq_false_of_ne heven
        rw [hmod_beq]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have h2 : k = 2 * (k / 2) + 1 := by omega
        apply Nat.eq_of_testBit_eq
        intro m
        rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_geomSum p hp, testBit_geomSum p hp]
        have h1bit : (1 : ℕ).testBit m = decide (m = 0) := by
          rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
          simp [eq_comm]
        rw [h1bit]
        have hmul_k : k * p = 2 * (k / 2) * p + p := by
          conv_lhs => rw [h2]
          ring
        by_cases hm0 : m = 0
        · subst hm0
          have hkp_pos : 0 < k * p := Nat.mul_pos (by omega) hp
          simp [hkp_pos]
        · have hdvd_iff : p ≤ m → (p ∣ (m - p) ↔ p ∣ m) := fun hpm => by
            constructor
            · intro hd
              have hadd : m = (m - p) + p := by omega
              rw [hadd]
              exact dvd_add hd (dvd_refl p)
            · intro hd
              exact Nat.dvd_sub hd (dvd_refl p)
          by_cases hpm : p ≤ m
          · have hlt_iff : m - p < 2 * (k / 2) * p ↔ m < k * p := by omega
            simp [hm0, hpm, hlt_iff, hdvd_iff hpm]
          · have hnotdvd : ¬ (p ∣ m) := fun hd =>
              hpm (Nat.le_of_dvd (by omega) hd)
            simp [hm0, hpm, hnotdvd]

lemma testBit_primeMask (p : ℕ) (hp3 : 3 ≤ p) (hp_odd : p % 2 = 1) (hp_le : 3 * p ≤ 2 * M + 1)
    (i : ℕ) (hi : i ≤ M) :
    (primeMask p).testBit i = true ↔ (p ∣ (2 * i + 1) ∧ p < 2 * i + 1) := by
  unfold primeMask
  dsimp only
  set start := (3 * p - 1) / 2
  set k := (M - start) / p + 1
  have hstart_eq : 2 * start + 1 = 3 * p := by omega
  have hstart_le : start ≤ M := by omega
  have hp_pos : 0 < p := by omega
  have hk_lt : k < 2 ^ 22 := by
    have h1 : (M - start) / p ≤ M - start := Nat.div_le_self _ _
    have hM : M = 1833290 := rfl
    omega
  have hrep : repBits p 22 k = geomSum p k := repBits_eq_geomSum p hp_pos 22 k hk_lt
  rw [hrep, Nat.testBit_shiftLeft, testBit_geomSum p hp_pos]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  have hlt_kp : i - start < k * p := by
    have h1 : M - start < k * p := by
      have hk_eq : k = (M - start) / p + 1 := rfl
      rw [hk_eq]
      have := Nat.div_add_mod (M - start) p
      have := Nat.mod_lt (M - start) hp_pos
      nlinarith
    omega
  constructor
  · rintro ⟨hsi, _, hdvd⟩
    have h2i : 2 * i + 1 = 2 * (i - start) + 3 * p := by omega
    refine ⟨?_, by omega⟩
    rw [h2i]
    exact dvd_add (dvd_mul_of_dvd_right hdvd 2) (dvd_mul_left p 3)
  · rintro ⟨hdvd, hlt⟩
    rcases hdvd with ⟨q, hq⟩
    have hq2 : 2 ≤ q := by nlinarith
    have hq_odd : q % 2 = 1 := by
      by_contra hq_even
      have hq0 : q % 2 = 0 := by omega
      have : (p * q) % 2 = 0 := by
        rw [Nat.mul_mod, hq0, Nat.mul_zero, Nat.zero_mod]
      omega
    have hq3 : 3 ≤ q := by omega
    have hsi : start ≤ i := by nlinarith
    refine ⟨hsi, hlt_kp, ?_⟩
    have h2sub : 2 * (i - start) = p * (q - 3) := by
      have : 2 * (i - start) + 3 * p = p * q := by omega
      have : p * (q - 3) + 3 * p = p * q := by
        rw [Nat.mul_sub_left_distrib]
        have : p * 3 ≤ p * q := Nat.mul_le_mul_left p hq3
        omega
      omega
    have hcop : Nat.Coprime p 2 := by
      rw [Nat.coprime_two_right]
      exact Nat.odd_iff.mpr hp_odd
    exact hcop.dvd_of_dvd_mul_left ⟨q - 3, h2sub⟩

lemma PrimeTree.allValid_spec (t : PrimeTree) (h : t.allValid = true) :
    ∀ p ∈ t.toList, 3 ≤ p ∧ p % 2 = 1 ∧ 3 * p ≤ 2 * M + 1 := by
  induction t with
  | leaf p =>
    simp only [PrimeTree.allValid, decide_eq_true_eq, PrimeTree.toList, List.mem_singleton] at h ⊢
    rintro _ rfl
    exact h
  | node l r ihl ihr =>
    simp only [PrimeTree.allValid, Bool.and_eq_true, PrimeTree.toList, List.mem_append] at h ⊢
    rintro p (hp | hp)
    · exact ihl h.1 p hp
    · exact ihr h.2 p hp

lemma PrimeTree.testBit_bitmask_mem (t : PrimeTree) (q : ℕ) (h : t.bitmask.testBit q = true) :
    q ∈ t.toList := by
  induction t with
  | leaf p =>
    simp only [PrimeTree.bitmask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
      decide_eq_true_eq, PrimeTree.toList, List.mem_singleton] at h ⊢
    exact h.symm
  | node l r ihl ihr =>
    simp only [PrimeTree.bitmask, Nat.testBit_or, Bool.or_eq_true, PrimeTree.toList,
      List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

lemma checkInterval_spec (mask : ℕ) : ∀ fuel lo hi,
    checkInterval mask fuel lo hi = true →
    ∀ q, lo ≤ q → q < hi → mask.testBit q = true ∨ hasTinyDivisor q = true
  | 0, lo, hi, h, q, hlo, hhi => by
    simp only [checkInterval, decide_eq_true_eq] at h
    omega
  | fuel + 1, lo, hi, h, q, hlo, hhi => by
    unfold checkInterval at h
    split_ifs at h with h1 h2
    · omega
    · have hq : q = lo := by
        simp only [beq_iff_eq] at h2
        omega
      subst hq
      simpa [Bool.or_eq_true] using h
    · simp only [Bool.and_eq_true] at h
      set mid := (lo + hi) / 2
      by_cases hqm : q < mid
      · exact checkInterval_spec mask fuel lo mid h.1 q hlo hqm
      · exact checkInterval_spec mask fuel mid hi h.2 q (by omega) hhi

lemma not_prime_of_hasTinyDivisor {q : ℕ} (h : hasTinyDivisor q = true) : ¬ q.Prime := by
  simp only [hasTinyDivisor, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ⟨d, hd_mem, hd_lt, hd_mod⟩
  have hd_ge2 : 2 ≤ d := by
    have : ∀ x ∈ tinyPrimes, 2 ≤ x := by decide
    exact this d hd_mem
  have hdvd : d ∣ q := Nat.dvd_of_mod_eq_zero hd_mod
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd d hdvd with h1 | h2 <;> omega

lemma primeTree_complete (q : ℕ) (hq3 : 3 ≤ q) (hq1914 : q ≤ 1914) (hq : q.Prime) :
    q ∈ primeTree.toList := by
  have h := checkInterval_spec primeTree.bitmask 12 3 1915 primeTree_complete_check q hq3 (by omega)
  rcases h with hbit | hdiv
  · exact primeTree.testBit_bitmask_mem q hbit
  · exact absurd hq (not_prime_of_hasTinyDivisor hdiv)

lemma PrimeTree.testBit_keepMask (t : PrimeTree)
    (ht : ∀ p ∈ t.toList, 3 ≤ p ∧ p % 2 = 1 ∧ 3 * p ≤ 2 * M + 1)
    (i : ℕ) (hi : i ≤ M) :
    t.keepMask.testBit i = true ↔ ∀ p ∈ t.toList, ¬ (p ∣ (2 * i + 1) ∧ p < 2 * i + 1) := by
  induction t with
  | leaf p =>
    have hp := ht p (by simp [PrimeTree.toList])
    have hall : allMask.testBit i = true := by
      simp only [allMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one,
        decide_eq_true_eq]
      omega
    simp only [PrimeTree.keepMask, Nat.testBit_xor, hall, Bool.true_bne, Bool.not_eq_true',
      PrimeTree.toList, List.mem_singleton, forall_eq]
    rw [← Bool.not_eq_true, testBit_primeMask p hp.1 hp.2.1 hp.2.2 i hi]
  | node l r ihl ihr =>
    have htl : ∀ p ∈ l.toList, 3 ≤ p ∧ p % 2 = 1 ∧ 3 * p ≤ 2 * M + 1 :=
      fun p hp => ht p (by simp [PrimeTree.toList, hp])
    have htr : ∀ p ∈ r.toList, 3 ≤ p ∧ p % 2 = 1 ∧ 3 * p ≤ 2 * M + 1 :=
      fun p hp => ht p (by simp [PrimeTree.toList, hp])
    simp only [PrimeTree.keepMask, Nat.testBit_and, Bool.and_eq_true, ihl htl, ihr htr,
      PrimeTree.toList, List.mem_append, or_imp, forall_and]

lemma testBit_allMask_sub_one (i : ℕ) :
    (allMask - 1).testBit i = decide (1 ≤ i ∧ i ≤ M) := by
  have h1 : allMask - 1 = (2 ^ M - 1) <<< 1 := by
    simp only [allMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
    have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    omega
  rw [h1, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi1 : 1 ≤ i <;> by_cases hiM : i ≤ M <;> simp [hi1, hiM] <;> omega

lemma sieveS_testBit_false_of_gt (i : ℕ) (hi : M < i) : sieveS.testBit i = false := by
  simp only [sieveS, Nat.testBit_and, testBit_allMask_sub_one]
  have : ¬ (1 ≤ i ∧ i ≤ M) := by omega
  simp [this]

lemma sieveS_lt : sieveS < 2 ^ (M + 1) :=
  lt_two_pow_of_testBit fun i hi => sieveS_testBit_false_of_gt i (by omega)

lemma sieveS_testBit_iff (i : ℕ) (hi : i ≤ M) :
    sieveS.testBit i = true ↔ (2 * i + 1).Prime := by
  have hvalid := primeTree.allValid_spec primeTree_allValid
  rw [sieveS, Nat.testBit_and, Bool.and_eq_true, testBit_allMask_sub_one, decide_eq_true_eq,
    primeTree.testBit_keepMask hvalid i hi]
  constructor
  · rintro ⟨⟨hi1, _⟩, hnodiv⟩
    by_contra hnotp
    set n := 2 * i + 1
    have hn2 : n ≠ 1 := by omega
    have hq_prime : n.minFac.Prime := Nat.minFac_prime hn2
    have hq_sq : n.minFac * n.minFac ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) hnotp
      rwa [sq] at this
    have hq_le : n.minFac ≤ 1914 := by
      have : n ≤ 3666581 := by
        show 2 * i + 1 ≤ 3666581
        unfold M at hi
        omega
      nlinarith
    have hq_dvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hq_ne2 : n.minFac ≠ 2 := by
      intro h2
      rw [h2] at hq_dvd
      omega
    have hq_ge3 : 3 ≤ n.minFac := by
      have := hq_prime.two_le
      omega
    have hq_mem : n.minFac ∈ primeTree.toList := primeTree_complete n.minFac hq_ge3 hq_le hq_prime
    have hq_lt : n.minFac < n := by nlinarith
    exact hnodiv n.minFac hq_mem ⟨hq_dvd, hq_lt⟩
  · intro hp
    refine ⟨⟨?_, hi⟩, ?_⟩
    · have := hp.two_le
      omega
    · intro p hp_mem ⟨hdvd, hlt⟩
      have hpv := hvalid p hp_mem
      rcases hp.eq_one_or_self_of_dvd p hdvd with h1 | h2 <;> omega

/-! ### Part 2: Gap Bitmasks & `INC`/`DEC` Invariants -/

noncomputable def isNextPrime (S : ℕ) (i j : ℕ) : Prop :=
  S.testBit i = true ∧ S.testBit j = true ∧ i < j ∧ ∀ t, i < t → t < j → S.testBit t = false

noncomputable def hasFwdGap (S : ℕ) (i d : ℕ) : Prop :=
  1 ≤ d ∧ isNextPrime S i (i + d)

noncomputable def hasBwdGap (S : ℕ) (j d : ℕ) : Prop :=
  1 ≤ d ∧ d ≤ j ∧ isNextPrime S (j - d) j

lemma isNextPrime_unique_right {S i j1 j2 : ℕ}
    (h1 : isNextPrime S i j1) (h2 : isNextPrime S i j2) : j1 = j2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := h2.2.2.2 j1 h1.2.2.1 hlt
    rw [h1.2.1] at this
    exact Bool.noConfusion this
  · have := h1.2.2.2 j2 h2.2.2.1 hgt
    rw [h2.2.1] at this
    exact Bool.noConfusion this

lemma isNextPrime_unique_left {S i1 i2 j : ℕ}
    (h1 : isNextPrime S i1 j) (h2 : isNextPrime S i2 j) : i1 = i2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := h1.2.2.2 i2 hlt h2.2.2.1
    rw [h2.1] at this
    exact Bool.noConfusion this
  · have := h2.2.2.2 i1 hgt h1.2.2.1
    rw [h1.1] at this
    exact Bool.noConfusion this

lemma hasFwdGap_unique {S i d1 d2 : ℕ}
    (h1 : hasFwdGap S i d1) (h2 : hasFwdGap S i d2) : d1 = d2 := by
  have := isNextPrime_unique_right h1.2 h2.2
  omega

lemma hasBwdGap_unique {S j d1 d2 : ℕ}
    (h1 : hasBwdGap S j d1) (h2 : hasBwdGap S j d2) : d1 = d2 := by
  have := isNextPrime_unique_left h1.2.2 h2.2.2
  have := h1.2.1
  have := h2.2.1
  omega

structure GapInv (S : ℕ) (m : ℕ) (st : GapState) : Prop where
  rem_iff : ∀ i, st.rem.testBit i = true ↔
    (S.testBit i = true ∧ i ≠ M ∧ ∀ e, 1 ≤ e → e ≤ m → S.testBit (i + e) = false)
  gLt_iff : ∀ i, st.gLt.testBit i = true ↔ ∃ e, 1 ≤ e ∧ e ≤ m ∧ hasFwdGap S i e
  bLt_iff : ∀ j, st.bLt.testBit j = true ↔ ∃ e, 1 ≤ e ∧ e ≤ m ∧ hasBwdGap S j e
  inc_iff : ∀ i, st.inc.testBit i = true ↔
    ∃ dp dn, 1 ≤ dp ∧ dp < dn ∧ dn ≤ m ∧ hasBwdGap S i dp ∧ hasFwdGap S i dn
  dec_iff : ∀ i, st.dec.testBit i = true ↔
    ∃ dp dn, 1 ≤ dn ∧ dn < dp ∧ dp ≤ m ∧ hasBwdGap S i dp ∧ hasFwdGap S i dn

lemma gapInv_init (S : ℕ) (hSM : S.testBit M = true) :
    GapInv S 0 { rem := S ^^^ (1 <<< M), bLt := 0, gLt := 0, inc := 0, dec := 0 } where
  rem_iff i := by
    simp only [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases hi : M = i
    · subst hi
      simp [hSM]
    · simp only [hi, decide_false, Bool.bne_false, ne_eq, Ne.symm hi, not_false_eq_true, true_and]
      constructor
      · intro hS
        exact ⟨hS, fun e he1 he0 => by omega⟩
      · exact And.left
  gLt_iff i := by
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he1 he0
    omega
  bLt_iff j := by
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e he1 he0
    omega
  inc_iff i := by
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro dp dn _ _ hdn
    omega
  dec_iff i := by
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro dp dn _ _ hdp
    omega

lemma gapInv_step (S : ℕ) (hS_gt : ∀ i, M < i → S.testBit i = false)
    (m : ℕ) (st : GapState) (hinv : GapInv S m st) :
    GapInv S (m + 1) (gapStep S st (m + 1)) := by
  set d := m + 1
  set gd := st.rem &&& (S >>> d)
  set bd := gd <<< d
  have hgd : ∀ i, gd.testBit i = true ↔ hasFwdGap S i d := by
    intro i
    simp only [gd, Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftRight, hinv.rem_iff]
    rw [Nat.add_comm d i]
    constructor
    · rintro ⟨⟨hSi, _, hzero⟩, hSid⟩
      refine ⟨by omega, hSi, hSid, by omega, fun t ht1 ht2 => ?_⟩
      have hsub : i + (t - i) = t := by omega
      rw [← hsub]
      exact hzero (t - i) (by omega) (by omega)
    · rintro ⟨_, hSi, hSid, _, hzero⟩
      have hiM : i ≠ M := by
        intro hEq
        subst hEq
        have := hS_gt (M + d) (by omega)
        rw [hSid] at this
        exact Bool.noConfusion this
      refine ⟨⟨hSi, hiM, fun e he1 hem => hzero (i + e) (by omega) (by omega)⟩, hSid⟩
  have hbd : ∀ j, bd.testBit j = true ↔ hasBwdGap S j d := by
    intro j
    simp only [bd, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, hgd]
    constructor
    · rintro ⟨hdj, _, hnext⟩
      refine ⟨by omega, hdj, ?_⟩
      have hsub : j - d + d = j := by omega
      rwa [hsub] at hnext
    · rintro ⟨_, hdj, hnext⟩
      refine ⟨hdj, by omega, ?_⟩
      have hsub : j - d + d = j := by omega
      rwa [hsub]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change (st.rem ^^^ gd).testBit i = true ↔ _
    rw [Nat.testBit_xor]
    by_cases hrem : st.rem.testBit i = true
    · rw [hrem, Bool.true_xor, Bool.not_eq_true', ← Bool.not_eq_true, hgd]
      have hri := (hinv.rem_iff i).mp hrem
      constructor
      · intro hngd
        refine ⟨hri.1, hri.2.1, fun e he1 hed => ?_⟩
        by_cases hem : e ≤ m
        · exact hri.2.2 e he1 hem
        · have heq : e = d := by omega
          subst heq
          cases hbit : S.testBit (i + d)
          · rfl
          · exfalso
            apply hngd
            refine ⟨by omega, hri.1, hbit, by omega, fun t ht1 ht2 => ?_⟩
            have hsub : i + (t - i) = t := by omega
            rw [← hsub]
            exact hri.2.2 (t - i) (by omega) (by omega)
      · rintro ⟨_, _, hzero⟩ ⟨_, _, hSid, _, _⟩
        have := hzero d (by omega) (le_refl d)
        rw [hSid] at this
        exact Bool.noConfusion this
    · have hremf : st.rem.testBit i = false := Bool.eq_false_iff.mpr hrem
      have hgdf : gd.testBit i = false := by
        simp [gd, Nat.testBit_and, hremf]
      rw [hremf, hgdf]
      simp only [Bool.false_xor, Bool.false_eq_true, false_iff]
      rintro ⟨hSi, hiM, hzero⟩
      exact hrem ((hinv.rem_iff i).mpr ⟨hSi, hiM, fun e he1 hem => hzero e he1 (by omega)⟩)
  · intro i
    change (st.gLt ||| gd).testBit i = true ↔ _
    simp only [Nat.testBit_or, Bool.or_eq_true, hinv.gLt_iff, hgd]
    constructor
    · rintro (⟨e, he1, hem, hf⟩ | hf)
      · exact ⟨e, he1, by omega, hf⟩
      · exact ⟨d, by omega, le_refl d, hf⟩
    · rintro ⟨e, he1, hed, hf⟩
      by_cases hem : e ≤ m
      · exact Or.inl ⟨e, he1, hem, hf⟩
      · have heq : e = d := by omega
        subst heq
        exact Or.inr hf
  · intro j
    change (st.bLt ||| bd).testBit j = true ↔ _
    simp only [Nat.testBit_or, Bool.or_eq_true, hinv.bLt_iff, hbd]
    constructor
    · rintro (⟨e, he1, hem, hb⟩ | hb)
      · exact ⟨e, he1, by omega, hb⟩
      · exact ⟨d, by omega, le_refl d, hb⟩
    · rintro ⟨e, he1, hed, hb⟩
      by_cases hem : e ≤ m
      · exact Or.inl ⟨e, he1, hem, hb⟩
      · have heq : e = d := by omega
        subst heq
        exact Or.inr hb
  · intro i
    change (st.inc ||| (gd &&& st.bLt)).testBit i = true ↔ _
    simp only [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true,
      hinv.inc_iff, hinv.bLt_iff, hgd]
    constructor
    · rintro (⟨dp, dn, hdp, hlt, hdn, hb, hf⟩ | ⟨hf, dp, hdp, hdpm, hb⟩)
      · exact ⟨dp, dn, hdp, hlt, by omega, hb, hf⟩
      · exact ⟨dp, d, hdp, by omega, le_refl d, hb, hf⟩
    · rintro ⟨dp, dn, hdp, hlt, hdn, hb, hf⟩
      by_cases hle : dn ≤ m
      · exact Or.inl ⟨dp, dn, hdp, hlt, hle, hb, hf⟩
      · have heq : dn = d := by omega
        subst heq
        exact Or.inr ⟨hf, dp, hdp, by omega, hb⟩
  · intro i
    change (st.dec ||| (bd &&& st.gLt)).testBit i = true ↔ _
    simp only [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true,
      hinv.dec_iff, hinv.gLt_iff, hbd]
    constructor
    · rintro (⟨dp, dn, hdn, hlt, hdp, hb, hf⟩ | ⟨hb, dn, hdn, hdnm, hf⟩)
      · exact ⟨dp, dn, hdn, hlt, by omega, hb, hf⟩
      · exact ⟨d, dn, hdn, by omega, le_refl d, hb, hf⟩
    · rintro ⟨dp, dn, hdn, hlt, hdp, hb, hf⟩
      by_cases hle : dp ≤ m
      · exact Or.inl ⟨dp, dn, hdn, hlt, hle, hb, hf⟩
      · have heq : dp = d := by omega
        subst heq
        exact Or.inr ⟨hb, dn, hdn, by omega, hf⟩

lemma gapInv_loop (S : ℕ) (hS_gt : ∀ i, M < i → S.testBit i = false) :
    ∀ fuel m st, GapInv S m st → GapInv S (m + fuel) (gapLoop S st fuel (m + 1))
  | 0, m, st, hinv => by simpa [gapLoop] using hinv
  | fuel + 1, m, st, hinv => by
    have h1 := gapInv_step S hS_gt m st hinv
    have h2 := gapInv_loop S hS_gt fuel (m + 1) (gapStep S st (m + 1)) h1
    have heq : m + 1 + fuel = m + (fuel + 1) := by omega
    rw [heq] at h2
    exact h2

/-! ### Part 3: SWAR Popcount Correctness -/

noncomputable def field (x w j : ℕ) : ℕ := (x >>> (j * w)) % 2 ^ w

lemma swarApply_swarMasks : ∀ r w x,
    swarApply (swarMasks r w) x = swarLoop r w x
  | 0, _, _ => rfl
  | r + 1, w, _ => swarApply_swarMasks r (2 * w) _

lemma field_mod_two_pow_eq {x w m j : ℕ} (hj : j < m) :
    field (x % 2 ^ (m * w)) w j = field x w j := by
  apply Nat.eq_of_testBit_eq
  intro r
  simp only [field, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hr : r < w
  · have hlt : j * w + r < m * w := by
      have : (j + 1) * w ≤ m * w := Nat.mul_le_mul_right w hj
      have : j * w + w = (j + 1) * w := by ring
      omega
    simp [hr, hlt]
  · simp [hr]

lemma sum_fields_eq (w : ℕ) : ∀ m x, x < 2 ^ (m * w) →
    ∑ j ∈ Finset.range m, field x w j * 2 ^ (j * w) = x
  | 0, x, hx => by
    simp only [Nat.zero_mul, Nat.pow_zero] at hx
    simp [show x = 0 by omega]
  | m + 1, x, hx => by
    rw [Finset.sum_range_succ]
    have hlow_lt : x % 2 ^ (m * w) < 2 ^ (m * w) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsum_low : ∑ j ∈ Finset.range m, field x w j * 2 ^ (j * w) = x % 2 ^ (m * w) := by
      have h1 : ∑ j ∈ Finset.range m, field x w j * 2 ^ (j * w) =
          ∑ j ∈ Finset.range m, field (x % 2 ^ (m * w)) w j * 2 ^ (j * w) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [field_mod_two_pow_eq (Finset.mem_range.mp hj)]
      rw [h1]
      exact sum_fields_eq w m (x % 2 ^ (m * w)) hlow_lt
    rw [hsum_low]
    have hhigh_lt : x / 2 ^ (m * w) < 2 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      have : w + m * w = (m + 1) * w := by ring
      rwa [this]
    have hfield_m : field x w m = x / 2 ^ (m * w) := by
      rw [field, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hhigh_lt]
    rw [hfield_m, Nat.mul_comm (x / 2 ^ (m * w))]
    exact Nat.mod_add_div x (2 ^ (m * w))

lemma field_of_sum_digits (w : ℕ) (f : ℕ → ℕ) : ∀ m,
    (∀ j < m, f j < 2 ^ w) →
    (∑ j ∈ Finset.range m, f j * 2 ^ (j * w)) < 2 ^ (m * w) ∧
    ∀ j < m, field (∑ k ∈ Finset.range m, f k * 2 ^ (k * w)) w j = f j
  | 0, _ => ⟨by simp, fun _ hj => by omega⟩
  | m + 1, hf => by
    have ⟨hlow_lt, hlow_field⟩ := field_of_sum_digits w f m (fun j hj => hf j (by omega))
    set low := ∑ k ∈ Finset.range m, f k * 2 ^ (k * w)
    have htot : ∑ k ∈ Finset.range (m + 1), f k * 2 ^ (k * w) = low + f m * 2 ^ (m * w) :=
      Finset.sum_range_succ _ m
    rw [htot]
    have hfm : f m < 2 ^ w := hf m (by omega)
    have htot_lt : low + f m * 2 ^ (m * w) < 2 ^ ((m + 1) * w) := by
      have h1 : f m + 1 ≤ 2 ^ w := hfm
      have h2 : (f m + 1) * 2 ^ (m * w) ≤ 2 ^ w * 2 ^ (m * w) :=
        Nat.mul_le_mul_right _ h1
      have h3 : 2 ^ w * 2 ^ (m * w) = 2 ^ ((m + 1) * w) := by
        rw [← Nat.pow_add]
        congr 1
        ring
      have h4 : (f m + 1) * 2 ^ (m * w) = f m * 2 ^ (m * w) + 2 ^ (m * w) := by ring
      omega
    refine ⟨htot_lt, fun j hj => ?_⟩
    by_cases hjm : j < m
    · rw [← hlow_field j hjm]
      apply Nat.eq_of_testBit_eq
      intro r
      simp only [field, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      by_cases hr : r < w
      · have hlt : j * w + r < m * w := by
          have : (j + 1) * w ≤ m * w := Nat.mul_le_mul_right w hjm
          have : j * w + w = (j + 1) * w := by ring
          omega
        simp [hr, testBit_add_mul_two_pow hlow_lt, hlt]
      · simp [hr]
    · have hj_eq : j = m := by omega
      subst hj_eq
      rw [field, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hlow_lt, Nat.zero_add, Nat.mod_eq_of_lt hfm]

lemma testBit_swarMask (w : ℕ) (hw : 0 < w) (m i : ℕ) :
    (geomSum (2 * w) m * (2 ^ w - 1)).testBit i =
    decide (i < m * (2 * w) ∧ i % (2 * w) < w) := by
  induction m with
  | zero => simp [geomSum]
  | succ m ih =>
    have hstep : geomSum (2 * w) (m + 1) * (2 ^ w - 1) =
        geomSum (2 * w) m * (2 ^ w - 1) + (2 ^ w - 1) * 2 ^ (m * (2 * w)) := by
      simp only [geomSum, Finset.sum_range_succ, Nat.add_mul]
      ring
    have hlow_lt : geomSum (2 * w) m * (2 ^ w - 1) < 2 ^ (m * (2 * w)) := by
      have hle : 2 ^ w - 1 ≤ 2 ^ (2 * w) - 1 := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : w ≤ 2 * w)
        omega
      have hmul : geomSum (2 * w) m * (2 ^ w - 1) ≤ (2 ^ (2 * w) - 1) * geomSum (2 * w) m := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hle
      rw [geomSum_mul (2 * w) (by omega) m] at hmul
      have hpos : 0 < 2 ^ (m * (2 * w)) := Nat.two_pow_pos _
      omega
    rw [hstep, testBit_add_mul_two_pow hlow_lt]
    by_cases hi : i < m * (2 * w)
    · rw [ite_eq_left hi, ih]
      have hlt : i < (m + 1) * (2 * w) := by
        have : (m + 1) * (2 * w) = m * (2 * w) + 2 * w := by ring
        omega
      simp [hi, hlt]
    · rw [ite_eq_right hi, Nat.testBit_two_pow_sub_one]
      have hsub_le : m * (2 * w) ≤ i := by omega
      by_cases hltw : i - m * (2 * w) < w
      · have hlt2 : i < (m + 1) * (2 * w) := by
          have : (m + 1) * (2 * w) = m * (2 * w) + 2 * w := by ring
          omega
        have hmod : i % (2 * w) = i - m * (2 * w) := by
          have hdec : i = (i - m * (2 * w)) + (2 * w) * m := by
            have : (2 * w) * m = m * (2 * w) := Nat.mul_comm _ _
            omega
          conv_lhs => rw [hdec]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        simp [hltw, hlt2, hmod]
      · rw [decide_eq_false hltw, eq_comm, decide_eq_false_iff_not]
        rintro ⟨hlt2, hmod⟩
        have hsub2 : i - m * (2 * w) < 2 * w := by
          have : (m + 1) * (2 * w) = m * (2 * w) + 2 * w := by ring
          omega
        have hmod_eq : i % (2 * w) = i - m * (2 * w) := by
          have hdec : i = (i - m * (2 * w)) + (2 * w) * m := by
            have : (2 * w) * m = m * (2 * w) := Nat.mul_comm _ _
            omega
          conv_lhs => rw [hdec]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub2]
        omega

lemma swarMaskLoop_eq (w : ℕ) (hw : 0 < w) : ∀ r j,
    swarMaskLoop (geomSum (2 * w) (2 ^ j) * (2 ^ w - 1)) r (2 ^ j * (2 * w)) =
      geomSum (2 * w) (2 ^ (j + r)) * (2 ^ w - 1)
  | 0, j => by simp [swarMaskLoop]
  | r + 1, j => by
    unfold swarMaskLoop
    have hstep : (geomSum (2 * w) (2 ^ j) * (2 ^ w - 1)) |||
        ((geomSum (2 * w) (2 ^ j) * (2 ^ w - 1)) <<< (2 ^ j * (2 * w))) =
        geomSum (2 * w) (2 ^ (j + 1)) * (2 ^ w - 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_swarMask w hw, testBit_swarMask w hw,
        testBit_swarMask w hw]
      have hpow : 2 ^ (j + 1) * (2 * w) = 2 ^ j * (2 * w) + 2 ^ j * (2 * w) := by
        rw [Nat.pow_succ]; ring
      by_cases hlow : i < 2 ^ j * (2 * w)
      · have hge : ¬ (2 ^ j * (2 * w) ≤ i) := by omega
        have hlt2 : i < 2 ^ (j + 1) * (2 * w) := by omega
        simp [hlow, hge, hlt2]
      · have hge : 2 ^ j * (2 * w) ≤ i := by omega
        have hmod : (i - 2 ^ j * (2 * w)) % (2 * w) = i % (2 * w) := by
          have hdec : i = (i - 2 ^ j * (2 * w)) + (2 * w) * 2 ^ j := by
            have : (2 * w) * 2 ^ j = 2 ^ j * (2 * w) := Nat.mul_comm _ _
            omega
          conv_rhs => rw [hdec]
          rw [Nat.add_mul_mod_self_left]
        have hlt_iff : i - 2 ^ j * (2 * w) < 2 ^ j * (2 * w) ↔ i < 2 ^ (j + 1) * (2 * w) := by
          omega
        simp [hlow, hge, hmod, hlt_iff]
    have hspan : 2 * (2 ^ j * (2 * w)) = 2 ^ (j + 1) * (2 * w) := by
      rw [Nat.pow_succ]; ring
    rw [hstep, hspan, swarMaskLoop_eq w hw r (j + 1)]
    rw [show j + 1 + r = j + (r + 1) by omega]

lemma sum_range_two_mul (f : ℕ → ℕ) : ∀ m,
    ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) = ∑ j ∈ Finset.range (2 * m), f j
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_range_two_mul f m]
    have h1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_assoc]

lemma swarLoop_eq_sum_fields (K : ℕ) : ∀ (r w x : ℕ),
    0 < w → 2 ^ r * w = 2 ^ K → x < 2 ^ (2 ^ r * w) →
    (∀ j < 2 ^ r, field x w j ≤ w) →
    swarLoop r w x = ∑ j ∈ Finset.range (2 ^ r), field x w j
  | 0, w, x, _, _, hx, _ => by
    simp only [swarLoop, Nat.pow_zero, Nat.one_mul, Finset.range_one, Finset.sum_singleton,
      field, Nat.zero_mul, Nat.shiftRight_zero] at hx ⊢
    exact (Nat.mod_eq_of_lt hx).symm
  | r + 1, w, x, hw, hrw, hx, hbound => by
    set m := 2 ^ r
    have h2m : 2 ^ (r + 1) = 2 * m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmw : m * (2 * w) = 2 ^ K := by
      calc m * (2 * w) = 2 * m * w := by ring
        _ = 2 ^ (r + 1) * w := by rw [h2m]
        _ = 2 ^ K := hrw
    have hmask_eq : swarMaskLoop ((1 <<< w) - 1) r (2 * w) =
        geomSum (2 * w) m * (2 ^ w - 1) := by
      have hinit : (1 <<< w) - 1 = geomSum (2 * w) (2 ^ 0) * (2 ^ w - 1) := by
        simp [geomSum, Nat.shiftLeft_eq]
      have h := swarMaskLoop_eq w hw r 0
      simpa [hinit] using h
    unfold swarLoop
    rw [hmask_eq]
    set mask := geomSum (2 * w) m * (2 ^ w - 1)
    set A := x &&& mask
    set B := (x >>> w) &&& mask
    have hA_lt : A < 2 ^ (m * (2 * w)) := lt_two_pow_of_testBit fun i hi => by
      simp only [A, mask, Nat.testBit_and, testBit_swarMask w hw m i]
      have : ¬ (i < m * (2 * w) ∧ i % (2 * w) < w) := by omega
      simp [this]
    have hB_lt : B < 2 ^ (m * (2 * w)) := lt_two_pow_of_testBit fun i hi => by
      simp only [B, mask, Nat.testBit_and, testBit_swarMask w hw m i]
      have : ¬ (i < m * (2 * w) ∧ i % (2 * w) < w) := by omega
      simp [this]
    have hA_field : ∀ j < m, field A (2 * w) j = field x w (2 * j) := by
      intro j hj
      apply Nat.eq_of_testBit_eq
      intro t
      simp only [field, A, mask, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
        Nat.testBit_and, testBit_swarMask w hw m]
      by_cases ht2 : t < 2 * w
      · have hidx_lt : j * (2 * w) + t < m * (2 * w) := by
          have : (j + 1) * (2 * w) ≤ m * (2 * w) := Nat.mul_le_mul_right _ hj
          have : j * (2 * w) + 2 * w = (j + 1) * (2 * w) := by ring
          omega
        have hmod : (j * (2 * w) + t) % (2 * w) = t := by
          rw [Nat.mul_comm j (2 * w), Nat.mul_add_mod, Nat.mod_eq_of_lt ht2]
        have heq_idx : j * (2 * w) + t = 2 * j * w + t := by ring
        by_cases htw : t < w
        · rw [hmod]
          simp only [ht2, htw, hidx_lt, and_self, decide_true, Bool.true_and, Bool.and_true]
          rw [heq_idx]
        · simp [ht2, htw, hidx_lt, hmod]
      · have htw : ¬ t < w := by omega
        simp [ht2, htw]
    have hB_field : ∀ j < m, field B (2 * w) j = field x w (2 * j + 1) := by
      intro j hj
      apply Nat.eq_of_testBit_eq
      intro t
      simp only [field, B, mask, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
        Nat.testBit_and, testBit_swarMask w hw m]
      by_cases ht2 : t < 2 * w
      · have hidx_lt : j * (2 * w) + t < m * (2 * w) := by
          have : (j + 1) * (2 * w) ≤ m * (2 * w) := Nat.mul_le_mul_right _ hj
          have : j * (2 * w) + 2 * w = (j + 1) * (2 * w) := by ring
          omega
        have hmod : (j * (2 * w) + t) % (2 * w) = t := by
          rw [Nat.mul_comm j (2 * w), Nat.mul_add_mod, Nat.mod_eq_of_lt ht2]
        have heq_idx : w + (j * (2 * w) + t) = (2 * j + 1) * w + t := by ring
        by_cases htw : t < w
        · simp only [ht2, htw, hidx_lt, hmod, and_self, decide_true, Bool.true_and, Bool.and_true, heq_idx]
        · simp [ht2, htw, hidx_lt, hmod]
      · have htw : ¬ t < w := by omega
        simp [ht2, htw]
    have hAB_sum : A + B = ∑ j ∈ Finset.range m,
        (field x w (2 * j) + field x w (2 * j + 1)) * 2 ^ (j * (2 * w)) := by
      have hA_eq := (sum_fields_eq (2 * w) m A hA_lt).symm
      have hB_eq := (sum_fields_eq (2 * w) m B hB_lt).symm
      rw [hA_eq, hB_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm := Finset.mem_range.mp hj
      rw [hA_field j hjm, hB_field j hjm, Nat.add_mul]
    have hcoef_le : ∀ j < m, field x w (2 * j) + field x w (2 * j + 1) ≤ 2 * w := by
      intro j hj
      have h1 := hbound (2 * j) (by rw [h2m]; omega)
      have h2 := hbound (2 * j + 1) (by rw [h2m]; omega)
      omega
    have hcoef_lt : ∀ j < m, field x w (2 * j) + field x w (2 * j + 1) < 2 ^ (2 * w) := by
      intro j hj
      have h1 := hcoef_le j hj
      have h2 : 2 * w < 2 ^ (2 * w) := Nat.lt_two_pow_self
      omega
    have ⟨hAB_lt, hAB_field⟩ := field_of_sum_digits (2 * w)
      (fun j => field x w (2 * j) + field x w (2 * j + 1)) m hcoef_lt
    rw [← hAB_sum] at hAB_lt hAB_field
    have hAB_bound : ∀ j < m, field (A + B) (2 * w) j ≤ 2 * w := by
      intro j hj
      rw [hAB_field j hj]
      exact hcoef_le j hj
    rw [swarLoop_eq_sum_fields K r (2 * w) (A + B) (by omega) hmw hAB_lt hAB_bound]
    have hsum_eq : ∑ j ∈ Finset.range m, field (A + B) (2 * w) j =
        ∑ j ∈ Finset.range m, (field x w (2 * j) + field x w (2 * j + 1)) :=
      Finset.sum_congr rfl fun j hj => hAB_field j (Finset.mem_range.mp hj)
    rw [hsum_eq, sum_range_two_mul (field x w) m, ← h2m]

lemma swar_popcount_eq (x : ℕ) (hx : x < 2 ^ (M + 1)) :
    swarApply (swarMasks 21 1) x =
    ((Finset.range (M + 1)).filter (fun i => x.testBit i)).card := by
  have hM_lt : M + 1 ≤ 2 ^ 21 := by unfold M; omega
  have hx21 : x < 2 ^ (2 ^ 21 * 1) := by
    rw [Nat.mul_one]
    exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hM_lt)
  rw [swarApply_swarMasks, swarLoop_eq_sum_fields 21 21 1 x (by omega) (by ring) hx21
    (fun j _ => by
      have : field x 1 j < 2 ^ 1 := Nat.mod_lt _ (by omega)
      omega)]
  have hfield1 : ∀ j, field x 1 j = if x.testBit j then 1 else 0 := by
    intro j
    rw [field, Nat.mul_one, Nat.pow_one]
    have hdec := Nat.decide_shiftRight_mod_two_eq_one (x := x) (i := j)
    have hlt2 : (x >>> j) % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hbit : x.testBit j
    · rw [hbit] at hdec
      simp only [decide_eq_false_iff_not] at hdec
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [hbit] at hdec
      simp only [decide_eq_true_eq] at hdec
      simp [hdec]
  have hsum_card : ∑ j ∈ Finset.range (2 ^ 21), field x 1 j =
      ((Finset.range (2 ^ 21)).filter (fun i => x.testBit i)).card := by
    simp_rw [hfield1]
    rw [Finset.sum_boole, Nat.cast_id]
  rw [hsum_card]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hbit⟩
    refine ⟨?_, hbit⟩
    by_contra hge
    have hle : M + 1 ≤ i := by omega
    have hxlt : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hle)
    have hf := Nat.testBit_lt_two_pow hxlt
    rw [hbit] at hf
    exact Bool.noConfusion hf
  · rintro ⟨hi, hbit⟩
    exact ⟨lt_of_lt_of_le hi hM_lt, hbit⟩

/-! ### Part 4: Linking `sieveS`, `gapLoop`, and `OeisA92243.a 261150` -/

lemma conjecture1_witness : a 261150 = 1 := by
  set S := sieveS
  set st0 : GapState := { rem := S ^^^ (1 <<< M), bLt := 0, gLt := 0, inc := 0, dec := 0 }
  set st := gapLoop S st0 74 1
  set masks := swarMasks 21 1
  have hcomp : (st.rem, S >>> M, swarApply masks S, swarApply masks st.inc, swarApply masks st.dec) =
      (0, 1, 261150, 126043, 126043) := computeAll_eq
  have hrem0 : st.rem = 0 := congrArg Prod.fst hcomp
  have hSM_shr : S >>> M = 1 := congrArg (fun p => p.2.1) hcomp
  have hpopS : swarApply masks S = 261150 := congrArg (fun p => p.2.2.1) hcomp
  have hpopInc : swarApply masks st.inc = 126043 := congrArg (fun p => p.2.2.2.1) hcomp
  have hpopDec : swarApply masks st.dec = 126043 := congrArg (fun p => p.2.2.2.2) hcomp
  have hSM : S.testBit M = true := by
    have : (S >>> M) % 2 = 1 := by rw [hSM_shr]
    rw [← Nat.decide_shiftRight_mod_two_eq_one, this]
    rfl
  have hinv : GapInv S 74 st := by
    have h0 := gapInv_init S hSM
    have hloop := gapInv_loop S sieveS_testBit_false_of_gt 74 0 st0 h0
    simpa [st] using hloop
  have hInc_lt : st.inc < 2 ^ (M + 1) := lt_two_pow_of_testBit fun i hi => by
    by_contra hne
    have ht : st.inc.testBit i = true := Bool.eq_true_of_not_eq_false hne
    rcases (hinv.inc_iff i).mp ht with ⟨_, _, _, _, _, _, _, hSi, _, _, _⟩
    have hf := sieveS_testBit_false_of_gt i (by omega)
    rw [hSi] at hf
    exact Bool.noConfusion hf
  have hDec_lt : st.dec < 2 ^ (M + 1) := lt_two_pow_of_testBit fun i hi => by
    by_contra hne
    have ht : st.dec.testBit i = true := Bool.eq_true_of_not_eq_false hne
    rcases (hinv.dec_iff i).mp ht with ⟨_, _, _, _, _, _, _, hSi, _, _, _⟩
    have hf := sieveS_testBit_false_of_gt i (by omega)
    rw [hSi] at hf
    exact Bool.noConfusion hf
  set oddBits := (Finset.range (M + 1)).filter (fun i => S.testBit i)
  have hcard_S : oddBits.card = 261150 := by
    rw [← swar_popcount_eq S sieveS_lt]
    exact hpopS
  have hcard_Inc : ((Finset.range (M + 1)).filter (fun i => st.inc.testBit i)).card = 126043 := by
    rw [← swar_popcount_eq st.inc hInc_lt]
    exact hpopInc
  have hcard_Dec : ((Finset.range (M + 1)).filter (fun i => st.dec.testBit i)).card = 126043 := by
    rw [← swar_popcount_eq st.dec hDec_lt]
    exact hpopDec
  -- Every prime bit i < M has a forward gap ≤ 74
  have hfwd_le : ∀ i d, hasFwdGap S i d → d ≤ 74 := by
    intro i d hd
    by_contra hgt
    have hiM : i ≠ M := by
      intro heq
      subst heq
      have hf := sieveS_testBit_false_of_gt (M + d) (by omega)
      rw [hd.2.2.1] at hf
      exact Bool.noConfusion hf
    have hrem_i : st.rem.testBit i = true := by
      rw [hinv.rem_iff]
      refine ⟨hd.2.1, hiM, fun e he1 he74 => hd.2.2.2.2 (i + e) (by omega) (by omega)⟩
    rw [hrem0, Nat.zero_testBit] at hrem_i
    exact Bool.noConfusion hrem_i
  have hbwd_le : ∀ j d, hasBwdGap S j d → d ≤ 74 := by
    intro j d hd
    have hfwd : hasFwdGap S (j - d) d := by
      refine ⟨hd.1, ?_⟩
      have hsub : j - d + d = j := by have := hd.2.1; omega
      rw [hsub]
      exact hd.2.2
    exact hfwd_le (j - d) d hfwd
  -- Count primes ≤ 2 * M + 1
  have hM_prime : (2 * M + 1).Prime := (sieveS_testBit_iff M (le_refl M)).mp hSM
  have hprimes_set : (Finset.range (2 * M + 2)).filter Nat.Prime =
      insert 2 (oddBits.image (fun i => 2 * i + 1)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image, oddBits]
    constructor
    · rintro ⟨hp_lt, hp⟩
      rcases hp.eq_two_or_odd with rfl | hodd
      · exact Or.inl rfl
      · refine Or.inr ⟨p / 2, ⟨⟨by omega, ?_⟩, by omega⟩⟩
        rw [sieveS_testBit_iff (p / 2) (by omega)]
        have : 2 * (p / 2) + 1 = p := by omega
        rwa [this]
    · rintro (rfl | ⟨i, ⟨⟨hi, hbit⟩, rfl⟩⟩)
      · exact ⟨by unfold M; omega, Nat.prime_two⟩
      · exact ⟨by omega, (sieveS_testBit_iff i (by omega)).mp hbit⟩
  have h2_not_mem : 2 ∉ oddBits.image (fun i => 2 * i + 1) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i _
    omega
  have hcount_succ : Nat.count Nat.Prime (2 * M + 2) = 261151 := by
    rw [Nat.count_eq_card_filter_range, hprimes_set, Finset.card_insert_of_notMem h2_not_mem,
      Finset.card_image_of_injective oddBits (fun a b h => by omega), hcard_S]
  have hcount_M : Nat.count Nat.Prime (2 * M + 1) = 261150 := by
    have hcs : Nat.count Nat.Prime (2 * M + 2) = Nat.count Nat.Prime (2 * M + 1) + 1 := by
      rw [show 2 * M + 2 = (2 * M + 1) + 1 by rfl, Nat.count_succ, ite_eq_left hM_prime]
    omega
  have hnth_N : Nat.nth Nat.Prime 261150 = 2 * M + 1 := by
    rw [← hcount_M]
    exact Nat.nth_count hM_prime
  -- Map k ↦ (p_k - 1) / 2 from Icc 1 261150 bijectively to oddBits
  let f : ℕ → ℕ := fun k => (Nat.nth Nat.Prime k - 1) / 2
  have hnth_prime : ∀ k, (Nat.nth Nat.Prime k).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime
  have hnth_smono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hf_eq : ∀ k, 1 ≤ k → 2 * f k + 1 = Nat.nth Nat.Prime k := by
    intro k hk
    have hp := hnth_prime k
    have hgt2 : 2 < Nat.nth Nat.Prime k := by
      rw [← Nat.nth_prime_zero_eq_two]
      exact hnth_smono (by omega)
    rcases hp.eq_two_or_odd with h2 | hodd
    · omega
    · dsimp [f]; omega
  have hf_smono : ∀ {a b}, 1 ≤ a → a < b → f a < f b := by
    intro a b ha hab
    have h1 := hf_eq a ha
    have h2 := hf_eq b (by omega)
    have hlt := hnth_smono hab
    omega
  have hf_le_M : ∀ k, 1 ≤ k → k ≤ 261150 → f k ≤ M := by
    intro k hk1 hkN
    have h1 := hf_eq k hk1
    have hle : Nat.nth Nat.Prime k ≤ 2 * M + 1 := by
      rw [← hnth_N]
      exact hnth_smono.monotone hkN
    omega
  have hf_mem : ∀ k ∈ Finset.Icc 1 261150, f k ∈ oddBits := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [oddBits, Finset.mem_filter, Finset.mem_range]
    have hle := hf_le_M k hk.1 hk.2
    refine ⟨by omega, ?_⟩
    rw [sieveS_testBit_iff (f k) hle, hf_eq k hk.1]
    exact hnth_prime k
  have hf_inj : Set.InjOn f (Finset.Icc 1 261150 : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hab (ne_of_lt (hf_smono ha.1 hlt))
    · exact absurd hab.symm (ne_of_lt (hf_smono hb.1 hgt))
  have hf_image_all : (Finset.Icc 1 261150).image f = oddBits := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      exact hf_mem k hk
    · rw [Finset.card_image_of_injOn hf_inj, Nat.card_Icc, hcard_S]
  have hf_1 : f 1 = 1 := by
    dsimp [f]
    rw [Nat.nth_prime_one_eq_three]
  have hf_N : f 261150 = M := by
    dsimp [f]
    rw [hnth_N]
    omega
  -- isNextPrime for consecutive k, k + 1
  have hf_next : ∀ k, 1 ≤ k → k < 261150 → isNextPrime S (f k) (f (k + 1)) := by
    intro k hk1 hkN
    have hfk_mem := hf_mem k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
    have hfk1_mem := hf_mem (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [oddBits, Finset.mem_filter, Finset.mem_range] at hfk_mem hfk1_mem
    refine ⟨hfk_mem.2, hfk1_mem.2, hf_smono hk1 (by omega), fun t ht1 ht2 => ?_⟩
    by_contra hne
    have ht_true : S.testBit t = true := Bool.eq_true_of_not_eq_false hne
    have ht_le : t ≤ M := by omega
    have ht_prime : (2 * t + 1).Prime := (sieveS_testBit_iff t ht_le).mp ht_true
    set c := Nat.count Nat.Prime (2 * t + 1)
    have hc_nth : Nat.nth Nat.Prime c = 2 * t + 1 := Nat.nth_count ht_prime
    have hlt1 : Nat.nth Nat.Prime k < Nat.nth Nat.Prime c := by
      rw [hc_nth, ← hf_eq k hk1]; omega
    have hlt2 : Nat.nth Nat.Prime c < Nat.nth Nat.Prime (k + 1) := by
      rw [hc_nth, ← hf_eq (k + 1) (by omega)]; omega
    have hkc : k < c := hnth_smono.lt_iff_lt.mp hlt1
    have hck1 : c < k + 1 := hnth_smono.lt_iff_lt.mp hlt2
    omega
  -- Inner bits image: Icc 2 261149 maps onto oddBits.filter (1 < · ∧ · < M)
  set innerBits := oddBits.filter (fun i => 1 < i ∧ i < M)
  have hf_image_inner : (Finset.Icc 2 261149).image f = innerBits := by
    ext i
    simp only [Finset.mem_image, Finset.mem_Icc, innerBits, Finset.mem_filter]
    constructor
    · rintro ⟨k, ⟨hk2, hkN⟩, rfl⟩
      refine ⟨hf_mem k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), ?_, ?_⟩
      · rw [← hf_1]; exact hf_smono (by omega) (by omega)
      · rw [← hf_N]; exact hf_smono (by omega) (by omega)
    · rintro ⟨hi_mem, hi1, hiM⟩
      rw [← hf_image_all] at hi_mem
      rcases Finset.mem_image.mp hi_mem with ⟨k, hk, rfl⟩
      rw [Finset.mem_Icc] at hk
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1; rw [hf_1] at hi1; omega
      · by_contra hgt
        have hkN : k = 261150 := by omega
        subst hkN; rw [hf_N] at hiM; omega
  -- Inc and Dec are supported inside innerBits
  have hInc_sub : ∀ i, st.inc.testBit i = true → i ∈ innerBits := by
    intro i hi
    rcases (hinv.inc_iff i).mp hi with ⟨dp, dn, hdp, _, _, hb, hf⟩
    have hi_le : i ≤ M := by
      by_contra hgt
      have hff := sieveS_testBit_false_of_gt i (by omega)
      rw [hf.2.1] at hff; exact Bool.noConfusion hff
    have hi_lt_M : i < M := by
      by_contra hge
      have hff := sieveS_testBit_false_of_gt (i + dn) (by omega)
      rw [hf.2.2.1] at hff; exact Bool.noConfusion hff
    have hi_gt_1 : 1 < i := by
      have hS0 : S.testBit 0 = false := by
        rw [show S = sieveS from rfl, sieveS, Nat.testBit_and, testBit_allMask_sub_one]
        simp
      have hne0 : i - dp ≠ 0 := by
        intro h0
        have := hb.2.2.1
        rw [h0, hS0] at this
        exact Bool.noConfusion this
      have := hb.2.1
      omega
    simp only [innerBits, oddBits, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, hf.2.1⟩, hi_gt_1, hi_lt_M⟩
  have hDec_sub : ∀ i, st.dec.testBit i = true → i ∈ innerBits := by
    intro i hi
    rcases (hinv.dec_iff i).mp hi with ⟨dp, dn, hdn, _, _, hb, hf⟩
    have hi_le : i ≤ M := by
      by_contra hgt
      have hff := sieveS_testBit_false_of_gt i (by omega)
      rw [hf.2.1] at hff; exact Bool.noConfusion hff
    have hi_lt_M : i < M := by
      by_contra hge
      have hff := sieveS_testBit_false_of_gt (i + dn) (by omega)
      rw [hf.2.2.1] at hff; exact Bool.noConfusion hff
    have hi_gt_1 : 1 < i := by
      have hS0 : S.testBit 0 = false := by
        rw [show S = sieveS from rfl, sieveS, Nat.testBit_and, testBit_allMask_sub_one]
        simp
      have hne0 : i - dp ≠ 0 := by
        intro h0
        have := hb.2.2.1
        rw [h0, hS0] at this
        exact Bool.noConfusion this
      have := hb.2.1
      omega
    simp only [innerBits, oddBits, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, hf.2.1⟩, hi_gt_1, hi_lt_M⟩
  -- Term-by-term match for k ∈ Icc 2 261149
  have hterm : ∀ k ∈ Finset.Icc 2 261149,
      ((primeGap (k + 1) : ℤ) - (primeGap k : ℤ)).sign =
      (if st.inc.testBit (f k) then (1 : ℤ) else 0) -
      (if st.dec.testBit (f k) then (1 : ℤ) else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hprev := hf_next (k - 1) (by omega) (by omega)
    have hnext := hf_next k (by omega) (by omega)
    have hkm1 : k - 1 + 1 = k := by omega
    rw [hkm1] at hprev
    set dp := f k - f (k - 1)
    set dn := f (k + 1) - f k
    have hdp_pos : 1 ≤ dp := by have := hprev.2.2.1; omega
    have hdn_pos : 1 ≤ dn := by have := hnext.2.2.1; omega
    have hbwd : hasBwdGap S (f k) dp := by
      refine ⟨hdp_pos, by omega, ?_⟩
      have hsub : f k - dp = f (k - 1) := by have := hprev.2.2.1; omega
      rwa [hsub]
    have hfwd : hasFwdGap S (f k) dn := by
      refine ⟨hdn_pos, ?_⟩
      have hadd : f k + dn = f (k + 1) := by have := hnext.2.2.1; omega
      rwa [hadd]
    have hdp74 : dp ≤ 74 := hbwd_le (f k) dp hbwd
    have hdn74 : dn ≤ 74 := hfwd_le (f k) dn hfwd
    have hgap_k : primeGap k = 2 * dp := by
      unfold primeGap
      have h1 := hf_eq k (by omega)
      have h2 := hf_eq (k - 1) (by omega)
      omega
    have hgap_k1 : primeGap (k + 1) = 2 * dn := by
      unfold primeGap
      rw [show k + 1 - 1 = k by omega]
      have h1 := hf_eq (k + 1) (by omega)
      have h2 := hf_eq k (by omega)
      omega
    have hinc_iff : st.inc.testBit (f k) = true ↔ dp < dn := by
      rw [hinv.inc_iff]
      constructor
      · rintro ⟨dp', dn', _, hlt, _, hb', hf'⟩
        rw [hasBwdGap_unique hb' hbwd, hasFwdGap_unique hf' hfwd] at hlt
        exact hlt
      · intro hlt
        exact ⟨dp, dn, hdp_pos, hlt, hdn74, hbwd, hfwd⟩
    have hdec_iff : st.dec.testBit (f k) = true ↔ dn < dp := by
      rw [hinv.dec_iff]
      constructor
      · rintro ⟨dp', dn', _, hlt, _, hb', hf'⟩
        rw [hasBwdGap_unique hb' hbwd, hasFwdGap_unique hf' hfwd] at hlt
        exact hlt
      · intro hlt
        exact ⟨dp, dn, hdn_pos, hlt, hdp74, hbwd, hfwd⟩
    rw [hgap_k, hgap_k1]
    rcases lt_trichotomy dp dn with hlt | heq | hgt
    · have hi1 : st.inc.testBit (f k) = true := hinc_iff.mpr hlt
      have hd0 : st.dec.testBit (f k) = false :=
        Bool.eq_false_iff.mpr (fun h => by have := hdec_iff.mp h; omega)
      rw [hi1, hd0]
      simp only [↓reduceIte, Bool.false_eq_true, sub_zero]
      exact Int.sign_eq_one_of_pos (by omega)
    · have hi0 : st.inc.testBit (f k) = false :=
        Bool.eq_false_iff.mpr (fun h => by have := hinc_iff.mp h; omega)
      have hd0 : st.dec.testBit (f k) = false :=
        Bool.eq_false_iff.mpr (fun h => by have := hdec_iff.mp h; omega)
      rw [hi0, hd0, heq]
      simp
    · have hi0 : st.inc.testBit (f k) = false :=
        Bool.eq_false_iff.mpr (fun h => by have := hinc_iff.mp h; omega)
      have hd1 : st.dec.testBit (f k) = true := hdec_iff.mpr hgt
      rw [hi0, hd1]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_sub]
      exact Int.sign_eq_neg_one_of_neg (by omega)
  -- Put the sum together!
  unfold a
  rw [ite_eq_right (by omega : ¬ 261150 ≤ 1)]
  have hIcc_split : Finset.Icc 2 261150 = insert 2 (Finset.Icc 3 261150) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc_split, Finset.sum_insert (by simp)]
  have hterm2 : ((primeGap 2 : ℤ) - (primeGap 1 : ℤ)).sign = 1 := by
    unfold primeGap
    rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
    decide
  rw [hterm2]
  have hshift : ∑ m ∈ Finset.Icc 3 261150, ((primeGap m : ℤ) - (primeGap (m - 1) : ℤ)).sign =
      ∑ k ∈ Finset.Icc 2 261149, ((primeGap (k + 1) : ℤ) - (primeGap k : ℤ)).sign := by
    refine (Finset.sum_nbij (· + 1) ?_ ?_ ?_ ?_).symm
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro a _ b _ h; dsimp only at h; omega
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_Icc] at hm
      exact ⟨m - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by dsimp only; omega⟩
    · intro k _; simp
  rw [hshift, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hsum_inc : ∑ k ∈ Finset.Icc 2 261149, (if st.inc.testBit (f k) then (1 : ℤ) else 0) =
      (((Finset.range (M + 1)).filter (fun i => st.inc.testBit i)).card : ℤ) := by
    have hinj2 : Set.InjOn f (Finset.Icc 2 261149 : Set ℕ) :=
      hf_inj.mono (by intro x hx; simp only [Finset.mem_coe, Finset.mem_Icc] at hx ⊢; omega)
    rw [← Finset.sum_image (f := fun i => if st.inc.testBit i then (1 : ℤ) else 0) hinj2,
      hf_image_inner]
    have hsub : innerBits ⊆ Finset.range (M + 1) := by
      intro x hx
      simp only [innerBits, oddBits, Finset.mem_filter] at hx
      exact hx.1.1
    rw [Finset.sum_subset hsub (fun i _ hi_nmem => by
      have : st.inc.testBit i = false :=
        Bool.eq_false_iff.mpr (fun h => hi_nmem (hInc_sub i h))
      simp [this])]
    rw [Finset.sum_boole]
  have hsum_dec : ∑ k ∈ Finset.Icc 2 261149, (if st.dec.testBit (f k) then (1 : ℤ) else 0) =
      (((Finset.range (M + 1)).filter (fun i => st.dec.testBit i)).card : ℤ) := by
    have hinj2 : Set.InjOn f (Finset.Icc 2 261149 : Set ℕ) :=
      hf_inj.mono (by intro x hx; simp only [Finset.mem_coe, Finset.mem_Icc] at hx ⊢; omega)
    rw [← Finset.sum_image (f := fun i => if st.dec.testBit i then (1 : ℤ) else 0) hinj2,
      hf_image_inner]
    have hsub : innerBits ⊆ Finset.range (M + 1) := by
      intro x hx
      simp only [innerBits, oddBits, Finset.mem_filter] at hx
      exact hx.1.1
    rw [Finset.sum_subset hsub (fun i _ hi_nmem => by
      have : st.dec.testBit i = false :=
        Bool.eq_false_iff.mpr (fun h => hi_nmem (hDec_sub i h))
      simp [this])]
    rw [Finset.sum_boole]
  rw [hsum_inc, hsum_dec, hcard_Inc, hcard_Dec]
  norm_num

end Conjecture1Proof

/--
There exists $n > 250000$ with $a(n) > 0$ (witnessed by $n = 261150$ with $a(261150) = 1$).
-/
theorem conjecture1 : ∃ n > 250000, a n > 0 := by
  refine ⟨261150, by omega, ?_⟩
  rw [Conjecture1Proof.conjecture1_witness]
  omega

end OeisA92243
