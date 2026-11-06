import Mathlib

open Real
open scoped BigOperators

/- Determine all positive integer numbers  $n$  satisfying the following condition:
 the sum of the squares of any  $n$  prime numbers greater than  $3$  is divisible by  $n$ .-/
theorem number_theory_8557 {n : ℕ} (hnpos : 0 < n) :
    let rare (n : ℕ) := ∀ {p : ℕ → ℕ}, (∀ i < n, Nat.Prime (p i) ∧ 3 < p i) →
      n ∣ ∑ i ∈ Finset.range n, (p i ^ 2)
    rare n ↔ n ∣ 24 := by
  -- Let us call a natural number ***rare*** if  $n$  satisfies the given condition.
  intro rare
  cases' n with n
  -- n = 0 is impossible since n is positive.
  . norm_num at hnpos
  constructor
  . intro hnrare
    cases' n with n
    -- It's clear that n = 1 divides 24.
    . norm_num
    -- Next assume  $n>2$  is a rare number.
    --Then there are  $n-1$  primes  $7 < p_1 < p_2 < \ldots \ p_{n-1}$  s.t.
    -- $n \mid 5^2 + \sum_{i=1}^{n-1} p_i^2$ and  $n \mid 7^2 + \sum_{i=1}^{n-1} p_i^2$ ,
    let p : ℕ → ℕ := fun n => match n with
      | 0 => 5
      | _ => 11
    have hp0 : p 0 = 5 := rfl
    have : ∀ i < n + 1 + 1, Nat.Prime (p i) ∧ 3 < p i := by
      intro i hi
      cases' i with i
      . simp [p]; norm_num
      simp [p]; norm_num
    have hpsum := hnrare this
    rw [Finset.sum_range_succ'] at hpsum
    let q : ℕ → ℕ := fun n => match n with
      | 0 => 7
      | _ => 11
    have hq0 : q 0 = 7 := rfl
    have : ∀ i < n + 1 + 1, Nat.Prime (q i) ∧ 3 < q i := by
      intro i hi
      cases' i with i
      . simp [q]; norm_num
      simp [q]; norm_num
    have hqsum := hnrare this
    rw [Finset.sum_range_succ'] at hqsum
    -- yielding  $n \mid 7^2 - 5^2 = 49 - 25$ , i.e. $(1) \;\; n \mid 24$ .
    have dvd_sub {a b c d : ℕ} (hab : a = b) (hdvda : n+1+1 ∣ a + c) (hdvdb : n+1+1 ∣ b + d) :
        n+1+1 ∣ c - d := by
      convert Nat.dvd_sub' hdvda hdvdb using 1
      omega
    rw [show 24 = q 0 ^ 2 - p 0 ^ 2 by rw [hq0, hp0]; norm_num]
    refine dvd_sub ?_ hqsum hpsum
    apply Finset.sum_congr rfl
    intro x _
    rw [show q (x + 1) = p (x + 1) by simp [p, q]]
  intro hndvd p hp
  -- If q is a prime number greater than 3 then we have q^2=1 mod 3 and q^2=1 mod 8.
  have prime_sq_mod {q : ℕ} (hqp : q.Prime) (hq : 3 < q) :
      q^2 ≡ 1 [MOD 3] ∧ q^2 ≡ 1 [MOD 8] := by
    constructor
    . rw [Nat.ModEq, pow_two, Nat.mul_mod]
      have qdiv_add_mod := Nat.div_add_mod q 3
      have : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases q % 3 <;> norm_num
      have : 3 ∣ q := by omega
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hqp] at this
      omega
    rw [Nat.ModEq, pow_two, Nat.mul_mod]
    have qdiv_add_mod := Nat.div_add_mod q 8
    have : q % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases q % 8 <;> norm_num
    all_goals have heven : 2 ∣ q := by omega
    all_goals rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp] at heven
    all_goals omega
  -- Assume  $q_1,q_2, \ldots ,q_n$  are  $n$  distinct primes greater than 3.
  -- Then for  $m \in \{3,8\}$  $S = \sum_{i=1}^n q_i^2 \equiv \sum_{i=1}^n 1 = n \pmod{m}$ ,
  -- i.e. $(2) \;\; m \mid S - n$ .
  have sum_prime_sq_mod : ∑ i ∈ Finset.range (n + 1), p i ^ 2 ≡ n + 1 [MOD 3] ∧
      ∑ i ∈ Finset.range (n + 1), p i ^ 2 ≡ n + 1 [MOD 8] := by
    constructor
    . rw [Nat.ModEq, Finset.sum_nat_mod]
      congr
      nth_rw 2 [← show ∑ i ∈ Finset.range (n + 1), 1 = n + 1 by simp]
      apply Finset.sum_congr rfl
      intro i hi
      change _ ≡ 1 [MOD 3]
      simp at hi
      have := hp _ hi
      have := prime_sq_mod this.1 this.2
      exact this.1
    . rw [Nat.ModEq, Finset.sum_nat_mod]
      congr
      nth_rw 2 [← show ∑ i ∈ Finset.range (n + 1), 1 = n + 1 by simp]
      apply Finset.sum_congr rfl
      intro i hi
      change _ ≡ 1 [MOD 8]
      simp at hi
      have := hp _ hi
      have := prime_sq_mod this.1 this.2
      exact this.2
  -- The fact that 3 and 8 are coprime combined with (2) result in $(3) \;\; 24 \mid S - n$ .
  have three_coprime_eight : Nat.Coprime 3 8 := by norm_num
  rw [Nat.modEq_and_modEq_iff_modEq_mul three_coprime_eight,
    Nat.modEq_iff_dvd] at sum_prime_sq_mod
  -- We know that  $n | S$  (since  $n$  is a rare), implying  $n | S-n$ .
  -- Hence by (1) and (3) every  $n$  satisfying (1) is a rare number.
  zify at hndvd ⊢
  have := Int.dvd_trans hndvd sum_prime_sq_mod
  rw [dvd_sub_comm] at this
  have := Int.dvd_add this (Int.dvd_refl (n+1))
  rw [Nat.cast_add, show (1 : ℤ) = (1 : ℕ) from rfl, Int.sub_add_cancel] at this
  convert this
  norm_cast
