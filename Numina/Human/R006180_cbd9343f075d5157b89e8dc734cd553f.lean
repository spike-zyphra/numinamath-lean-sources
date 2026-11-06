import Mathlib

/-
Let $n$ be a positive integer, and $ n ^ { n } $ can divide $ 8 ^ { ( 8 ^ { 8 } }) $, then the maximum value of $n$ is

A: $ 2 ^ { 1 6 } $

B: $ 2 ^ { 2 1 } $

C: $ 2 ^ { 2 2 } $

D: $ 2 ^ { 2 3 } $

E: $ 2 ^ { 2 4 } $
-/

theorem number_theory_630283:
IsGreatest {n:ℕ | 0< n ∧ ( (n^n) ∣ 8^(8^8))} (2^21) := by
  unfold IsGreatest
  unfold upperBounds
  simp only [Set.mem_setOf_eq]

  --We rewrite 8^8^8 to be 2 ^(3*2^24).
  have p8: 8 ^ (8^8) = 2 ^ (3*2^24) := by 
    have : 8 = 2^3 := by norm_num
    nth_rw 1 [this]
    rw [Nat.pow_mul]
    have : 8^8 = 2^24 := by 
      nth_rw 1 [this]
      rw [←Nat.pow_mul]
    rw [this]
  rw [p8]

  constructor
  constructor

  exact Nat.two_pow_pos 21

  --2^21 divides 8^8^8.Simple verification.
  have : (2 ^ 21) ^ 2 ^ 21  = 2^(21 * 2^21) := by rw [Nat.pow_mul]
  rw [this]
  apply pow_dvd_pow
  norm_num

  --For every a such that a^a divides 8^8^8, we have that a is a power of 2. Then, we simple check the exponent to make sure that it is at most 3*2^24.
  intro a ⟨apos, ha⟩
  have ub : a ^ a ≤ 2^(3*2^24) := by apply Nat.le_of_dvd; exact Nat.two_pow_pos (3*2^24); exact ha
  rw [Nat.dvd_prime_pow] at ha
  obtain ⟨i, hi⟩ := ha
  have : a ∣ 2^i := by 
    use (a^(a-1))
    rw [mul_comm]
    rw [←pow_succ]
    have : a - 1 + 1 = a := by omega
    rw [this]
    symm
    exact hi.right
  rw [Nat.dvd_prime_pow] at this
  obtain ⟨k, hk⟩ := this
  obtain ⟨_,hk⟩ := hk

  have : a^a = 2^(k*2^k) := by
    rw[ hk]
    rw [Nat.pow_mul]
  rw [this] at ub

  have : (k * 2 ^ k) ≤ (3 * 2 ^ 24) := by 
    rw [pow_le_pow_iff_right₀] at ub
    exact ub
    norm_num
  have : k ≤ 21 := by 
    by_contra
    have kge22 : 22 ≤ k := by omega
    have : 2^22 ≤ 2^k := by rw [pow_le_pow_iff_right₀]; exact kge22; norm_num
    nlinarith
  rw [hk]
  rw [pow_le_pow_iff_right₀]
  exact this
  linarith; 
  repeat norm_num