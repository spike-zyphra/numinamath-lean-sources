import Mathlib

theorem number_theory_25756 :
    IsGreatest {n : ℕ | 0 < n ∧ n < 1000 ∧ ∃ m : ℕ, 0 < m ∧ Nat.lcm m n = 3 * m * Nat.gcd m n} 972 := by
  constructor
  · -- Show that 972 is in the set, using m = 18.
    constructor
    · norm_num
    constructor
    · norm_num
    use 18
    constructor
    · norm_num
    -- Verify that lcm(18, 972) = 3 * 18 * gcd(18, 972)
    native_decide
  · -- Show that no larger integer is in the set
    intro n hn
    rcases hn with ⟨hn0, hn1, m, hm0, h⟩
    by_contra h2
    push_neg at h2
    -- We have n > 972, and n < 1000
    have h2 : n > 972 := by omega
    have h3 : n < 1000 := by linarith
    -- From the equation, n = 3 * (Nat.gcd m n) ^ 2
    have h4 : Nat.lcm m n = 3 * m * Nat.gcd m n := h
    have h5 : m * n = 3 * m * (Nat.gcd m n) ^ 2 := by
      have h6 : m * n = Nat.gcd m n * (Nat.lcm m n) := by
        rw [Nat.gcd_mul_lcm]
      rw [h6, h4]
      <;> ring_nf
    have h7 : n = 3 * (Nat.gcd m n) ^ 2 := by
      nlinarith [show 0 < m from hm0]
    -- Now we derive a contradiction from h7
    have h8 : Nat.gcd m n ≤ 18 := by
      nlinarith [h7, show n < 1000 by omega]
    -- Now we can determine all possible values of g = Nat.gcd m n
    interval_cases h : Nat.gcd m n <;> norm_num [h7] at *
    all_goals
      omega