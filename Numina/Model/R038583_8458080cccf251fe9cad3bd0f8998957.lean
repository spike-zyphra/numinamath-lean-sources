import Mathlib

theorem number_theory_160048 (n : ℕ) :
    0 < n ∧ (n + 1) ∣ (2 * n ^ 2 + 5 * n) ↔ n = 2 := by
  constructor
  · -- Forward direction: if 0 < n ∧ (n + 1) ∣ (2 * n ^ 2 + 5 * n), then n = 2
    intro h
    rcases h with ⟨hn_pos, hdiv⟩
    have h1 : (n + 1) ∣ (2 * n ^ 2 + 5 * n) := hdiv
    have h2 : (n + 1) ∣ 3 := by
      have h3 : (n + 1) ∣ (2 * n ^ 2 + 5 * n + 3) := by
        have h4 : (2 * n ^ 2 + 5 * n + 3) = (2 * n + 3) * (n + 1) := by
          ring_nf
        rw [h4]
        simp [Nat.mul_comm]
      have h5 : (n + 1) ∣ (3 : ℕ) := by
        have h6 : (n + 1) ∣ ((2 * n ^ 2 + 5 * n + 3) - (2 * n ^ 2 + 5 * n)) := by
          apply Nat.dvd_sub'
          · exact h3
          · exact h1
        have h7 : ((2 * n ^ 2 + 5 * n + 3) - (2 * n ^ 2 + 5 * n)) = 3 := by
          omega
        rw [h7] at h6
        exact h6
      exact h5
    -- We know that if `d | a` and `d | b` then `d | a - b`.
    -- The idea is that if n + 1 divides both of these expressions
    -- then n + 1 divides their difference, which is 3, so n + 1 divides 3.
    -- Now we need to find all possible values n such that n + 1 divides 3 and n > 0.
    -- So if `n + 1` divides 3, then n + 1 must be a divisor of 3, that is
    -- n + 1 ∈ {1, 3}, hence n ∈ {0, 2}, but n > 0 so n = 2.
    have h8 : (n + 1) ≤ 3 := by
      apply Nat.le_of_dvd (show 0 < (3 : ℕ) by norm_num) h2
    -- Now, find all positive integers n such that n + 1 divides 3
    -- The possible divisors of 3 are 1 and 3
    have h9 : n + 1 = 1 ∨ n + 1 = 3 := by
      interval_cases h : n + 1 <;> try { tauto }
    rcases h9 with h13 | h14
    · -- n + 1 = 1, so n = 0, which contradicts n > 0.
      have hn0 : n = 0 := by
        omega
      linarith
    · -- n + 1 = 3, so n = 2, which is the desired result.
      have hn2 : n = 2 := by
        omega
      exact_mod_cast hn2
  · -- Backward direction: if n = 2, then 0 < n ∧ (n + 1) ∣ (2 * n ^ 2 + 5 * n)
    intro h
    rw [h]
    constructor
    · -- Show that 0 < 2
      norm_num
    · -- Show that 3 divides 18, which is true because 18 = 3 * 6.
      norm_num