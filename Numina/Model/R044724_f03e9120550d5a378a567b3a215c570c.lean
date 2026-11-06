import Mathlib

open Nat

theorem inequalities_99537 (n : ℕ) : 2^n + 2 > n^2 := by
  have h1 : 2 ^ 0 + 2 > (0 : ℕ) ^ 2 := by norm_num 
  have h2 : 2 ^ 1 + 2 > (1 : ℕ) ^ 2 := by norm_num 
  have h3 : 2 ^ 2 + 2 > (2 : ℕ) ^ 2 := by norm_num 
  have h4' : 2 ^ 3 + 2 > (3 : ℕ) ^ 2 := by norm_num
  have h5 : ∀ (n : ℕ), n ≥ 4 → 2 ^ n + 2 > n ^ 2 := by 
    intro n hn 
    have base := show 2 ^ 4 + 2 > (4 : ℕ) ^ 2 by norm_num 
    have step : ∀ (n : ℕ), n ≥ 4 → 2 ^ n + 2 > n ^ 2 → 2 ^ (n + 1) + 2 > (n + 1) ^ 2 := by 
      intro n hn h
      have eq1 : 2 ^ (n + 1) = 2 * (2 ^ n) := by ring 
      have eq2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring 
      have eq3 : 2 ^ (n + 1) + 2 = 2 * (2 ^ n) + 2 := by ring 
      have h6 : 2 * (2 ^ n) + 2 > n ^ 2 + 2 * n + 1 := by 
        nlinarith [sq_nonneg ((2 ^ n : ℕ) - (n : ℕ) ^ 2 + 2), sq_nonneg ((n : ℕ) - 3), sq_nonneg ((2 ^ n : ℕ) - 2 * (n : ℕ) ^ 2), 
          pow_pos (show (0 : ℕ) < 2 by norm_num) n, sq_nonneg (((n + 1) : ℕ) ^ 2 - (2 ^ (n + 1)) + 2), 
            sq_nonneg ((2 ^ n : ℕ) - (n + 1) ^ 2), sq_nonneg ((2 * (n : ℕ) - 3)), h]
      linarith [eq3, h6, eq2]
    exact Nat.le_induction base step n hn 
  by_cases h' : n < 4 
  · -- Base cases n < 4
    interval_cases n <;> norm_num 
  · -- Inductive step n >= 4 
    have h9 : n ≥ 4 := by linarith
    specialize h5 n h9 
    exact h5