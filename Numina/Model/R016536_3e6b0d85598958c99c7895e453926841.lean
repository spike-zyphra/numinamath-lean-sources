import Mathlib

open Nat

theorem inequalities_311829 (n : ℕ) : 2^n + 2 > n^2 := by
  have h1 : ∀ (n : ℕ), 2^n + 2 > n^2 := by 
    intro n 
    induction n with 
    | zero => 
      all_goals norm_num 
    | succ n ih =>
      have eq1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      by_cases h : n < 4
      · -- n < 4, so n is 0, 1, 2, 3
        interval_cases n <;> norm_num at ih ⊢ <;> omega 
      · -- n ≥ 4
        have h3 : n ≥ 4 := by linarith 
        have h4 : (2 : ℕ) ^ (n + 1) + 2 > (n + 1) ^ 2 := by 
          have eq2 : (2 : ℕ) ^ (n + 1) + 2 = 2 * (2 ^ n) + 2 := by ring 
          rw [eq2] 
          have h5 : 2 * (2 ^ n) + 2 > n ^ 2 + 2 * n + 1 := by
            nlinarith [sq_nonneg ((n : ℕ) : ℕ), sq_nonneg ((n - 1 : ℕ) : ℕ), 
                      sq_nonneg ((n : ℕ) - 2 : ℤ), sq_nonneg ((n : ℕ) - 3 : ℤ), 
                      sq_nonneg ((2 ^ n : ℕ) - (n ^ 2) : ℤ), 
                      sq_nonneg ((2 ^ n) : ℤ), 
                      sq_nonneg ((n : ℕ) : ℤ), 
                      sq_pos_of_pos (show 0 < (2 : ℕ) by norm_num), 
                      pow_pos (show 0 < (2 : ℕ) by norm_num) n, 
                      ih, 
                      sq_pos_of_pos (show 0 < (2 : ℕ) by norm_num), 
                      sq_nonneg ((n - 1 : ℕ))]
          nlinarith 
        linarith 
  specialize h1 n 
  simpa using h1