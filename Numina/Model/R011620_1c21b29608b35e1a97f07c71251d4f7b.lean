import Mathlib

open Nat

theorem number_theory_134331 :
    ∃ c E N A : ℕ,
      100 ≤ 100 * E + 10 * N + A ∧              -- number is at least 100
      100 * E + 10 * N + A < 1000 ∧             -- number is less than 1000
      E ≠ N ∧ N ≠ A ∧ A ≠ E ∧                   -- all digits are distinct
      c * (100 * E + 10 * N + A) = 2331 ∧       -- scaled by c gives 2331
      c = 9 := by 
        use 9, 2, 5, 9 
        constructor 
        · -- Show that 100 ≤ 100 * E + 10 * N + A 
          norm_num 
        constructor
        · -- Show that 100 * E + 10 * N + A < 1000
          norm_num 
        constructor 
        · -- Show that E ≠ N 
          norm_num 
        constructor 
        · -- Show that N ≠ A 
          norm_num 
        constructor 
        · -- Show that A ≠ E 
          norm_num 
        constructor
        · -- Show that c * (100 * E + 10 * N + A) = 2331 
          all_goals norm_num 
        all_goals norm_num