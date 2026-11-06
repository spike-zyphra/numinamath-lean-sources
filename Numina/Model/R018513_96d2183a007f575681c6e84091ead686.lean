import Mathlib

theorem number_theory_255292 (n : ℕ) :
    (n + 2)^3 ≠ (n^3 + (n + 1)^3) := by
  intro h
  have eq1 : (n + 2) ^ 3 = n ^ 3 + (n + 1) ^ 3 := by
    omega
  have eq2 : n ≤ 8 := by
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 9 := by omega
    have eq7 : (n + 2 : ℕ) ^ 3 < n^3 + (n + 1 : ℕ) ^ 3 := by
      nlinarith [sq_pos_of_pos (show 0 < n by omega), sq_pos_of_pos (show 0 < n + 1 by omega),
        sq_pos_of_pos (show 0 < n + 2 by omega), 
        pow_pos (show 0 < n by omega) 2, pow_pos (show 0 < n by omega) 3, 
        sq_nonneg ((n) : ℕ), sq_nonneg ((n + 1) : ℕ), sq_nonneg ((n + 2) : ℕ), 
        mul_pos (show (0 : ℕ) < n by omega) (show (0 : ℕ) < n + 1 by omega), 
        mul_pos (show (0 : ℕ) < n + 1 by omega) (show (0 : ℕ) < n + 2 by omega)]
    omega
  interval_cases n <;> omega