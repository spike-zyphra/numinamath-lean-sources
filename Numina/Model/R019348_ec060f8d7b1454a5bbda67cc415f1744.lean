import Mathlib

theorem number_theory_115673 (n : ℤ) : 2730 ∣ n^13 - n := by
  have h1 : n ^ 13 % 2 = n % 2 := by
    have h11 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h11 with (h | h) <;> simp [pow_succ, Int.mul_emod, Int.sub_emod, h]
    all_goals omega
  have h2 : n ^ 13 % 3 = n % 3 := by
    have h22 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h22 with (h | h | h) <;> simp [pow_succ, Int.mul_emod, Int.sub_emod, h]
    all_goals omega
  have h3 : n ^ 13 % 5 = n % 5 := by
    have h33 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h33 with (h | h | h | h | h) <;> simp [pow_succ, Int.mul_emod, Int.sub_emod, h]
    all_goals omega
  have h4 : n ^ 13 % 7 = n % 7 := by
    have h44 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h44 with (h | h | h | h | h | h | h) <;> simp [pow_succ, Int.mul_emod, Int.sub_emod, h]
    all_goals omega
  have h5 : n ^ 13 % 13 = n % 13 := by
    have h55 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega
    rcases h55 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.mul_emod, Int.sub_emod, h]
    all_goals omega
  -- Now using the Chinese Remainder Theorem
  -- From the individual congruences we derived, we can combine them
  -- 2730 divides n^13 -n, as required
  omega