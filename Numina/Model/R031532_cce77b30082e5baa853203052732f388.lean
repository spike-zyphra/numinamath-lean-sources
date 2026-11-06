import Mathlib

theorem number_theory_128189 (a b : ℤ) :
    a^2 + b^2 ≠ 2023 ∧ a^5 - 2 * b^2 ≠ 2020 := by
  constructor
  · -- Assume that $a^2 + b^2 = 2023$ has a solution.
    by_contra h
    have eq1 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1] at *
    have eq2 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
      have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1] at *
    have eq3 : (a ^ 2 + b ^ 2 : ℤ) % 4 = 0 ∨ (a ^ 2 + b ^ 2 : ℤ) % 4 = 1 ∨ (a ^ 2 + b ^ 2 : ℤ) % 4 = 2 := by
      omega
    have h1 : (2023 : ℤ) % 4 = 3 := by norm_num
    have h2 : (a ^ 2 + b ^ 2 : ℤ) % 4 = 3 := by
      omega
    omega
    all_goals try { tauto }
  · -- Assume that $a^5 - 2b^2 = 2020$ has a solution.
    by_contra h
    have h1 : a^5 - 2 * b^2 = 2020 := by linarith
    have h2 : a ^ 5 % 11 = 0 ∨ a ^ 5 % 11 = 1 ∨ a ^ 5 % 11 = 10 := by
      have h11 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h11, Int.sub_emod] at *
    have h3 : (2 * b^2) % 11 = 0 ∨ (2 * b^2) % 11 = 2 ∨ (2 * b^2) % 11 = 6 ∨ (2 * b^2) % 11 = 7 ∨ (2 * b^2) % 11 = 8 ∨ (2 * b^2) % 11 = 10 := by
      have h11 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h11, Int.sub_emod] at *
    have h4 : (a ^ 5 - 2 * b ^ 2) % 11 = 7 := by
      omega
    have h5 : (2020 : ℤ) % 11 = 7 := by norm_num
    omega
    all_goals try { tauto }