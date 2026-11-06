import Mathlib

theorem number_theory_236220 (n : ℕ) : ¬(Nat.digits 10 (n ^ 2)).sum = 1967 := by
  by_contra h
  have h1 : (Nat.digits 10 (n ^ 2)).sum = 1967 := by
    exact h
  have h2 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
    have h3 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
      omega
    rcases h3 with (h | h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h] 
  have h3 : (n ^ 2) % 9 = 5 := by
    have h4 : (n ^ 2) % 9 = (Nat.digits 10 (n ^ 2)).sum % 9 := by
      rw [Nat.modEq_nine_digits_sum]
      all_goals omega
    rw [h1] at h4
    omega
  omega