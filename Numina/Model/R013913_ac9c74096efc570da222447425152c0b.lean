import Mathlib

theorem algebra_138981 (a b : ℤ) (x : ℤ) :
    x^2 + 10 * a * x + 5 * b + 3 ≠ 0 ∧ x^2 + 10 * a * x + 5 * b - 3 ≠ 0 := by 
  constructor
  · -- Assume x^2 + 10 * a * x + 5 * b + 3 = 0, prove a contradiction.
    intro h
    have h1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
      have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod] at *
    have h2 : x ^ 2 % 5 = 2 := by
      have h_eq : (x ^ 2 + 10 * a * x + 5 * b + 3) % 5 = 0 := by 
        omega 
      simp [Int.add_emod, Int.mul_emod] at h_eq ⊢ 
      all_goals 
        omega 
    omega 
  · -- Assume x^2 + 10 * a * x + 5 * b - 3 = 0, prove a contradiction.
    intro h 
    have h1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
      have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod] at *
    have h2 : x ^ 2 % 5 = 3 := by 
      have h_eq : (x ^ 2 + 10 * a * x + 5 * b - 3) % 5 = 0 := by 
        omega 
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod] at h_eq ⊢ 
      all_goals 
        omega 
    omega