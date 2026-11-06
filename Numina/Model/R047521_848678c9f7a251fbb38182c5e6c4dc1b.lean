import Mathlib

theorem algebra_322163 (a b : ℤ) (x : ℤ) :
    x^2 + 10 * a * x + 5 * b + 3 ≠ 0 ∧ x^2 + 10 * a * x + 5 * b - 3 ≠ 0 := by
  constructor
  · -- Assume x² + 10ax + 5b + 3 = 0, prove contradiction
    intro h
    have h1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
      have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
        simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h2 : (x ^ 2 + 10 * a * x + 5 * b + 3) % 5 = 0 := by
      omega
    have h3 : x ^ 2 % 5 = 2 := by
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod] at h2 ⊢
      omega
    omega
  · -- Assume x² + 10ax + 5b - 3 = 0, prove contradiction
    intro h
    have h1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
      have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
        simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h2 : (x ^ 2 + 10 * a * x + 5 * b - 3) % 5 = 0 := by 
      omega
    have h3 : x ^ 2 % 5 = 3 := by 
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod] at h2 ⊢
      omega
    omega