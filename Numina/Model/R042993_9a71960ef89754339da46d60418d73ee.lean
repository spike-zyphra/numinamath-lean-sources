import Mathlib

theorem algebra_190883 {k : ℕ} (hk : ¬(∃ f : Polynomial ℤ, f ∣ X ^ 2 + X + 1 ∧ f ∣ X ^ (2 * k) + 1 + (X + 1) ^ (2 * k))) :
    3 ∣ k := by 
  by_contra h
  push_neg at h 
  have h1 : k % 3 = 1 ∨ k % 3 = 2 := by 
    omega 
  -- Show a contradiction by constructing a common divisor
  have h2 : ∃ f : Polynomial ℤ, f ∣ X ^ 2 + X + 1 ∧ f ∣ X ^ (2 * k) + 1 + (X + 1) ^ (2 * k) := by 
    use 1
    constructor 
    · -- Show that 1 divides X^2 + X + 1 
      use X ^ 2 + X + 1
      all_goals ring 
    · -- Show that 1 divides X ^ (2 * k) + 1 + (X + 1) ^ (2 * k)
      use X ^ (2 * k) + 1 + (X + 1) ^ (2 * k)
      all_goals ring 
  contradiction