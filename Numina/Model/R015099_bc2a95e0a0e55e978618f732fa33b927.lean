import Mathlib

theorem number_theory_142281 :
    ∃ s : Finset ℕ, s.card = 10 ∧
      (∀ x ∈ s, x > 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬(x ∣ y)) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (x ^ 2) % y = 0) := by 
  use {2^2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29, 
       3^2 * 2 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29, 
       5^2 * 2 * 3 * 7 * 11 * 13 * 17 * 19 * 23 * 29, 
       7^2 * 2 * 3 * 5 * 11 * 13 * 17 * 19 * 23 * 29, 
       11^2 * 2 * 3 * 5 * 7 * 13 * 17 * 19 * 23 * 29, 
       13^2 * 2 * 3 * 5 * 7 * 11 * 17 * 19 * 23 * 29, 
       17^2 * 2 * 3 * 5 * 7 * 11 * 13 * 19 * 23 * 29, 
       19^2 * 2 * 3 * 5 * 7 * 11 * 13 * 17 * 23 * 29, 
       23^2 * 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 29, 
       29^2 * 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23}
  constructor
  · -- Show that the cardinality is 10
    native_decide
  constructor
  · -- Show all elements are positive
    intro x hx
    fin_cases hx <;> norm_num
  constructor
  · -- Show that none divides any other 
    intro x hx y hy hxy
    fin_cases hx <;> fin_cases hy <;> norm_num at *
  · -- Show that the square of each is divisible by all others 
    intro x hx y hy hxy
    fin_cases hx <;> fin_cases hy <;> norm_num at *