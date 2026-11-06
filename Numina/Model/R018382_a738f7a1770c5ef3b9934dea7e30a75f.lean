import Mathlib

theorem algebra_167122 (a b c : ℕ) (h₀ : a + b + c = 12) (h₁ : c - b = 3) :
    (a, b, c) = (9, 0, 3) ∨ (a, b, c) = (7, 1, 4) ∨ (a, b, c) = (5, 2, 5) ∨
    (a, b, c) = (3, 3, 6) ∨ (a, b, c) = (1, 4, 7) := by 
  have h2 : c = b + 3 := by
    omega 
  rw [h2] at h₀ 
  -- Now, simplify to turn into a + 2 * b = 9
  have h3 : a + 2 * b = 9 := by 
    omega 
  have h4 : b ≤ 4 := by 
    omega 
  -- Show that a ≤ 9
  have h5 : a ≤ 9 := by 
    omega 
  -- Show that c ≤ 7
  have h6 : c ≤ 7 := by 
    omega 
  -- Now, since all variables are bounded, perform exhaustive search to check all possibilities
  interval_cases b <;> interval_cases a <;> norm_num [Prod.ext_iff, h2] at *
  <;> omega