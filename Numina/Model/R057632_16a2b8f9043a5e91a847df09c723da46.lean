import Mathlib

theorem algebra_102964 (x : ℝ) (h : ∃ y : ℝ, 4 * y ^ 2 + 4 * x * y + x + 6 = 0) :
    x ≤ -2 ∨ x ≥ 3 := by
  rcases h with ⟨y, hy⟩
  have h1 : 16 * (x ^ 2 - x - 6) ≥ 0 := by
    nlinarith [sq_nonneg (4 * y + 2 * x)]
  have h2 : x ^ 2 - x - 6 ≥ 0 := by 
    nlinarith
  have h3 : (x ≤ -2) ∨ (x ≥ 3) := by
    by_cases h4 : x ≤ -2
    · left
      exact h4
    · -- If x > -2, then since x^2 - x - 6 >= 0, it must be that x >= 3
      have h5 : x > -2 := by linarith
      have h6 : x ^ 2 - x - 6 ≥ 0 := by nlinarith
      have h7 : x ≥ 3 := by nlinarith [sq_nonneg (x - 3)]
      right
      linarith
  exact h3