import Mathlib

/- The integer solutions to the equation ${{x}^{2}}-xy-5x+5y-1=0$ are ___          ___ or ___          ___. -/
theorem algebra_2774 {x y : ℤ} (h : x^2 - x * y - 5 * x + 5 * y - 1 = 0) :
    (x = 6 ∧ y = 5) ∨ (x = 4 ∧ y = 5) := by 
  have h1 : (x - y) * (x - 5) = 1 := by
    linarith 
  -- From (x - y) * (x - 5) = 1, either (x - y) = 1 and (x - 5) = 1, or (x - y) = -1 and (x - 5) = -1
  cases' (Int.eq_one_or_neg_one_of_mul_eq_one h1) with h2 h2
  · -- Case where (x - y) = 1 and (x - 5) = 1, thus x = 6, y = 5
    have hxy1 : x - y = 1 := by
      linarith
    have hx51 : x - 5 = 1 := by 
      nlinarith
    have hx1 : x = 6 := by 
      linarith
    have hy1 : y = 5 := by 
      linarith
    left
    exact ⟨hx1, hy1⟩
  · -- Case where (x - y) = -1 and (x - 5) = -1, thus x = 4, y = 5
    have hxy2 : x - y = -1 := by
      linarith
    have hx52 : x - 5 = -1 := by 
      nlinarith
    have hx2 : x = 4 := by 
      linarith
    have hy2 : y = 5 := by 
      linarith
    right
    exact ⟨hx2, hy2⟩