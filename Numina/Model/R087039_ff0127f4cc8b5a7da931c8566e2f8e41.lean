import Mathlib

theorem algebra_258523 (x y : ℕ) (h : x + y = 11) :
    x * y ≤ 30 := by 
  have h1 : y = 11 - x := by 
    omega
  rw [h1]
  by_cases h2 : x ≤ 11
  · -- Since $x \leq 11$, we can check all cases
    interval_cases x <;> omega
  · -- x > 11
    have h3 : x > 11 := by omega
    have h4 : (11 - x) = 0 := by
      omega
    rw [h4]
    nlinarith