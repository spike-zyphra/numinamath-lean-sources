import Mathlib

theorem algebra_20991 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : 10 * x * y + 14 * x + 15 * y = 166) : x + y = 6 := by 
  have h1 : x ≤ 11 := by 
    by_contra hx'
    push_neg at hx'
    have h2 : 10 * x * y + 14 * x + 15 * y > 166 := by
      have h3 : x ≥ 12 := by linarith 
      have h4 : y ≥ 1 := by nlinarith 
      nlinarith [h3, h4]
    linarith [h, h2]
  interval_cases x <;> omega