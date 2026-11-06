import Mathlib

theorem algebra_221384 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y = 100 + 40) (h2 : y * 3 = x * 40 + 100) :
    x = 120 := by
  have h3 : x ≤ 140 := by
    nlinarith
  have h4 : y ≤ 140 := by
    nlinarith
  interval_cases x <;> omega