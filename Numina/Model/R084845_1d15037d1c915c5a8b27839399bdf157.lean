import Mathlib

theorem number_theory_187 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : x ^ 2 + y ^ 2 = 1997) : x + y = 63 := by
  have h1 : x ≤ 44 := by
    nlinarith
  have h2 : y ≤ 44 := by
    nlinarith
  interval_cases x <;> interval_cases y <;> omega