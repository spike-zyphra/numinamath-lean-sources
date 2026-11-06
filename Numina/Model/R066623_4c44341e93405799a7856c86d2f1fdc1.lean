import Mathlib

theorem number_theory_258169 (x y : ℕ) (hx : x < 10) (hy : y < 10)
    (h : 1375 ∣ 700000 + 10000 * x + 3000 + 600 + 10 * y + 5) :
    713625 = 700000 + 10000 * x + 3000 + 600 + 10 * y + 5 := by
  interval_cases x <;> interval_cases y <;> omega