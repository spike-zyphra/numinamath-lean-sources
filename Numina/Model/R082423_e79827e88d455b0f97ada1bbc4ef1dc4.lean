import Mathlib

theorem number_theory_172344 {x : ℕ} (hx : x > 0) (h : 21 * (x - 6) = 30 * x) :
    x = 14 ∨ x = 13 := by
  omega