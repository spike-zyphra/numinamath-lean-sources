import Mathlib

theorem number_theory_259529 (x : ℕ) (hx : x > 0) (h : x / 9 = (x - x / 9) * 8) :
    x = 512 := by
  omega