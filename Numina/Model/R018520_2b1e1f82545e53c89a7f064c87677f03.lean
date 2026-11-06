import Mathlib

theorem number_theory_41302 (x : ℕ) (hx : x * 9 = 2 * 23 * 17 + 1 * 23 + 5) :
    x = 90 := by
  norm_num at hx
  omega