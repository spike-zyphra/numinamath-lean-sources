import Mathlib

theorem algebra_267572 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : (5 * 100 + 14) / 7 = 5 * 100 + 9) (h2 : (5 * 100 + 14) / 7 < 5 * 100 + 10) :
    ¬(a = 10.5 ∧ b = 5 * 100 + 14) := by
  norm_num at h1