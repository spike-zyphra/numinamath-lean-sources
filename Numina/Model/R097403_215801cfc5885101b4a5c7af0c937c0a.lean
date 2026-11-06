import Mathlib

theorem algebra_177070 (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
    (h : m * 7 + n * 8 = (m + n) * 16 / 2) :
    m * 28 + n * 21 = (m + n) * 16 := by
  nlinarith