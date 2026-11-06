import Mathlib

theorem algebra_192388 (x : ℝ) (hx : x ≠ 0) (h : (x / 4) * 1.04 = (4 * x) * 1.04) :
    |(x / 4) * 1.04 - (4 * x) * 1.04| / (x / 4) * 1.04 = 0.16 / 100 := by
  have h1 : x = 0 := by
    norm_num at h
    linarith
  contradiction