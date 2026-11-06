import Mathlib

theorem algebra_170467 (x : ℝ) (hx : x > 0) (h : 5 * x = 50 + 2.5 * x * 30) :
    x ≤ 130 := by 
        norm_num at h 
        linarith