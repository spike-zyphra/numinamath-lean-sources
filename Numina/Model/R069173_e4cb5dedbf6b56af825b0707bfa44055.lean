import Mathlib

theorem algebra_258825 {x : ℝ} (hx : x ≠ 0) (h : 12 * x + 10 * x = 12 * (1 - 10 / 100) * x + 10 * (1 + 2 / 100) * x) :
    (12 * (1 - 10 / 100) * x + 10 * (1 + 2 / 100) * x - 12 * x - 10 * x) / (12 * x + 10 * x) = 4 / 100 := by
        have h1 : x = 0 := by
            linarith 
        contradiction