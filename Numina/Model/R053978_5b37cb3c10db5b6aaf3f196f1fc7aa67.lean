import Mathlib

theorem algebra_3253 {x : ℝ} (hx : x = 250 * 24) :
    (x - 5000) / 5000 * 100 = 20 := by
        rw [hx]
        norm_num