import Mathlib
open Real

theorem algebra_1589 {x : ℝ} (hx : (7 * x - 1) / 0.024 = (1 - 0.2 * x) / 0.018 - (5 * x + 1) / 0.012) :
    x = 5 / 259 := by
        norm_num at hx ⊢
        linarith