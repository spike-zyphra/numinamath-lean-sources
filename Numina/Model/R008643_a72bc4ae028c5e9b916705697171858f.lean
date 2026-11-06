import Mathlib

theorem algebra_232769 {x : ℝ} (hx : x > 0) (h : 56 = x * (1 + x / 100)) :
    x = 40 := by
        have h1 : x ^ 2 + 100 * x - 5600 = 0 := by
            nlinarith [h]
        have h2 : (x - 40) * (x + 90) = 0 := by
            nlinarith [h1]
        cases' (mul_eq_zero.1 h2) with h3 h4
        · linarith
        · linarith