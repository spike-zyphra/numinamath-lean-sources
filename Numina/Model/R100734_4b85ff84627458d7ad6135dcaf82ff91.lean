import Mathlib

theorem algebra_203891 {x : ℝ} (hx : 0 < x) (h1 : (1 - 90 / 100) * x = (1 + 320 / x) * x)
    (h2 : (1 - 70 / 100) * x = (1 - 160 / x) * x) :
    x = 1840 := by
        have eq1 : (1 - 90 / 100 : ℝ) * x = (1 + 320 / x) * x := h1
        have eq2 : (1 - 70 / 100 : ℝ) * x = (1 - 160 / x) * x := h2
        have hx' : x ≠ 0 := by linarith
        field_simp at eq1 eq2
        nlinarith [sq_pos_of_pos hx]