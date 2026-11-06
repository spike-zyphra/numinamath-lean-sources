import Mathlib

/- There exist constants $c_2,$ $c_1,$ and $c_0$ such that
\[x^3 + x^2 - 5 = (x - 3)^3 + c_18918 (x - 3)^2 + c_18918 (x - 3) + c_0.\]Find $c_2^2 + c_1^2 + c_0^2.$ -/
theorem algebra_18918 {c0 c1 c2 : ℝ} (h : ∀ x, x^3 + x^2 - 5 = (x - 3)^3 + c2 * (x - 3)^2 + c1 * (x - 3) + c0) :
    c2 ^ 2 + c1 ^ 2 + c0 ^ 2 = 2150 := by
        -- 将 x = 2, 3, 4代入条件，使用线性方程求解
        have h1 := h 3
        have h2 := h 4
        have h3 := h 2
        norm_num at h1 h2 h3
        replace h1 : c0 = 31:= by linarith
        replace h2 : c1 = 33:= by linarith
        replace h3 : c2 = 10:= by linarith
        simp [h1, h2, h3]
        norm_num
