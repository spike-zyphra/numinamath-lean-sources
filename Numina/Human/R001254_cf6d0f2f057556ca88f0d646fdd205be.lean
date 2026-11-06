import Mathlib

/- When the expression $-2x^2-20x-53$ is written in the form $a(x+d)^2+e$, where $a$, $d$, and $e$ are constants, what is the sum $a+d+e$? -/
theorem algebra_22138 {a d e : ℝ} (h : ∀ x, -2 * x ^ 2 - 20 * x - 53 = a * (x + d) ^ 2 + e) :
    a + d + e = 0 := by
    -- 将 x = 0 代入等式
    have h1 := h 0
    -- 将 x = 1 代入等式
    have h2 := h 1
    -- 将 x = -1 代入等式
    have h3 := h (-1)
    -- 通过消元得到：22 = -a(1 + 2d)
    have h4 : 22 = -a * (1 + 2 * d):= by linarith
    -- 通过消元得到：-18 = -a(1 - 2d)
    have h5 : -18 = -a * (1 - 2 * d):= by linarith
    -- 解出 a = -2
    have h6 : a = -2 := by linarith
    -- 将 a = -2 代入之前的所有等式
    rw [h6] at h1 h2 h3 h4 h5
    -- 解出 d = 5
    have h7 : d = 5:= by linarith
    -- 将 d = 5 代入之前的所有等式
    rw [h7] at h1 h2 h3 h4 h5
    -- 使用线性算术求解最终结果
    linarith
