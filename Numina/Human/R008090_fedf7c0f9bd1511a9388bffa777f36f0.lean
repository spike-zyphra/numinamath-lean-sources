import Mathlib

/- A parabola with equation $y=x^2+bx+c$ passes through the points $(2,3)$ and $(4,3)$. What is $c$? -/
theorem algebra_21812 (b c : ℝ) (f : ℝ → ℝ) (hf : ∀x, f x = x ^ 2 + b * x + c) (h1: 3 = f 2) (h2: 3 = f 4) :
    c = 11 := by
        -- 将函数定义 f x = x^2 + bx + c 代入两个已知点
        rw [hf] at h1 h2
        -- 得到两个方程：
        -- 3 = 2^2 + 2b + c  (即 3 = 4 + 2b + c)
        -- 3 = 4^2 + 4b + c  (即 3 = 16 + 4b + c)
        -- 通过 linarith 自动解这个方程组得到 c = 11
        linarith
