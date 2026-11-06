import Mathlib

/- A circle is inscribed in a square with perimeter of 32 inches. What is the circumference of the circle, in inches? Express your answer in terms of $\pi$. -/
theorem algebra_20509 (s d : ℝ) (h₁ : 4 * s = 32) (h₂ : d = s * Real.pi) :
    d = 8 * Real.pi := by
        -- 从 4s = 32 推导出 s = 8（正方形的边长）
        replace h₁ : s = 8 := by linarith
        -- 将 s = 8 代入 d = s * π
        rw [h₁] at h₂
        -- 得到最终结果 d = 8π（圆的周长）
        exact h₂
