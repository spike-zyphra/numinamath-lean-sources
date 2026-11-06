import Mathlib

/- A rectangular patio has an area of $180$ square feet and a perimeter of $54$ feet. What is the length of the diagonal (in feet) squared? -/
theorem algebra_19423 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h₀ : l * w = 180) -- 面积等于180
    (h₁ : 2 * (l + w) = 54) : -- 周长等于54
    l^2 + w^2 = 369 := by
        -- 简化周长方程，得到长和宽之和
        replace h₁ : l + w = 27:= by linarith

        -- 使用平方差公式：(l + w)² - 2lw = l² + w²
        calc _ = (l + w) ^ 2 - 2 * (l * w):= by ring_nf
             -- 代入 l + w = 27 和 l * w = 180
             _ = 27 ^ 2 - 2 * 180:= by rw [h₀,h₁]
             -- 计算最终结果：729 - 360 = 369
             _ = 369:= by norm_num
