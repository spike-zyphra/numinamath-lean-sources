import Mathlib

/- The points $(x, y)$ represented in this table lie on a straight line. The point $(13, q)$ lies on the same line. What is the value of $p + q?$ Express your answer as a decimal to the nearest tenth. $$\begin{array}{c|c}
x & y \\ \hline
2 & -5 \\
p & -14 \\
p+2 & -17 \\
\end{array}$$ -/
theorem algebra_18825 (p q a b: ℝ) (h₀ : a * 2 + b = -5) (h₁ : a * p + b = -14) (h₂ : a * (p + 2) + b = -17)
    (h₃ : a * 13 + b = q) :
    p + q = -13.5 := by
        -- 从 h₀ 推导出 a * 2 = -3
        have h₄ : a * 2 = -3:= by linarith
        -- 计算出斜率 a = -3/2
        replace h₄ : a = -3 / 2:= by linarith
        -- 将 a = -3/2 代入其他方程
        subst h₄
        -- 简化 h₁, h₂, h₃ 中的代数表达式
        ring_nf at h₁ h₂ h₃
        -- 推导出 p + q = -27/2
        have h₅ : p + q = -27 / 2:= by linarith
        -- 将 p + q = -27/2 代入目标等式
        rw [h₅]
        -- 最终化简得到 -27/2 = -13.5
        ring_nf