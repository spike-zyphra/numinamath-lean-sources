import Mathlib

/- If $a+b=7$ and $a^3+b^3=42$, what is the value of the sum $\dfrac{1}{a}+\dfrac{1}{b}$?  Express your answer as a common fraction. -/
theorem algebra_20478 {a b : ℝ} (h1 : a + b = 7) (h2 : a^3 + b^3 = 42) :
    1 / a + 1 / b = 21 / 43 := by
        -- 用反证法证明 a 和 b 都不为 0
        have ha : a ≠ 0 ∧ b ≠ 0:= by
            constructor
            all_goals
            by_contra H
            subst H
            simp at h1 h2
            subst h1
            linarith
        rcases ha with ⟨ha, hb⟩
        -- 利用 h1 得到 (a + b)^3 = 7^3
        have h3 : (a + b) ^ 3 = 7 ^ 3:= by rw [h1]
        -- 展开 (a + b)^3
        ring_nf at h3
        -- 整理得到 (a^3 + b^3) + 3ab(a + b) = 343
        replace h3 : (a ^ 3 + b ^ 3) + 3 * a * b * (a + b) = 343:= by linarith
        -- 代入 h1 和 h2，即 a + b = 7 和 a^3 + b^3 = 42
        rw [h1, h2] at h3
        -- 解得 ab = 43/3
        replace h3 : a * b = 43 / 3:= by linarith
        -- 证明 1/a + 1/b = (a + b)/(ab) 的代数恒等式
        have h4 : 1 / a + 1 / b = (a + b) / (a * b):= by
            field_simp
            linarith
        -- 代入 h4 中的表达式
        rw [h4]
        -- 将 a + b = 7 和 ab = 43/3 代入
        rw [h1, h3]
        -- 化简得到最终结果 21/43
        norm_num
