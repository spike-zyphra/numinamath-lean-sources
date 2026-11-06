import Mathlib

/- For two real values of $n$, the equation $9x^2+nx+36=0$ has exactly one solution in $x$. What is the positive value of $n$? -/
theorem algebra_19316 {n : ℝ} :
    (∀ (x : ℝ), 9 * x ^ 2 + n * x + 36 = 0 ↔ x = -n / 18) ∧ n > 0 ↔ n = 36 := by
        constructor
        . -- 证明左到右方向
            intro h1
            -- 分解假设为两部分：方程性质和n为正
            rcases h1 with ⟨h1, h2⟩
            -- 将x = -n/18代入方程
            specialize h1 (-n / 18)
            -- 简化表达式
            simp at h1
            -- 使用环的性质进行标准化
            ring_nf at h1
            -- 得到二次方程
            replace h1 : (n - 36) * (n + 36) = 0:= by linarith
            -- 由n > 0可知 n + 36 ≠ 0
            have h3 : n + 36 ≠ 0:= by linarith
            -- 得到 n = 36
            have g4 : n - 36 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero h3 h1
            linarith
        . -- 证明右到左方向
            intro h1
            constructor
            . -- 证明方程只有一个解
                intro x
                constructor
                . -- 证明若x是解，则x = -n/18
                    intro hx
                    rw [h1] at hx    -- 将n = 36代入方程
                    replace hx : (3 * x + 6) ^ 2 = 0:= by linarith  -- 化简为完全平方形
                    replace hx : 3 * x + 6 = 0:= by exact pow_eq_zero hx  -- 平方为零则本身为零
                    linarith
                . -- 证明若x = -n/18，则x是解
                    intro hx
                    rw [h1] at hx
                    rw [h1]
                    norm_num at hx
                    rw [hx]
                    norm_num
            . -- 证明n > 0
                linarith
