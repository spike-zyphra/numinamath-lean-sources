import Mathlib

/- The equation $y = -4.9t^2 - 3.5t + 2.4$ relates the height $y$ (in meters) to the elapsed time $t$ (in seconds) for a ball thrown downward at 3.5 meters per second from a height of 2.4 meters from the ground. In how many seconds will the ball hit the ground? Express your answer as a decimal rounded to the nearest hundredth. -/
theorem algebra_19089 {t : ℝ} (ht : t ≥ 0) (h : -4.9 * t ^ 2 - 3.5 * t + 2.4 = 0) :
    round (t * 100) / (100 : ℝ)  = 0.43 := by
        -- 第一步：将原方程转化为因式分解形式 (7t-3)(7t+8) = 0 
        replace h : (7 * t -3) * (7 * t + 8) = 0 := by
            ring_nf           -- 使用环形式标准化
            norm_num at h     -- 在假设h中进行数值标准化
            linarith         -- 使用线性算术求解器
        -- 第二步：证明 7t+8 ≠ 0 
        have hpos : 7 * t + 8 ≠ 0 := by linarith
        -- 第三步：得出 7t-3 = 0 
        have h2 : 7 * t - 3 = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero hpos h
        -- 第四步：求解 t = 3/7 
        replace h2 : t = 3 / 7 := by linarith
        -- 最后：代入t值并化简
        subst t              -- 替换t
        rw [round_eq]        -- 使用round_eq引理
        norm_num            -- 数值计算标准化
