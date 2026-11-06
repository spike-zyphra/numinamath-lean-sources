import Mathlib
/- If $3^{x + y} = 81$ and $81^{x - y} = 3,$ then what is the value of the product $xy$? Express your answer as a common fraction. -/
theorem algebra_21246 {x y : ℝ} (h1 : (3 : ℝ) ^ (x + y)= 81) (h2 : (81 : ℝ) ^ (x - y) = 3) : x * y = 255 / 64 := by
    -- 将第一个等式转换为对数形式
    have h3 : Real.logb 3 (3 ^ (x + y)) = Real.logb 3 81 := by rw [h1]

    -- 将81表示为3^4，并重写第二个等式
    have s :  (81 : ℝ) ^ (x - y) = 3 ^ (4 * (x - y)) := by
        calc _ = ((3 : ℝ) ^ (4 : ℝ)) ^ (x - y) := by rw [show (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) by ring_nf]
             _ = 3 ^ (4 * (x - y)) := symm (Real.rpow_mul (by linarith) 4 (x - y))
    rw [s] at h2

    -- 将第二个等式转换为对数形式
    have h4 : Real.logb 3 (3 ^ (4 * (x - y))) = Real.logb 3 3 := by rw [h2]

    -- 简化分式
    field_simp at h3 h4

    -- 证明 log_3(81) = 4
    have h5 : Real.logb 3 81 = 4:= by
        have h : Real.logb 3 81 = 4 ↔ (3 : ℝ) ^ (4 : ℝ)= 81:= Real.logb_eq_iff_rpow_eq
            (show 0 < 3 by linarith)
            (show 3 ≠ 1 by linarith)
            (show 0 < 81 by linarith)
        replace h := h.2
        apply h
        ring_nf
    rw [h5] at h3
    -- 解出 x 和 y 的值
    have h6 : x = 17 / 8 := by linarith
    have h7 : y = 15 / 8 := by linarith
    -- 计算 x * y
    rw [h6,h7]
    norm_num
