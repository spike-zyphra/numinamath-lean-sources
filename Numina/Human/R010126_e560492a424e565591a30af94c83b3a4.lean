import Mathlib

/- The length of a rectangle is twice its width. Given the length of the diagonal is $5\sqrt{5}$, find the area of the rectangle. -/
theorem algebra_21524 {l w : ℝ} (hl : l = 2 * w) (hw : w > 0)
    (h : l ^ 2 + w ^ 2 = (5 * Real.sqrt 5) ^ 2) : l * w = 50 := by
        -- 对 h 进行代数化简
        ring_nf at h
        -- 证明并使用 √5 ^ 2 = 5
        rw [show √5 ^ 2 = 5 by exact Real.sq_sqrt (by linarith) ] at h
        ring_nf at h
        -- 将 l = 2w 代入方程
        rw [hl] at h
        ring_nf at h
        -- 化简得到 w ^ 2 = 25
        replace h : w ^ 2 = 25:= by linarith
        -- 转化为 (w - 5)(w + 5) = 0 的形式
        replace h : (w - 5) * (w + 5) = 0:= by linarith
        -- 证明 w + 5 ≠ 0（因为已知 w > 0）
        have h1 : w + 5 ≠ 0:= by linarith
        -- 由 (w - 5)(w + 5) = 0 且 w + 5 ≠ 0 得到 w - 5 = 0
        replace h : w - 5 = 0:= eq_zero_of_ne_zero_of_mul_right_eq_zero h1 h
        -- 得到 w = 5
        replace h : w = 5:= by linarith
        -- 将 w = 5 代入 l = 2w
        rw [h] at hl
        ring_nf at hl
        -- 最后代入 w = 5 和 l = 10 计算面积
        rw [h, hl]
        norm_num
