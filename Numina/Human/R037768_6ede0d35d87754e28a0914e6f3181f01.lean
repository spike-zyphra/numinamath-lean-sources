import Mathlib

/- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem algebra_19792 (a : ℝ) (h : a + 1 ≥ 0):
    Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 ↔ a = 8 := by
        -- 分两步证明：充分性 + 必要性
        constructor
        -- 充分性
        .
            intro ha
            rw [show 16 + 16 * a = 16 * (1 + a) by ring_nf] at ha
            rw [show √(16 * (1 + a)) = √16 * √(1 + a) by refine Real.sqrt_mul' 16 (by linarith)] at ha
            rw [show (16 : ℝ) = 4 ^ 2 by ring_nf] at ha
            rw [show √(4 ^ 2) = 4 by refine Real.sqrt_sq (by linarith)] at ha
            rw [show 4 + 4 * √(1 + a) = 4 * (1 + √(1 + a)) by ring_nf] at ha
            have h1 : 1 + √(1 + a) ≥ 0:= by linarith only [Real.sqrt_nonneg (1 + a)]
            rw [show √(4 * (1 + √(1 + a))) = √4 * √(1 + √(1 + a)) by refine Real.sqrt_mul' 4 h1] at ha
            rw [show (4 : ℝ) = 2 ^ 2 by ring_nf] at ha
            rw [show √(2 ^ 2) = 2 by refine Real.sqrt_sq (by linarith)] at ha
            replace ha : √(1 + √(1 + a)) = 2:= by linarith
            replace ha : √(1 + √(1 + a)) ^ 2 = 2 ^ 2:= by rw [ha]
            rw [show √(1 + √(1 + a)) ^ 2 = 1 + √(1 + a) by exact Real.sq_sqrt h1] at ha
            replace ha : √(1 + a) = 3:= by linarith
            replace ha : √(1 + a) ^ 2 = 3 ^ 2:= by rw [ha]
            rw [show √(1 + a) ^ 2 = 1 + a by refine Real.sq_sqrt (by linarith)] at ha
            linarith
        -- 必要性
        .
            intro ha
            rw [ha]
            norm_num
            rw [show (144 : ℝ) = 12 ^ 2 by ring_nf]
            rw [show (9 : ℝ) = 3 ^ 2 by ring_nf]
            rw [show √(12 ^ 2) = 12 by refine Real.sqrt_sq (by linarith)]
            rw [show √(3 ^ 2) = 3 by refine Real.sqrt_sq (by linarith)]
            norm_num
            rw [show (4 : ℝ) = 2 ^ 2 by ring_nf]
            rw [show (16 : ℝ) = 4 ^ 2 by ring_nf]
            rw [show √(2 ^ 2) = 2 by refine Real.sqrt_sq (by linarith)]
            rw [show √(4 ^ 2) = 4 by refine Real.sqrt_sq (by linarith)]
            norm_num
