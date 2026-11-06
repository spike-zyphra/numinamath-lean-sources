import Mathlib

/- Simplify $\sqrt{32670}$. -/
theorem algebra_21147 : Real.sqrt 32670 = 33 * Real.sqrt 30 := by
    calc _ = √(33 ^ 2 * 30) := by ring_nf    -- 将 32670 重写为 33² * 30
         _ = √(33 ^ 2) * √30 := by rw [Real.sqrt_mul (by linarith) 30]    -- 使用根号乘法法则：√(a*b) = √a * √b
         _ = 33 * √30 := by rw [Real.sqrt_sq (show 0 ≤ 33 by linarith)]   -- 化简 √(33²) = 33，因为 33 ≥ 0
         
