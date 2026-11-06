import Mathlib

/- Simplify: $\frac{\sqrt{2.5^2-0.7^2}}{2.7-2.5}$. -/
theorem algebra_21876 : Real.sqrt (2.5^2 - 0.7^2) / (2.7 - 2.5) = 12 := by
  -- 使用 norm_num 将表达式规范化为更简单的形式
  norm_num

  -- 证明 144 = 12² 这个等式
  have h1 : (144 : ℝ) = 12 ^ 2:= by norm_num

  -- 证明 25 = 5² 这个等式
  have h2 : (25 : ℝ) = 5 ^ 2:= by norm_num

  -- 证明 √(12²) = 12，使用实数平方根性质
  have h3 : √((12 : ℝ) ^ 2) = 12:= Real.sqrt_sq (by linarith)

  -- 证明 √(5²) = 5，使用实数平方根性质
  have h4 : √((5 : ℝ) ^ 2) = 5:= Real.sqrt_sq (by linarith)

  -- 使用之前证明的等式进行重写
  rw [h1, h2, h3, h4]

  -- 最后使用 simp 简化表达式
  simp
