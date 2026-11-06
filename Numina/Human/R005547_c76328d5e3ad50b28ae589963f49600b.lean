import Mathlib
theorem Combinatorics_608761 : (5 : ℚ) / 27 = 5 / 27 := by
  -- 使用 norm_num 来验证分数的正确性
  norm_num
  -- 使用 rfl 来确认等式的正确性
  <;> rfl
  -- 再次使用 norm_num 来确保所有计算步骤的正确性
  <;> norm_num
  -- 最后使用 rfl 来确认最终结果的正确性
  <;> rfl