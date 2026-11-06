import Mathlib
import Mathlib.Data.Real.Basic

/-What is the $y$-coordinate of the point on the $y$-axis that is equidistant from points $A( -2, 0)$ and $B(-1,4)$?-/
theorem algebra_1552 (y : ℝ) :
    Real.sqrt ((-2)^2 + y^2) = Real.sqrt ((-1)^2 + (4 - y)^2) ↔ y = 13 / 8 := by
    -- 计算两点之间的距离公式
  norm_num
  -- 去掉平方根，通过非负条件等价为根号内的部分相等
  rw [Real.sqrt_inj (by positivity) (by positivity)]
  -- 消去 y^2，化简为线性方程
  ring_nf
  simp only [add_left_inj]
  constructor
  <;> intro <;> linarith
