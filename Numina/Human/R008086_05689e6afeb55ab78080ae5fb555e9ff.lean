import Mathlib

/- If $x$ is an integer, what is the smallest value of the expression $x^2 - 6x +13$? -/
theorem algebra_19122 : IsLeast {n : ℤ | ∃ x, n = x^2 - 6 * x + 13} 4 := by
  -- 分两部分证明：1) 4是该集合中的元素 2) 4是下界
  constructor <;>
  simp [lowerBounds]
  . -- 第一部分：证明4在集合中
    -- 取 x = 3，代入原表达式
    use 3
    -- 自动计算 3^2 - 6*3 + 13 = 4
    omega
  .  -- 第二部分：证明4是下界
    -- 引入任意元素 a
    intro a
    -- 任何数的平方都大于等于0
    have h : (a - 3) ^ 2 ≥ 0:= by exact sq_nonneg (a - 3)
    -- 展开代数式
    ring_nf at h
    -- 自动完成不等式证明
    omega
