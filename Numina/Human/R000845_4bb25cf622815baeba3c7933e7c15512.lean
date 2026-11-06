import Mathlib

/- What is the value of the arithmetic series $28 + 30 + 32 + \cdots + 86$? -/
theorem algebra_18569 : ∑ i in Finset.range 30, (28 + 2 * i) = 1710 := by
  -- 第一步：将求和式拆分为常数项和变量项之和
  have h1 : ∑ i in Finset.range 30, (28 + 2 * i) = ∑ i in Finset.range 30, 28 + ∑ i in Finset.range 30, 2 * i := rfl

  -- 第二步：计算常数项之和：28 × 30
  have h2 : ∑ i in Finset.range 30, 28 = 28 * 30 := by apply Finset.sum_const

  -- 第三步：将系数2提取出来
  have h3 : ∑ i in Finset.range 30, 2 * i = 2 * ∑ i in Finset.range 30, i := rfl

  -- 第四步：使用等差数列求和公式：1+2+...+n = n(n-1)/2
  have h4 : ∀ n : ℕ, ∑ i in Finset.range n, i = n * (n - 1) / 2 := fun n => Finset.sum_range_id n
  specialize h4 30
  rw [h4] at h3
  rw [h2, h3] at h1
  rw [h1]
