import Mathlib

open Real

/- Evaluate the infinite geometric series: $$1-\frac{2}{7}+\frac{4}{49}-\frac{8}{343}+\dots$$ -/
theorem algebra_20772 : ∑' n : ℕ, (-2 : ℝ) ^ n / ((7 : ℝ) ^ n) = 7 / 9 := by
  -- 首先证明 (-2)^n / 7^n = (-2/7)^n
  have h : ∀ n : ℕ, (-2 : ℝ) ^ n / ((7 : ℝ) ^ n) = (-2 / 7) ^ n:= by
    intro n
    ring_nf
    calc _ = ((-2 : ℝ) * (1 / 7)) ^ n:= by exact Eq.symm (mul_pow (-2) (1 / 7) n)
         _ = _:= by ring_nf

  -- 使用h简化表达式
  simp_rw [h]
  ring_nf
  -- 应用几何级数公式：当|r|<1时，∑(r^n) = 1/(1-r)
  rw [tsum_geometric_of_abs_lt_one]
  -- 最后化简得到 7/9
  ring
  -- 这里 r = -2/7，显然|-2/7| < 1
  norm_num [abs_div]
