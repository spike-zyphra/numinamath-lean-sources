import Mathlib

/-Find $\left(\frac{1+i}{\sqrt{2}}\right)^{46}$.-/
theorem algebra_14362 : ((1 + Complex.I) / Real.sqrt 2) ^ 46 = -Complex.I := by
  have h : ((1 + Complex.I) / Real.sqrt 2)^2 = Complex.I :=
    calc
    --分子分母同时平方，并展开分子
    _ = (1 +2*Complex.I+ Complex.I^2) / ((Real.sqrt 2)^2) := by
      rw[div_pow (1 + Complex.I)  (Real.sqrt 2) 2]
      simp[add_sq 1 Complex.I]
    --利用复数单位i的平方等于-1化简
    -- 注意分母的类型是ℝ
    _ = (1 +2*Complex.I+-1) / (2:ℝ):= by
      rw[Complex.I_sq]
      --将↑√2 ^ 2 转化为↑(√2 ^ 2)
      rw[←Complex.ofReal_pow √2 2]
      -- (√2 ^ 2)是实数，利用Real.sq_sqrt化简
      rw[Real.sq_sqrt]
      linarith
    _ = Complex.I := by simp
  calc
  --将(1 + Complex.I) / Real.sqrt 2)^46转化为((1 + Complex.I) / Real.sqrt 2)^2)^23
  _ = (((1 + Complex.I) / Real.sqrt 2)^2)^23 := by ring
  --利用h化简
  _ = (Complex.I)^23 := by rw[h]
  -- 将^23拆分为^(2*11+1)的形式
  -- 利用Complex.I^2 = -1化简
  _ = (Complex.I^2)^11 * (Complex.I) := by ring
  _ = -Complex.I :=  by rw[Complex.I_sq];ring