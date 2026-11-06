import Mathlib

/- Find $\left \lceil \frac{\left \lfloor 52/3 \right. \rfloor}{5/23} \right \rceil$. -/
theorem algebra_21349 : ⌈(⌊(52 / 3 : ℝ)⌋ / (5 / 23 :ℝ))⌉ = 79 := by
  -- notice that 51/3=17 and 54/3 = 18, so floor of 52/3 is 17
  have h1: ⌊(52/3:ℝ)⌋ = 17 := by norm_num
  -- 17/(5/23) = 17x23/5 = 391/5
  have h2: (17:ℝ)/(5/23) = 391/5 := by norm_num
  rw [h1]; simp; rw [h2]
  -- notice that 390/5 = 78 and 395/5= 79, so ceil of 391/5 is 79
  apply Int.ceil_eq_on_Ioc 79 (391 / 5) 
  simp; norm_num