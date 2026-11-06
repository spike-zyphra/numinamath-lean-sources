import Mathlib

/- Evaluate $\lfloor6.7\rfloor+\lfloor-6.7\rfloor$. -/
theorem algebra_19188: ⌊(6.7:ℝ)⌋ + ⌊(-6.7:ℝ)⌋ = -1 := by
  -- 6<6.7<7, -7<-6.7<-6, so floor6.7 is 6, and floor-6.7 is -7.
  -- 6+-7=-1.
  norm_num