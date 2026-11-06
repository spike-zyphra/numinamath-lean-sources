import Mathlib

/- If $(w+13)^2=(3w+7)(2w+4)$, find $w^2$. Express your answer as a decimal. -/
theorem algebra_11307 {w : ℝ} (h : (w + 13)^2 = (3 * w + 7) * (2 * w + 4)) :
    w^2 = 28.2 := by
  norm_num
  nlinarith