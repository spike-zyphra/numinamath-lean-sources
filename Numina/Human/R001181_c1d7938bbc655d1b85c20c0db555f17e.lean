import Mathlib

/- If $\displaystyle{f(x)=x^{(x+1)}(x+2)^{(x+3)}}$, then find the value of $f(0)+f(-1)+f(-2)+f(-3)$. -/
theorem algebra_20907 {f : ℝ → ℝ} (hf : f = fun x => x^(x + 1) * (x + 2)^(x + 3)) :
    f 0 + f (-1) + f (-2) + f (-3) = 10 / 9 := by 
  rw [hf]
  norm_num