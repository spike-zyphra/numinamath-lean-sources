import Mathlib

/- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem algebra_21208 {f : ℝ → ℝ} (hf : f = fun x => 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by 
  rw [hf]
  norm_num