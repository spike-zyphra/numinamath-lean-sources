import Mathlib

/-Given functions $f\left(x\right)=x^{2}$ and $g\left(x\right)=x+2$, find $f\left(g\left(3\right)\right)=\_\_\_\_\_\_$.-/
theorem algebra_9227 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2) (hg : g = fun x => x + 2) :
    f (g 3) = 25 := by
  -- Solve for $g(3)$.
  have : g 3 = 5 := by rw [hg]; norm_num
  -- Plug in $g(3)$ to get the desired result.
  rw [this, hf]; norm_num