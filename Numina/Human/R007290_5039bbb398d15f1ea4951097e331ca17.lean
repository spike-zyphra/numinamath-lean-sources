import Mathlib

open Real

/- Let $r(\theta) = \frac{1}{1-\theta}$. What is $r(r(r(r(r(r(30))))))$ (where $r$ is applied $6$ times)? -/
theorem algebra_14207 {r : ℝ → ℝ} (hr : r = fun θ => 1 / (1 - θ)) :
    r (r (r (r (r (r 30))))) = 30 := by 
  rw [hr]; norm_num