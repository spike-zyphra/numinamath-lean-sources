import Mathlib

/- Solve for $x>0$ in the following arithmetic sequence: $1^2, x^2, 3^2, \ldots$. -/
theorem algebra_10268 (x : ℝ) (hxpos : 0 < x) (harith : ∃ d, x ^ 2 = 1 ^ 2 + d ∧ 3 ^ 2 = x ^ 2 + d) :
    x = √5 := by
  -- The term $x^2$ is simply the average of $1^2 = 1$ and $3^2 = 9$, so $x^2 = (1 + 9)/2 = 5$.
  rcases harith with ⟨d, hx1, hx2⟩
  have hx : 2 * x ^ 2 = 3 ^ 2 + 1 ^ 2 := by linear_combination hx1 - hx2
  apply_fun (· / 2) at hx
  norm_num at hx
  -- Because $x > 0$, $x = \boxed{\sqrt{5}}$.
  replace hx : x ^ 2 = √5 ^ 2 := by rwa [Real.sq_sqrt (by norm_num)]
  rwa [sq_eq_sq hxpos.le (by positivity)] at hx
