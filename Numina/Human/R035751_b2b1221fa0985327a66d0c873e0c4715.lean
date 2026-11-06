import Mathlib

/- Given the equation of motion of an object, $s=t^{2}+ \frac {3}{t}$, determine the velocity $v$ of the object at time $t=2$. -/
theorem algebra_9237 (s : ℝ → ℝ) (h₀ : s = fun t => t^2 + 3 / t) :
    deriv s 2 = 13 / 4 := by
  -- f'(t) = 2t - 3/t^2
  -- f'(2) = 4 - 3/4 = 13/4

  -- Just use the rules for differentiation
  rw [h₀, deriv_add, deriv_pow, deriv_div] <;> try simp
  . norm_num
  . apply DifferentiableAt.div <;> simp
