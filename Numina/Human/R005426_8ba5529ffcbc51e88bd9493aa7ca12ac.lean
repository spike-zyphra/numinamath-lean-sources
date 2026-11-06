import Mathlib
/- The function $f$ satisfies

$$
f(x)+f(2 x+y)+5 x y=f(3 x-y)+2 x^{2}+1
$$

for all real numbers $x, y$. Determine the value of $f(10)$. -/
theorem algebra_608255 (f : ℝ → ℝ) (hf : ∀ x y : ℝ, f x + f (2 * x + y) + 5 * x * y = f (3 * x - y) + 2 * x ^ 2 + 1) : f 10 = -49:= by
  -- Substitute x = 10 and y = 5 into the equation
  specialize hf 10 5
  -- Simplify the equation
  ring_nf at hf
  -- Solve for f(10)
  linarith
