import Mathlib

/- Half the value of $3x-9$ is $x+37$. What is the value of $x$?-/
theorem algebra_20217 (x : ℝ) (h : (3 * x - 9) / 2 = x + 37) : x = 83 := by
  --We translate the problem to the equation $\frac{1}{2}(3x-9) = x+37$.
  --Multiplying both sides by 2 gives $3x-9 = 2x+74$.
  --Subtracting $2x$ from both sides yield $x-9 = 74$.
  --Adding $9$ to both sides yields $ x = \boxed{83}$.
  linarith
