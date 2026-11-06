import Mathlib
/- The solution to the quadratic equation J7^{2}-2x=0$ is ____.-/
theorem algebra_9030 (x : ℝ) (hx : x ^ 2 - 2 * x = 0) : x = 0 ∨ x = 2 := by
  have eq : x * (x - 2) = 0 :=
  calc
      _ = x ^ 2 - 2 * x := by ring
      _ = 0 := by rw [hx]
  --Factor out the common term $x$: \[x(x-2)=0\]
  have := (mul_eq_zero).1 eq
  --Set each factor equal to zero to find the solutions:
  --\[x=0 \quad \text{and} \quad x-2=0\]
  rcases this with h1 | h2
  left ; exact h1
  right ; exact eq_of_sub_eq_zero h2
  --Solve each equation for $x$:
  --\[x=0 \quad \text{and} \quad x=2\]
