import Mathlib


/-
The solution to the equation $x^{2}=4x$ is ___ .
-/

theorem algebra_9199 (x : ℝ) :
    x ^ 2 = 4 * x ↔ x = 0 ∨ x = 4 := by

  constructor

  . intro h

    -- To solve the equation $x^{2}=4x$, we first bring all terms to one side to set the equation to zero:
    apply sub_eq_zero_of_eq at h

    -- Next, we factor the left side of the equation, Factor out $x$: $x(x-4)=0$.
    rw [pow_two, ← sub_mul, mul_comm] at h

    -- Now, we solve for $x$ by setting each factor equal to zero:
    rcases mul_eq_zero.mp h with h1 | h2

    -- Set the first factor equal to zero: $x=0$.
    . simp [h1]

    -- Set the second factor equal to zero: $x-4=0$, which simplifies to $x=4$.
    . simp [eq_of_sub_eq_zero h2]

  -- verify that 0 and 4 are solutions
  . intro h
    rcases h with h | h
    <;> norm_num [h]
