import Mathlib
/-The roots of the equation $x^{2}=2x$ are ____.$-/
theorem algebra_9358 (x : ℝ) : x^2 = 2 * x ↔ x = 0 ∨ x = 2 := by
  constructor
  · intro h
    -- 1. Start with the given equation: $$x^{2}=2x$$
    rw [← sub_eq_zero] at h
    -- 2. Move all terms to one side to set the equation to zero: $$x^{2}-2x=0$$
    have : x * (x - 2) = 0 := by simp only [← h, mul_sub, pow_two, mul_comm]
    -- 3. Factor the equation: $$x(x-2)=0$$
    have := eq_zero_or_eq_zero_of_mul_eq_zero this
    rwa [sub_eq_zero] at this
    -- 4. Set each factor equal to zero to solve for $x$:
    -- · For the first factor: $x=0$
    -- · For the second factor: $x-2=0$, which simplifies to $x=2$
  · rintro (rfl | rfl) <;> norm_num
    -- Check that $0^{2}=2\cdot 0$ and $2^{2}=2\cdot 2$ to verify that both $x=0$ and $x=2$ are solutions to the equation.
    -- Therefore, the roots of the equation are $x_{1}=0$ and $x_{2}=2$. 
