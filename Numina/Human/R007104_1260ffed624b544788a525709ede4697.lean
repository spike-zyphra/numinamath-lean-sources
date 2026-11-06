import Mathlib

/-The radius of a circle is $x+6$ and its diameter is $3x+5$. What is the circumference of the circle, in terms of $\pi$? (Do not include the variable $x$ in your answer.)-/
theorem algebra_19787 (x : ℝ) (hx : x ≠ -5 / 3) (h : (x + 6) * 2 = 3 * x + 5) :
    (x + 6) * 2 * Real.pi = 26 * Real.pi := by
  -- Since the diameter of a circle is twice its radius, we know that $3x+5=2(x+6)$, or $3x+5=2x+12$. Subtracting $2x+5$ from both sides gives $x=7$. The circumference of a circle is $\pi$ times its diameter, so the circumference is $(3x+5)\pi=(3\cdot7+5)\pi=(21+5)\pi=\boxed{26\pi}$.
  have : x = 7 := by linarith
  rw [this]
  norm_num
