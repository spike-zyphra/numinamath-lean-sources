import Mathlib
/- Let $X$ be a positive integer.
Theorem: The fraction $\frac{2X+1}{2X+3}$ is greater than the fraction $\frac{3X+1}{3X+4}$. -/
theorem algebra_639058 (X : ℤ) (hX : X > 0) : (2 * X + 1) / (2 * (↑X : ℝ) + 3) > (3 * X + 1) / (3 * X + 4):= by
  -- Prove that the product of denominators (2X+3)(3X+4) is positive
  have g : (2 * X + 3) * (3 * X + 4) > 0:= by positivity
  -- Convert the hypothesis to real numbers
  rify at g
  -- Use the fact that if ab > 0, then x/y > z/w iff x*w > z*y (by multiplying both sides by ab)
  suffices (2 * X + 1) / (2 * (↑X : ℝ) + 3) * ((2 * X + 3) * (3 * X + 4)) > (3 * X + 1) / (3 * X + 4) * ((2 * X + 3) * (3 * X + 4)) by exact (mul_lt_mul_iff_of_pos_right g).mp this
  -- Simplify the left side: (2X+1)/(2X+3) * (2X+3)(3X+4) = (2X+1)(3X+4)
  rw [show (2 * X + 1) / (2 * (↑X : ℝ) + 3) * ((2 * X + 3) * (3 * X + 4)) = (2 * X + 1) * (3 * X + 4) by field_simp ; ring]
  -- Simplify the right side: (3X+1)/(3X+4) * (2X+3)(3X+4) = (3X+1)(2X+3)
  rw [show (3 * (X : ℝ) + 1) / (3 * X + 4) * ((2 * X + 3) * (3 * X + 4)) = (3 * X + 1) * (2 * X + 3) by field_simp ; ring]
  -- Use linear arithmetic to prove (2X+1)(3X+4) > (3X+1)(2X+3)
  linarith
