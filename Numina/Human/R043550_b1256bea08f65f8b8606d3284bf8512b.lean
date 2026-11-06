import Mathlib

/- 271. Prove the inequality:


$$

a^{4}+2 a^{3} b+2 a b^{3}+b^{4} \geqslant 6 a^{2} b^{2}

$$


where $a$ and $b$ have the same sign. -/
theorem inequalities_276900 (a b : ℝ) (h₀ : a * b ≥ 0) :
    a^4 + 2 * a^3 * b + 2 * a * b^3 + b^4 ≥ 6 * a^2 * b^2 := by
  -- take all terms to greater side
  suffices 0 ≤ a^4 + 2 * a^3 * b + 2 * a * b^3 + b^4 - 6 * a^2 * b^2 by linarith
  -- write it as (a-b)^2 * (a^2 + b^2 + 4*a*b)
  convert_to 0 ≤ (a-b)^2 * (a^2 + b^2 + 4*a*b)
  . ring
  -- now just use the hypothesis
  rw [mul_assoc]
  positivity