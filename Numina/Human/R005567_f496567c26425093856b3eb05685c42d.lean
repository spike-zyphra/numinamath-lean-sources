import Mathlib
/- Let $x$ be a real number such that $2^{x}=3$. Determine the value of $4^{3 x+2}$. -/
theorem algebra_608905 (x : ℝ) (h : (2 : ℝ) ^ x = 3) : (4 : ℝ) ^ (3 * x + 2) = 11664:= by
  -- Rewrite 4 as 2^2
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by ring]
  -- Use power rule: (a^b)^c = a^(b*c)
  rw [Eq.symm (Real.rpow_mul (by linarith) 2 (3 * x + 2))]
  -- Simplify the exponent: 2(3x + 2) = 6x + 4
  rw [show 2 * (3 * x + 2) = x * 6 + 4 by ring]
  -- Use power rule: a^(b+c) = a^b * a^c
  rw [Real.rpow_add (by linarith) (x * 6) 4]
  -- Use power rule: a^(b*c) = (a^b)^c
  rw [Real.rpow_mul (by linarith) x 6]
  -- Use the hypothesis h: 2^x = 3
  rw [h]
  -- Simplify the resulting expression
  ring
