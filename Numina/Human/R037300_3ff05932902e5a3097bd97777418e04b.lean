import Mathlib

/- # Problem 10.2

Prove that if the numbers $x, y, z$ are solutions to the system for some values of $p$ and $q$:

$y=x^{2}+p x+q, z=y^{2}+p y+q, x=z^{2}+p z+q$,

then the inequality $x^{2} y+y^{2} z+z^{2} x \geq x^{2} z+y^{2} x+z^{2} y$ holds.

Points: 7 -/
theorem inequalities_120961 (p q : ℝ) (x y z : ℝ)
    (h₀ : y = x^2 + p * x + q)
    (h₁ : z = y^2 + p * y + q)
    (h₂ : x = z^2 + p * z + q) :
    x^2 * y + y^2 * z + z^2 * x ≥ x^2 * z + y^2 * x + z^2 * y := by
  -- Using nlinarith tactic with several non-negative expressions to prove the inequality
  -- We use:
  -- 1. The squares of differences between variables are non-negative
  -- 2. The squares of sums of variables with p are non-negative
  -- 3. The original system of equations
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x + y + p), sq_nonneg (y + z + p), sq_nonneg (z + x + p),
    h₀, h₁, h₂]
