import Mathlib
open Polynomial
/- Let $P$ be a polynomial such that $P(x)=P(0)+P(1) x+P(2) x^{2}$ and $P(-1)=1$. Compute $P(3)$. -/
theorem algebra_608998 (P : ℝ[X]) (hP : ∀ x : ℝ, P.eval x = P.eval 0 + P.eval 1 * x + P.eval 2 * x ^ 2) (hP1 : P.eval (-1) = 1) : P.eval 3 = 5:= by
  -- Apply the polynomial formula to x = -1, 1, and 2
  have h1:= hP (-1)
  have h2:= hP 1
  have h3:= hP 2
  -- Simplify the equations
  simp at h1 h2 h3
  -- From the equations, deduce that P(0) = -1
  replace h1 : P.eval 0 = -1:= by linarith
  -- Deduce that P(1) = -1
  replace h2 : P.eval 1 = -1:= by linarith
  -- Deduce that P(2) = 1
  replace h3 : P.eval 2 = 1:= by linarith
  -- Substitute the values back into the polynomial formula
  rw [h1, h2, h3] at hP
  -- Apply the formula to x = 3
  specialize hP 3
  rw [hP]
  -- Solve the final equation
  linarith
