import Mathlib

theorem algebra_2907 {x : ℝ} (hx : x^2+2*x=3) : x^3+4*x^2+x+2=8 := by
  have h1 : x^2 = 3 - 2 * x := by
    linarith
  have h2 : x^3 = 7 * x - 6 := by
    calc
      x^3 = x * (x^2) := by ring
      _ = x * (3 - 2 * x) := by rw [h1]
      _ = 3 * x - 2 * (x^2) := by ring
      _ = 3 * x - 2 * (3 - 2 * x) := by rw [h1]
      _ = 7 * x - 6 := by ring
  rw [h2]
  -- Now compute $X^3 + 4*x^2+x+2$ using $x^2=3 - 2*x$
  have h3 : 4 * (x^2) = 4 * (3 - 2 * x) := by
    rw [h1]
  rw [h3]
  -- Now the expression has substitutions, solved as linear expression
  linarith