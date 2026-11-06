import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

/- Find all real numbers $x$ so that the product $(x + i)((x + 1) + i)((x + 2) + i)$ is pure imaginary.  Enter all the solutions, separated by commas. -/
theorem algebra_16903 (x : ℝ) :
    ((x + Complex.I) * (x + 1 + Complex.I) * (x + 2 + Complex.I)).re = 0 ↔
    x = -3 ∨ x = -1 ∨ x = 1 := by
  -- first, we calculate (x+i)(x+1+i)(x+2+i)
  have heq: (x + Complex.I) * (x + 1 + Complex.I) * (x + 2 + Complex.I) =
    (x^3+3*x^2-x-3) + (3*x^2+6*x+1)*Complex.I :=
    calc
      (x + Complex.I) * (x + 1 + Complex.I) * (x + 2 + Complex.I) =
      (x*(x+1) + (x+(x+1))*Complex.I + -1) * (x+2+Complex.I) := by
        nth_rw 1 [← I_mul_I]; ring
      _ = ((x*(x+1)-1) + (x+(x+1))*Complex.I) * ((x+2) + Complex.I) := by ring
      _ = (x*(x+1)-1)*(x+2) + ((x*(x+1)-1) + (x+(x+1))*(x+2)) * Complex.I + (x+(x+1)) * (Complex.I*Complex.I) := by ring
      -- i^2=-1
      _ = ((x^2+x-1)*(x+2)-(2*x+1)) + ((x^2+x-1)+(2*x+1)*(x+2))*Complex.I := by
        rw [I_mul_I]; ring
      -- simplify
      _ = (x^3+3*x^2-x-3) + (3*x^2+6*x+1)*Complex.I := by ring
  -- x is real, obviously, first part is the real part.
  have heq1: ((x^3+3*x^2-x-3) + (3*x^2+6*x+1)*Complex.I).re =
    (x^3+3*x^2-x-3) := by
    simp [pow_three, pow_two]
  -- to solve "real part = 0", we do some factorization.
  have heq2: x^3+3*x^2-x-3 = (x+3)*(x+1)*(x-1) := by ring
  rw [heq, heq1, heq2]
  constructor <;> intro h
  --given (x+3)(x+1)(x-1)=0, obviously, x = -3,-1,1
  · have h1 := mul_eq_zero.mp h
    rcases h1 with h1l | h1r
    · have h2 := mul_eq_zero.mp h1l
      rcases h2 with h2l | h2r
      · left
        rw [← add_zero (-3), ← h2l]; ring
      · right
        left
        rw [← add_zero (-1), ← h2r]; ring
    right
    right
    rw [← add_zero 1, ← h1r]; ring
  -- given x=-3,-1,1, we have (x+3)(x+1)(x-1)=0
  rcases h with h1 | h1 | h1 <;> rw [h1] <;> simp