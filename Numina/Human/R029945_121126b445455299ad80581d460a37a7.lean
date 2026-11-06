import Mathlib

/-For what real value of $b$ is the expression $\frac{1}{2}b^2 + 5b - 3$ minimized?-/
theorem algebra_12628 (f : ℝ → ℝ) (hf : f = fun b => (1/2)*b^2 + 5*b - 3) :
    IsLeast (Set.range f) (f (-5)) := by
    simp [IsLeast, lowerBounds]
    intro b
    -- substitute the expression for f
    rw [hf]
    ring_nf
    
    -- the square of any real number is never negative
    have ineq : (b + 5) ^ 2 ≥ 0 := by positivity
    -- calculate the goal
    calc
      -3 + b * 5 + b ^ 2 * (1 / 2) = (1 / 2) * (b ^ 2 + 10 * b) + (-3) := by ring_nf
      _ = (1 / 2) * (b + 5) ^ 2 + (-3) -(25 / 2) := by ring_nf
      _ ≥ -31 / 2 := by linarith only [ineq]
