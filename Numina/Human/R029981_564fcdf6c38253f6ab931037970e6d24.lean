import Mathlib

/- A bicycle is traveling at 20 feet per minute. What is the bicycle's speed expressed in inches per second? -/
theorem algebra_21236 (v : ℝ) (h : v = 20) :
    v * 12 / 60 = 4 := by
    -- substitute v = 20 into the equation
    rw [h]
    -- trivial arithmetic
    linarith