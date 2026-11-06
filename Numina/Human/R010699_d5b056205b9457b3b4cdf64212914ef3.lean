import Mathlib

/- The complement of an angle is $5^{\circ}$ more than four times the angle. What is the number of degrees in the measure of the angle? -/
theorem algebra_17156 (θ : ℝ) (hθ : 90 - θ = 4 * θ + 5) :
    θ = 17 := by
  ring_nf at hθ
  linarith
