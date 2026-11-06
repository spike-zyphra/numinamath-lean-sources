import Mathlib

/- The interior angles of a quadrilateral form an arithmetic sequence. If the measure of the largest angle is $129^{\circ}$, what is the measure of the second largest angle, in degrees? -/
theorem algebra_19476 (d : ℝ) (h : 0 < d ∧ 129 - 3 * d > 0) (H : 129 + (129 - d) + (129 - 2 * d) + (129 - 3 * d) = 360) :
    (129 - d) = 103 := by linarith
