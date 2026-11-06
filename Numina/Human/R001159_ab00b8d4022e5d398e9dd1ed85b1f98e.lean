import Mathlib

/- Quadrilateral $ABCD$ is a parallelogram. If the measure of angle $A$ is 62 degrees and the measure of angle $ADB$ is 75 degrees, what is the measure of angle $ADC$, in degrees? -/
theorem algebra_20780 (A ADC ADB : ℝ) (h1 : A = 62) (h2 : ADB = 75) (h3 : A + ADC = 180) : ADC = 118 := by
  linarith