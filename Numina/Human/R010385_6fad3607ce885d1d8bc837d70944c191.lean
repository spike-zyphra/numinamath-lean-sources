import Mathlib
/-Given that $i$ is the imaginary unit, determine the real and imaginary parts of the complex number $i(3-4i)$.-/
theorem algebra_9341 : (Complex.I * (3 - 4 * Complex.I)).re = 4 ∧ (Complex.I * (3 - 4 * Complex.I)).im = 3 := by 
constructor
-- prove by definition
simp
simp
