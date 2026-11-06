import Mathlib

/-Suppose $z$ is a complex number such that $z^2 = 156 + 65i.$  Find $|z|.$-/
theorem algebra_21504 {z : ℂ} (hz : z^2 = 156 + 65 * .I) : Complex.abs z = 13 := by
  -- do calculation
  calc
    Complex.abs z = √(Complex.abs (z ^ 2)) := by rw [Complex.abs_pow, Real.sqrt_sq]; positivity
    _ = √(Complex.abs (156 + 65 * .I)) := by rw [hz]
    _ = √(√(156 ^ 2 + 65 ^ 2)) := by rw [<-Complex.abs_add_mul_I]; norm_cast
    _ = √(√(169 ^ 2)) := by norm_num
    _ = √(169) := by rw [Real.sqrt_sq]; positivity
    _ = √(13 ^ 2) := by norm_num
    _ = 13 := by rw [Real.sqrt_sq]; positivity