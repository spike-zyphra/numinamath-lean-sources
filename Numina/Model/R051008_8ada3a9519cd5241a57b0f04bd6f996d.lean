import Mathlib

theorem calculus_14786 (z : ℂ) (hz : z = 2 * .I) :
    (z - (-1 + 4 * .I)) * (-2) + (-1 + 4 * .I) = -3 + 8 * .I := by
  rw [hz]
  ring_nf
  <;> simp [Complex.I_mul_I, Complex.ext_iff]
  <;> norm_num
  <;> try ring