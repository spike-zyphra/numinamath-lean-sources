import Mathlib

theorem algebra_180644 {z1 z2 : ℂ} (hz1 : z1 = -2 + 5 * .I) (hz2 : z2 = 3 - 4 * .I) :
    z1 + z2 = 1 + .I ∧ z2 - z1 = 5 - 9 * .I ∧ z1 * z2 = 14 + 23 * .I ∧
    z1 / z2 = -26 / 25 + 7 / 25 * .I := by
  constructor
  · -- Proof of addition
    rw [hz1, hz2]
    ring_nf
  constructor
  · -- Proof of subtraction
    rw [hz1, hz2]
    ring_nf
  constructor
  · -- Proof of multiplication
    rw [hz1, hz2]
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    all_goals norm_num
  · -- Proof of division
    rw [hz1, hz2]
    field_simp [Complex.ext_iff, Complex.I_mul_I]
    all_goals norm_num