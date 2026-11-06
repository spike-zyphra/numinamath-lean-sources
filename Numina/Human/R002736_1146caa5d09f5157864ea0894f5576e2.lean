import Mathlib

theorem algebra_105835 {z1 z2 : ℂ} (hz1 : (z1 - 2) * (1 + .I) = 1 - .I)
    (hz2 : z2.im = 2) : ∃ r : ℝ, z1 * z2 = r ↔ z2 = 4 + 2 * .I := by

  have hz1_eq : z1 = 2 - Complex.I := by
    have : z1 - 2 = (1 - Complex.I) / (1 + Complex.I) := by
      rw [← hz1]
      field_simp [Complex.ext_iff, Complex.I_mul_I]
    have : z1 - 2 = -Complex.I := by
      rw [this]
      field_simp [Complex.ext_iff, Complex.I_mul_I]
    calc
      z1 = (z1 - 2) + 2 := by ring
      _ = -Complex.I + 2 := by rw [this]
      _ = 2 - Complex.I := by ring

  use (2 * z2.re + 2 + (4 - z2.re) * 0)
  rw [hz1_eq]
  simp [Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hz2]
  constructor
    <;> intro h
    <;> linarith
