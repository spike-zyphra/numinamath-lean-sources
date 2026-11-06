import Mathlib

theorem algebra_147119 (z : ℂ) (hz : Complex.abs z = 3) :
    Complex.abs (25 / z) ^ 2 = (25 / 3) ^ 2 := by
  have hz' : z ≠ 0 := by
    by_contra h
    have h_abs : Complex.abs z = 0 := by
      simp [h]
    rw [h_abs] at hz
    all_goals linarith
  have h_abs : Complex.abs (25 / z) = 25 / Complex.abs z := by
    field_simp [Complex.abs, Complex.normSq, hz']
    all_goals norm_num
  rw [h_abs, hz]
  all_goals norm_num