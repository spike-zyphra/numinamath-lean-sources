import Mathlib

open scoped BigOperators

theorem algebra_5771 {x : ℚ} (hx : 0 < x) (h : x = 5 / (4 + 5 / (4 + x))) : x = 1 := by
  have h1 : x > 0 := hx
  have h2 : 4 + x ≠ 0 := by
    linarith
  have h3 : 4 + 5 / (4 + x) ≠ 0 := by
    by_contra h4
    have h5 : 4 + 5 / (4 + x) = (0 : ℚ) := by linarith
    have h6 : 5 / (4 + x) = (-4 : ℚ) := by linarith
    have h7 : 0 < (4 + x : ℚ) := by linarith
    have h8 : (5 / (4 + x) : ℚ) > 0 := by
      apply div_pos
      norm_num
      linarith
    linarith
  field_simp [h2] at h
  have h6 : (x - 1) * (x + 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- case where x - 1 = 0, so x = 1
    linarith
  · -- case where x + 5 = 0, so x = -5
    have h7 : x = (-5 : ℚ) := by linarith
    linarith -- contradiction