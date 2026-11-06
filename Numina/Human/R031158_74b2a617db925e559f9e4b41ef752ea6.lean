import Mathlib

open Real

theorem algebra_185416 (α : ℝ) (h : sin (2 * α) ≠ 0) :
    cos (4 * α) - sin (4 * α) * cot (2 * α) = cos (2 * α) - 2 * cos α ^ 2 := by
  rw [cot_eq_cos_div_sin,
      show 4 * α = 2 * (2 * α) by ring,
      cos_two_mul,
      sin_two_mul,
      cos_sq α]
  field_simp
  ring
