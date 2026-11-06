import Mathlib

open Real

theorem algebra_178669 (α : ℝ) (hα : cos (α / 2) ≠ 0) :
    cos ((5 * π / 2 - α)) * sin ((π / 2) + (α / 2)) /
    ((2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2) =
    2 * tan (α / 2) := by
  rw [add_comm, sin_add_pi_div_two]
  rw [show 5 * π / 2 - α = π / 2 - α + 2 * π by ring, cos_add_two_pi]
  rw [cos_pi_div_two_sub, ← div_sub_div_same, sin_pi_div_two_sub]
  rw [cos_sq, show 2 * ((π - α) / 4) = π / 2 - α / 2 by ring]
  rw [cos_pi_div_two_sub, show 3 * π / 2 - α = (π / 2 - α) + π by ring]
  rw [cos_add_pi, ← sub_eq_add_neg, cos_pi_div_two_sub]
  have : sin α = 2 * cos (α / 2) * sin (α / 2) := by
    nth_rw 1 [show α = 2 * (α / 2) by ring]
    rw [sin_two_mul]; ring
  nth_rw 2 [this]; rw [← mul_one_sub, mul_assoc, div_add_div_same]
  rw [mul_div]; nth_rw 4 [mul_comm]; rw [← sq_sub_sq]
  rw [one_pow, ← cos_sq', tan_eq_sin_div_cos, this]
  field_simp; ring