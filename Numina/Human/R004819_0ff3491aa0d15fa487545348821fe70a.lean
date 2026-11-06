import Mathlib

theorem algebra_571696 (x y z : ℝ) (xne0 : x ≠ 0) (yne0 : y ≠ 0) (zne0 : z ≠ 0)
    (h1 : 9 * x * (15 * z) = (12 * y) ^ 2 )
    (h2 : 1 / x + 1 / z = 2 / y) :
    x / z + z / x = 34 / 15 := by
  field_simp at *; have : z + x ≠ 0 := by
    intro h; simp [h] at h2; rcases h2
    all_goals contradiction
  rw [mul_comm, ← eq_div_iff] at h2
  rw [h2] at h1; field_simp at h1
  rw [← sub_eq_zero] at h1; ring_nf at h1
  rw [sub_add_eq_add_sub, sub_eq_zero] at h1
  rw [show x*z^3*135+x^3*z*135 = (x*x+z*z)*15*(9*x*z) by ring] at h1
  rw [show x ^ 2 * z ^ 2 * 306 = 34*(z*x)*(9*x*z) by ring] at h1
  apply mul_right_cancel₀ at h1; exact h1
  all_goals positivity