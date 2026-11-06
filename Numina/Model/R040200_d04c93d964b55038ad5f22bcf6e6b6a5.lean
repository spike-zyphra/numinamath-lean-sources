import Mathlib

theorem algebra_230199 {a b : ℝ} (ha : a ≠ -b^2) (hb : b ≠ -a^2) (h : a / (a + b^2) + b / (b + a^2) = 4 / 5) (hab : a * b = -1) : a^9 + b^9 = 1030 := by
  have eq1 : a * (b + a ^ 2) + b * (a + b ^ 2) = 4 / 5 * ( (a + b ^ 2) * (b + a ^ 2) ) := by
    have denom1 : a + b ^ 2 ≠ 0 := by
      intro h1
      apply ha
      nlinarith
    have denom2 : b + a ^ 2 ≠ 0 := by
      intro h1
      apply hb
      nlinarith
    field_simp [denom1, denom2] at h ⊢
    nlinarith
  have eq2 : a ^ 3 + b ^ 3 = 10 := by
    nlinarith [eq1, hab, sq_pos_of_ne_zero (show a + b ^ 2 ≠ 0 by
      intro h1
      apply ha
      nlinarith
    ), sq_pos_of_ne_zero (show b + a ^ 2 ≠ 0 by
      intro h1
      apply hb
      nlinarith
    ), sq_nonneg (a^3 + b^3), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b)]
  have h1 : a ^ 9 + b ^ 9 = (a^3 + b^3)^3 - 3 * (a^3 * b^3) * (a^3 + b^3) := by
    ring
  have h2 : a^3 * b^3 = (a * b)^3 := by
    ring
  have h3 : a^3 * b^3 = -1 := by
    rw [h2, hab]
    norm_num
  rw [h1]
  rw [eq2, h3]
  all_goals norm_num