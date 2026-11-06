import Mathlib

theorem algebra_323935 {a b : ℝ} (ha : a^2 + 1 = 3 * a) (hb : b^2 + 1 = 3 * b)
    (hne : a ≠ b) : 1 / a^2 + 1 / b^2 = 7 := by
  have ha2 : a^2 = 3 * a - 1 := by
    linarith
  have hb2 : b^2 = 3 * b - 1 := by
    linarith
  have h1 : a ≠ 0 := by
    intro h
    rw [h] at ha
    norm_num at ha
    all_goals linarith
  have h2 : b ≠ 0 := by
    intro h
    rw [h] at hb
    norm_num at hb
    all_goals linarith
  have h3 : a + b = 3 := by
    have eq_a : a^2 - 3 * a + 1 = 0 := by linarith [ha]
    have eq_b : b^2 - 3 * b + 1 = 0 := by linarith [hb]
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have eq : a^2 - 3 * a + 1 - (b^2 - 3 * b + 1) = 0 := by
      linarith [eq_a, eq_b]
    have : (a - b) * (a + b - 3) = 0 := by
      ring_nf at eq ⊢
      linarith
    cases' (mul_eq_zero.mp this) with h h'
    · -- a - b = 0, which is a ≠ b given
      exfalso
      exact hne (by linarith)
    · -- a + b - 3 = 0, which is the goal
      linarith
  have h4 : a * b = 1 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne), sq_pos_of_ne_zero (show b - a ≠ 0 by intro h; apply hne; linarith), sq_pos_of_ne_zero (show a ≠ 0 by intro h; apply h1; assumption), sq_pos_of_ne_zero (show b ≠ 0 by intro h; apply h2; assumption)]
  have eq1 : 1 / a^2 + 1 / b^2 = (b^2 + a^2) / (a^2 * b^2) := by
    field_simp [pow_two, h1, h2]
    <;> ring
  rw [eq1]
  have h5 : a^2 + b^2 = 7 := by
    nlinarith [h3, h4, sq_nonneg (a - b)]
  have h6 : a^2 * b^2 = 1 := by
    have h7 : a * b = 1 := h4
    have h8 : a^2 * b^2 = (a * b)^2 := by
      ring
    rw [h8]
    rw [h7]
    all_goals norm_num
  have h7 : b^2 + a^2 = 7 := by
    linarith [h5]
  rw [show b^2 + a^2 = 7 by linarith [h5]]
  rw [show a^2 * b^2 = 1 by linarith [h6]]
  all_goals norm_num
  <;> nlinarith