import Mathlib

theorem algebra_234539 (a b c : ℝ) (ha : a^3 - 2022 * a^2 + 1011 = 0) (hb : b^3 - 2022 * b^2 + 1011 = 0) (hc : c^3 - 2022 * c^2 + 1011 = 0) (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 / (a * b) + 1 / (b * c) + 1 / (a * c) = -2 := by

  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith

  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    nlinarith

  have h3 : c ≠ 0 := by
    by_contra h
    rw [h] at hc
    nlinarith

  have hab : a - b ≠ 0 := by
    intro h
    apply hne.left
    linarith

  have hac : a - c ≠ 0 := by
    intro h
    apply hne.right.left
    linarith

  have hbc : b - c ≠ 0 := by
    intro h
    apply hne.right.right
    linarith

  have h5 : a^2 + a * b + b^2 = 2022 * (a + b) := by
    apply (mul_left_inj' hab).mp
    nlinarith

  have h7 : a^2 + a * c + c^2 = 2022 * (a + c) := by
    have hac : a - c ≠ 0 := by
      intro h
      apply hne.right.left
      linarith
    apply (mul_left_inj' hac).mp
    nlinarith

  have h8 : b^2 + b * c + c^2 = 2022 * (b + c) := by
    have hbc : b - c ≠ 0 := by
      intro h
      apply hne.right.right
      linarith
    apply (mul_left_inj' hbc).mp
    nlinarith

  have h9 : (a^2 + a * b + b^2) - (a^2 + a * c + c^2) = 2022 * (b - c) := by
    nlinarith

  have h10 : (b^2 - c^2) + a * (b - c) = 2022 * (b - c) := by
    nlinarith

  have h12 : (b - c) * (b + c + a) = 2022 * (b - c) := by
    nlinarith

  have h13 : b - c ≠ 0 := by
    intro h
    apply hne.right.right
    linarith

  have h11 : a + b + c = 2022 := by
    have h14 : b - c ≠ 0 := h13
    apply (mul_left_inj' h14).mp
    nlinarith

  have h14 : a * b * c = -1011 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply hne.left
      linarith
    ), sq_pos_of_ne_zero (show a - c ≠ 0 by
      intro h
      apply hne.right.left
      linarith
    ), sq_pos_of_ne_zero (show b - c ≠ 0 by
      intro h
      apply hne.right.right
      linarith
    )]

  have h15 : 1 / (a * b) + 1 / (b * c) + 1 / (a * c) = (a + b + c) / (a * b * c) := by
    field_simp [h1, h2, h3]
    <;> ring

  rw [h15, h11, h14]
  norm_num