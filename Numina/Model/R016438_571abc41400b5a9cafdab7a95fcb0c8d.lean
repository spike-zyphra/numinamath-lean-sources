import Mathlib

theorem algebra_305716 {a b x y : ℝ} (ha : a^2 - a - 1 = 0) (hb : b^2 - b - 1 = 0)
    (hroots : a ≠ b) (h1 : x / a + y / b = 1 + x) (h2 : x / b + y / a = 1 + y) :
    x = -1 / 2 ∧ y = -1 / 2 := by

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [show a = 0 by linarith] at ha
    nlinarith

  have hb1 : b ≠ 0 := by
    by_contra h
    rw [show b = 0 by linarith] at hb
    nlinarith

  have eq1 : x * b + y * a = (1 + x) * (a * b) := by
    have h1' : x / a + y / b = 1 + x := h1
    field_simp [ha1, hb1] at h1' ⊢
    linarith

  have eq2 : x * a + y * b = (1 + y) * (a * b) := by
    have h2' : x / b + y / a = 1 + y := h2
    field_simp [ha1, hb1] at h2' ⊢
    linarith

  have h3 : a + b = 1 := by
    have eq1 : a^2 = a + 1 := by linarith
    have eq2 : b^2 = b + 1 := by linarith
    have eq3 : (a - b) * (a + b - 1) = 0 := by
      nlinarith

    cases (mul_eq_zero.mp eq3) with
    | inl h4 =>
      exfalso
      apply hroots
      linarith
    | inr h5 =>
      linarith

  have h4 : a * b = -1 := by
    have eq1 : a^2 = a + 1 := by linarith
    have eq2 : b^2 = b + 1 := by linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply hroots
      linarith
    ), h3]

  have eq3 : x * b + y * a + x + 1 = 0 := by
    rw [show a * b = -1 by linarith [h4]] at eq1
    nlinarith

  have eq4 : x * a + y * b + y + 1 = 0 := by
    rw [show a * b = -1 by linarith [h4]] at eq2
    nlinarith

  have eq5 : x + y = -1 := by
    have eq6 : x * (1 - a) + x + y * a + 1 = 0 := by
      rw [show b = 1 - a by linarith [h3]] at eq3
      nlinarith
    have eq7 : x * a + 2 * y - a * y + 1 = 0 := by
      rw [show b = 1 - a by linarith [h3]] at eq4
      nlinarith
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply hroots
      linarith
    ), h3, eq6, eq7]

  have eq9 : x = -1 / 2 := by
    have eq10 : x * (1 - a) + x + (-1 - x) * a + 1 = 0 := by
      have eq11 : y = -1 - x := by
        linarith [eq5]
      rw [eq11] at eq3
      nlinarith
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply hroots
      linarith
    ), h3, sq_nonneg (a - 1)]

  have eq10 : y = -1 / 2 := by
    linarith [eq9, eq5]

  constructor
  · linarith [eq9]
  · linarith [eq10]