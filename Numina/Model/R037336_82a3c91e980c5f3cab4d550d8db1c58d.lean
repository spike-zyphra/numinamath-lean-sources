import Mathlib

theorem algebra_354
    (a b : ℝ)
    (ha : a^2 - a - 1 = 0)
    (hb : b^2 - b - 1 = 0)
    (hab : a ≠ b) :
    3 * a^3 + 4 * b + 2 / a^2 = 11 := by

  have h1 : a + b = 1 := by
    have ha_eq : a^2 - a - 1 = 0 := ha
    have hb_eq : b^2 - b - 1 = 0 := hb
    have h4 : a^2 - b^2 = (a - b) := by
      nlinarith [ha_eq, hb_eq]
    have h5 : (a - b) * (a + b) = (a - b) := by
      nlinarith [ha_eq, hb_eq]
    have h6 : a - b ≠ 0 := by
      intro h
      apply hab
      linarith
    have h7 : (a + b) = 1 := by
      apply (mul_left_inj' h6).mp
      linarith
    assumption

  have h2 : a * b = -1 := by
    have h1_eq : a + b = 1 := h1
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply hab
      linarith
    )]

  have ha2 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith

  have ha0 : a^2 = a + 1 := by 
    linarith [ha]

  have ha1 : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [ha0]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [ha0]
      _ = 2 * a + 1 := by ring

  have hb1 : b = 1 - a := by
    linarith [h1]

  have hb2 : b^2 = b + 1 := by 
    nlinarith [hb]

  have h3a3 : 3 * a^3 = 6 * a + 3 := by 
    rw [ha1]
    ring

  have h4b : 4 * b = 4 - 4 * a := by
    rw [hb1]
    ring

  have h2a2 : 2 / a^2 = 2 * b^2 := by 
    field_simp [ha2]
    nlinarith [h1, h2]

  rw [h3a3, h4b, h2a2]
  rw [hb2]
  nlinarith [sq_pos_of_ne_zero (show a^2 ≠ 0 by
    intro h
    have : a = 0 := by nlinarith
    contradiction
  ), sq_nonneg (a - b)]