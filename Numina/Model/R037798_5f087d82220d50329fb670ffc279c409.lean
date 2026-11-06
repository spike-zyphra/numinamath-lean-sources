import Mathlib

theorem inequalities_597704 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    a ^ 2 / (a + 1) + b ^ 2 / (b + 1) ≥ 1 / 3 := by

  have h1 : 0 < a * b := by
    nlinarith

  have hb_eq : b = 1 - a := by linarith

  rw [hb_eq]

  have h3 : a < 1 := by
    nlinarith

  have h4 : (a : ℝ) + 1 > 0 := by
    linarith

  have h5 : ((1 - a : ℝ)) + 1 > 0 := by
    nlinarith

  have h6 : a ^ 2 / (a + 1) + (1 - a) ^ 2 / ((1 - a) + 1) - (1 / 3) ≥ 0 := by 
    have h7 : a ^ 2 / (a + 1) + (1 - a) ^ 2 / ((1 - a) + 1) - (1 / 3) =
        (3 * a^2 * ((1 - a) + 1) + 3 * (1 - a)^2 * (a + 1) - (a + 1) * ((1 - a) + 1)) / (3 * (a + 1) * ((1 - a) + 1)) := by
      field_simp
      ring
    rw [h7]

    have h8 : 3 * a^2 * ((1 - a) + 1) + 3 * (1 - a)^2 * (a + 1) - (a + 1) * ((1 - a) + 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 2 / 3), sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) - 2 / 3), mul_pos ha (show 0 < (1 - a : ℝ) by nlinarith)]

    apply div_nonneg
    linarith
    positivity

  linarith