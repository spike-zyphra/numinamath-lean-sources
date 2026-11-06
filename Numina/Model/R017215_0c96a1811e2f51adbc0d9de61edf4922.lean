import Mathlib

open Real

theorem inequalities_1401 {a b : ℝ} (h : abs (a^3 - b^3) = -abs (a * abs (a^3) + b^3)) :
    a ≤ b := by

  have h1 : abs (a ^ 3 - b ^ 3) ≥ 0 := by apply abs_nonneg
  have h2 : abs (a * abs (a ^ 3) + b ^ 3) ≥ 0 := by apply abs_nonneg

  have h3 : - abs (a * abs (a ^ 3) + b ^ 3) ≤ 0 := by linarith [abs_nonneg (a * abs (a ^ 3) + b ^ 3)]

  have h4 : abs (a ^ 3 - b ^ 3) + abs (a * abs (a ^ 3) + b ^ 3) = 0 := by
    linarith [h, h1, h2, h3]

  have h5 : abs (a ^ 3 - b ^ 3) = 0 := by
    linarith [abs_nonneg (a ^ 3 - b ^ 3), abs_nonneg (a * abs (a ^ 3) + b ^ 3), h4]

  have h6 : abs (a * abs (a ^ 3) + b ^ 3) = 0 := by
    linarith [abs_nonneg (a ^ 3 - b ^ 3), abs_nonneg (a * abs (a ^ 3) + b ^ 3), h4]

  have h7 : a ^ 3 - b ^ 3 = 0 := by
    rwa [abs_eq_zero] at h5

  have h8 : a^3 = b^3 := by linarith [h7]

  have h9 : a = b := by
    have h10 : a ^ 3 - b ^ 3 = 0 := by linarith [h8]
    have h11 : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
      ring_nf at h10 ⊢
      linarith

    cases' (mul_eq_zero.1 h11) with h12 h13
    · -- Case a - b = 0
      linarith
    · -- Case a^2 + a * b + b^2 = 0
      have h14 : a ^ 2 + a * b + b ^ 2 = 0 := by nlinarith
      have h15 : (2 * a + b) ^ 2 + 3 * b ^ 2 = 0 := by nlinarith [h14]
      have h16 : (2 * a + b) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg (b), h15]
      have h17 : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg (b), h15]
      have hb0 : b = 0 := by nlinarith [pow_eq_zero h17]
      have ha0 : a = 0 := by nlinarith [pow_eq_zero h16, hb0]
      linarith [hb0, ha0]

  linarith [h9]