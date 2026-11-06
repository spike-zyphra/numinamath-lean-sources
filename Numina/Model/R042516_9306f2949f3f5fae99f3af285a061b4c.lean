import Mathlib

theorem algebra_605971 {a b c : ℝ} (hab : a ≠ b) (hc : 0 < c)
    (h1 : a ^ 4 - 2019 * a = c) (h2 : b ^ 4 - 2019 * b = c) :
    -√c < a * b ∧ a * b < 0 := by
  have h3 : (a - b) * ((a + b) * (a ^ 2 + b ^ 2) - 2019) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by 
      intro h
      apply hab
      linarith
    ), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b)]
  have gne : a - b ≠ 0 := by 
    intro h
    apply hab
    linarith
  have h4 : (a + b) * (a ^ 2 + b ^ 2) - 2019 = 0 := by 
    apply (mul_right_inj' gne).mp 
    linarith 
  replace h4 : (a + b) * (a ^ 2 + b ^ 2) = 2019 := by linarith
  have h5 : 2 * c = a ^ 4 + b ^ 4 - 2019 * (a + b) := by
    nlinarith
  rw [←h4] at h5
  rw [show a ^ 4 + b ^ 4 - (a + b) * (a ^ 2 + b ^ 2) * (a + b) = -2 * a * b * (a ^ 2 + a * b + b ^ 2) by ring_nf] at h5
  have h5' : -2 * a * b * (a ^ 2 + a * b + b ^ 2) > 0 := by 
    nlinarith 
  have h7 : a ^ 2 + a * b + b ^ 2 > 0 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by 
      intro h
      apply hab
      linarith
    ), sq_nonneg (a + b), sq_nonneg (a), sq_nonneg (b)]
  have h8 : -2 * a * b > 0 := by 
    have h9 : -2 * a * b * (a ^ 2 + a * b + b ^ 2) > 0 := by linarith 
    have h10 : a ^ 2 + a * b + b ^ 2 > 0 := h7 
    have h11 : -2 * a * b > 0 := by nlinarith 
    linarith 
  have h9 : a * b < 0 := by 
    nlinarith
  have h10 : -√c < a * b := by
    have h11 : (a * b) ^ 2 < c := by 
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by 
        intro h
        apply hab
        linarith
      ), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a * b)]
    have h14 : (√c) ^ 2 = c := by 
      rw [Real.sq_sqrt]
      linarith 
    have h41 : -√c < a * b := by
      nlinarith [Real.sqrt_pos.mpr hc, Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith)]
    linarith
  constructor
  · linarith 
  · linarith