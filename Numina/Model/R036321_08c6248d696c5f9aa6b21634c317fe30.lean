import Mathlib

theorem algebra_103161 {a b c : ℝ} (ha : a ≠ b) (hc : c > 0)
    (h : a^4 - 2019 * a = c) (h' : b^4 - 2019 * b = c) :
    -Real.sqrt c < a * b ∧ a * b < 0 := by
  have eq1 : a^4 - 2019 * a - (b^4 - 2019 * b) = 0 := by
    linarith [h, h']
  have eq2 : (a - b) * ((a + b) * (a^2 + b^2) - 2019) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h0
      apply ha
      linarith
    ), sq_nonneg (a^2 - b^2), sq_nonneg (a + b), sq_nonneg (a - b)]
  have eq3 : (a + b) * (a^2 + b^2) = 2019 := by
    apply (mul_left_inj' (show a - b ≠ 0 by
      intro h0
      apply ha
      linarith
    )).mp
    linarith [eq2]

  have eq4 : a * b < 0 := by
    nlinarith [sq_pos_of_pos (show 0 < c by linarith), sq_nonneg (a^2 - b^2), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h0
      apply ha
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_pos_of_pos (show 0 < c by linarith)]

  have h3 : (a * b)^2 < c := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h0
      apply ha
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_pos_of_pos (show 0 < c by linarith), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]

  have h4 : Real.sqrt c ^ 2 = c := by
    rw [Real.sq_sqrt]
    linarith

  have h5 : -Real.sqrt c < a * b := by
    nlinarith [show 0 ≤ Real.sqrt c by positivity, sq_nonneg (a * b + Real.sqrt c), Real.sqrt_nonneg c, h4, sq_nonneg (a * b), sq_nonneg (Real.sqrt c)]

  constructor
  · linarith
  · linarith