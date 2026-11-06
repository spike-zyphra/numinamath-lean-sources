import Mathlib

theorem algebra_196026 (a b c : ℝ) (ha : a^3 - 2*a^2 + 3*a - 4 = 0) (hb : b^3 - 2*b^2 + 3*b - 4 = 0)
    (hc : c^3 - 2*c^2 + 3*c - 4 = 0) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1/(a*(b^2 + c^2 - a^2)) + 1/(b*(c^2 + a^2 - b^2)) + 1/(c*(a^2 + b^2 - c^2)) = 1/8 := by

  have ha1 : a ≠ 0 := by
    intro ha0
    rw [ha0] at ha
    nlinarith

  have hb1 : b ≠ 0 := by
    intro hb0
    rw [hb0] at hb
    nlinarith

  have hc1 : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    nlinarith
  
  have h1 : a^2 + a * b + b^2 - 2 * (a + b) + 3 = 0 := by
    have h11 : a^3 - 2 * a^2 + 3 * a - 4 = 0 := by linarith [ha]
    have h12 : b^3 - 2 * b^2 + 3 * b - 4 = 0 := by linarith [hb]
    have eq_sub : (a^3 - 2 * a^2 + 3 * a - 4) - (b^3 - 2 * b^2 + 3 * b - 4) = 0 := by linarith [h11, h12]
    have eq1 : (a - b) * (a^2 + a * b + b^2 - 2 * (a + b) + 3) = 0 := by 
      ring_nf at eq_sub ⊢
      nlinarith
    cases' (mul_eq_zero.mp eq1) with h2 h3
    · -- case a - b = 0
      exfalso
      exact hdist.1 (by linarith)
    · -- case a^2 + a * b + b^2 - 2 * (a + b) + 3 = 0
      linarith
  
  have h2 : a^2 + a * c + c^2 - 2 * (a + c) + 3 = 0 := by
    have h11 : a^3 - 2 * a^2 + 3 * a - 4 = 0 := by linarith [ha]
    have h12 : c^3 - 2 * c^2 + 3 * c - 4 = 0 := by linarith [hc]
    have eq_sub : (a^3 - 2 * a^2 + 3 * a - 4) - (c^3 - 2 * c^2 + 3 * c - 4) = 0 := by linarith [h11, h12]
    have eq1 : (a - c) * (a^2 + a * c + c^2 - 2 * (a + c) + 3) = 0 := by 
      ring_nf at eq_sub ⊢
      nlinarith
    cases' (mul_eq_zero.mp eq1) with h2 h3
    · -- case a - c = 0
      exfalso
      exact hdist.2.1 (by linarith)
    · -- case a^2 + a * c + c^2 - 2 * (a + c) + 3 = 0
      linarith
  
  have h3 : b^2 + b * c + c^2 - 2 * (b + c) + 3 = 0 := by
    have h11 : b^3 - 2 * b^2 + 3 * b - 4 = 0 := by linarith [hb]
    have h12 : c^3 - 2 * c^2 + 3 * c - 4 = 0 := by linarith [hc]
    have eq_sub : (b^3 - 2 * b^2 + 3 * b - 4) - (c^3 - 2 * c^2 + 3 * c - 4) = 0 := by linarith [h11, h12]
    have eq1 : (b - c) * (b^2 + b * c + c^2 - 2 * (b + c) + 3) = 0 := by 
      ring_nf at eq_sub ⊢
      nlinarith
    cases' (mul_eq_zero.mp eq1) with h2 h3
    · -- case b - c = 0
      exfalso
      exact hdist.2.2 (by linarith)
    · -- case b^2 + b * c + c^2 - 2 * (b + c) + 3 = 0
      linarith
  
  have h4 : a * (b ^ 2 + c ^ 2 - a ^ 2) ≠ 0 := by
    intro h
    have h5 : b ^ 2 + c ^ 2 - a ^ 2 = 0 := by
      apply (mul_left_inj' ha1).mp
      linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
      intro h'
      apply hdist.1
      linarith
    ), sq_pos_of_ne_zero (show (a - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.1
      linarith
    ), sq_pos_of_ne_zero (show (b - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.2
      linarith
    ), sq_pos_of_ne_zero ha1, sq_pos_of_ne_zero hb1, sq_pos_of_ne_zero hc1, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have h5 : b * (c ^ 2 + a ^ 2 - b ^ 2) ≠ 0 := by
    intro h
    have h6 : c ^ 2 + a ^ 2 - b ^ 2 = 0 := by
      apply (mul_left_inj' hb1).mp
      linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
      intro h'
      apply hdist.1
      linarith
    ), sq_pos_of_ne_zero (show (a - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.1
      linarith
    ), sq_pos_of_ne_zero (show (b - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.2
      linarith
    ), sq_pos_of_ne_zero ha1, sq_pos_of_ne_zero hb1, sq_pos_of_ne_zero hc1, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have h6 : c * (a ^ 2 + b ^ 2 - c ^ 2) ≠ 0 := by
    intro h
    have h7 : a ^ 2 + b ^ 2 - c ^ 2 = 0 := by
      apply (mul_left_inj' hc1).mp
      linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
      intro h'
      apply hdist.1
      linarith
    ), sq_pos_of_ne_zero (show (a - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.1
      linarith
    ), sq_pos_of_ne_zero (show (b - c : ℝ) ≠ 0 by
      intro h'
      apply hdist.2.2
      linarith
    ), sq_pos_of_ne_zero ha1, sq_pos_of_ne_zero hb1, sq_pos_of_ne_zero hc1, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

  field_simp [h4, h5, h6]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]