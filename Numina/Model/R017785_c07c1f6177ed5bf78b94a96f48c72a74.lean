import Mathlib

theorem algebra_207741 (a d : ℝ) (h₀ : 0 < d) (h₁ : a^3 + (a+d)^3 + (a+2*d)^3 + (a+3*d)^3 + (a+4*d)^3 = 0)
    (h₂ : a^2 + (a+d)^2 + (a+2*d)^2 + (a+3*d)^2 + (a+4*d)^2 = 70) :
    a = -2 * Real.sqrt 7 := by

  have h3 : (a + 2 * d) * (a ^ 2 + 4 * a * d + 10 * d ^ 2) = 0 := by 
    ring_nf at h₁ ⊢ 
    nlinarith [sq_nonneg (d ^ 2), sq_nonneg (a + 2 * d), sq_nonneg (a ^ 2 - a * 4 * d + 2 * d ^ 2), sq_nonneg (d ^ 2), sq_nonneg (a + 2 * d), sq_pos_of_pos h₀]

  cases (mul_eq_zero.mp h3) with 
  | inl h4 =>
    have h4' : a + 2 * d = 0 := h4
    have h10 : a = -2 * d := by linarith [h4']
    have eq1 : 10 * d ^ 2 = 70 := by
      rw [show a = -2 * d by linarith [h4']] at h₂ 
      nlinarith
    have h13 : d ^ 2 = 7 := by
      nlinarith 
    have h14 : d = Real.sqrt 7 := by
      have h15 : d > 0 := by linarith [h₀]
      have h16 : d ^ 2 = 7 := h13
      have h17 : d = Real.sqrt 7 := by
        rw [← h16]
        field_simp 
      linarith 
    have h18 : a = -2 * Real.sqrt 7 := by
      rw [show a = -2 * d by linarith [h4']]
      rw [h14]
    linarith
  | inr h5 =>
    have h6 : a ^ 2 + 4 * a * d + 10 * d ^ 2 = 0 := by
      linarith [h5]
    nlinarith [sq_nonneg (a + 2 * d), sq_nonneg (d), sq_pos_of_pos h₀, sq_nonneg (a + 4 * d), sq_nonneg (d ^ 2)]