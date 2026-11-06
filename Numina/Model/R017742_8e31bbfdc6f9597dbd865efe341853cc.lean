import Mathlib

theorem algebra_153774 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 0) (h2 : a^3 + b^3 + c^3 = a^5 + b^5 + c^5) :
    a^2 + b^2 + c^2 = 6 / 5 := by

  have h3 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    have h4 : c = -a - b := by linarith
    rw [h4]
    ring_nf

  have h5 : a * b + a * c + b * c = -3 / 5 := by 
    have h4 : c = -a - b := by linarith 
    have h5' : a * b * c ≠ 0 := by 
      apply mul_ne_zero 
      apply mul_ne_zero 
      exact ha 
      exact hb 
      exact hc 
    have eq1 : a^5 + b^5 + c^5 = -5 * (a * b * c) * (a * b + a * c + b * c) := by
      rw [h4]
      ring_nf 
    have eq2 : 3 * (a * b * c) = -5 * (a * b * c) * (a * b + a * c + b * c) := by 
      have eq3 : a^3 + b^3 + c^3 = a^5 + b^5 + c^5 := by linarith 
      rw [h3, eq1] at eq3 
      linarith
    -- Since `a * b * c ≠ 0`, we can solve for `a * b + a * c + b * c`
    have : a * b + a * c + b * c = -3 / 5 := by 
      apply (mul_left_inj' h5').mp 
      linarith 
    assumption

  have h3' : a^2 + b^2 + c^2 = 6/5 := by
    have eq4 : a^2 + b^2 + c^2 = -2 * (a * b + a * c + b * c) := by 
      have h4' : a + b + c = 0 := h1 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    rw [eq4, h5]
    norm_num 
  linarith