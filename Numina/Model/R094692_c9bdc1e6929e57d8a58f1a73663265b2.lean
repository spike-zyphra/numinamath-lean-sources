import Mathlib

theorem algebra_44887 {a b c d : ℝ} (h1 : a + b + c + d = 20) (h2 : a * b + a * c + a * d + b * c + b * d + c * d = 150) :
    a = 5 ∧ b = 5 ∧ c = 5 ∧ d = 5 := by
  have h4 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 100 := by
    have h : (a + b + c + d) ^ 2 = 400 := by
      rw [h1]
      norm_num
    have h5 : (a + b + c + d) ^ 2 = a^2 + b^2 + c^2 + d^2 + 2 * (a * b + a * c + a * d + b * c + b * d + c * d) := by
      ring
    rw [h] at h5
    nlinarith [h2]
  
  have h3 : (a - 5) ^ 2 + (b - 5) ^ 2 + (c - 5) ^ 2 + (d - 5) ^ 2 = 0 := by
    nlinarith

  have ha : (a - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]

  have hb : (b - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]

  have hc : (c - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]

  have hd : (d - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]

  have ha2 : a - 5 = 0 := by
    nlinarith [sq_nonneg (a - 5)]

  have hb2 : b - 5 = 0 := by
    nlinarith [sq_nonneg (b - 5)]

  have hc2 : c - 5 = 0 := by
    nlinarith [sq_nonneg (c - 5)]

  have hd2 : d - 5 = 0 := by
    nlinarith [sq_nonneg (d - 5)]

  have ha3 : a = 5 := by linarith

  have hb3 : b = 5 := by linarith

  have hc3 : c = 5 := by linarith

  have hd3 : d = 5 := by linarith

  exact ⟨ha3, hb3, hc3, hd3⟩