import Mathlib

theorem algebra_322254 {a : ℝ} (ha : a^2 - a - 1 = 0) :
    a^8 + 7 * a^(-4 : ℤ) = 48 := by 
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha 
    norm_num at ha 
  have h2 : a^2 = a + 1 := by
    linarith 
  have h3 : a^3 = 2*a + 1 := by 
    calc 
      a^3 = a * a^2 := by ring 
      _ = a * (a + 1) := by rw [h2] 
      _ = a^2 + a := by ring 
      _ = (a + 1) + a := by rw [h2] 
      _ = 2*a + 1 := by ring 
  have h4 : a^4 = 3*a + 2 := by 
    calc 
      a^4 = a * a^3 := by ring 
      _ = a * (2*a + 1) := by rw [h3] 
      _ = 2*a^2 + a := by ring 
      _ = 2*(a + 1) + a := by rw [h2] 
      _ = 3*a + 2 := by ring 
  have h5 : a^8 = 21*a + 13 := by
    have h6 : a^4 = 3*a + 2 := h4
    have h7 : a^8 = (a^4)^2 := by ring 
    rw [h7, h6]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  have h8 : a^(-4 : ℤ) = (-3*a + 5) := by 
    have h9 : a^(-4 : ℤ) = (a^4)⁻¹ := by 
      simp [zpow_neg, zpow_ofNat] 
    rw [h9]
    have h10 : a^4 = 3*a + 2 := h4 
    rw [h10]
    have h11 : a^2 = a + 1 := h2
    field_simp [(show 3*a + 2 ≠ 0 by
      by_contra h
      have h13 : 3*a + 2 = 0 := by linarith 
      nlinarith [h11, sq_nonneg (a), sq_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    )]
    <;> nlinarith [sq_nonneg (a), sq_nonneg (a - 1), sq_nonneg (a + 1)]
  rw [h5, h8]
  all_goals 
    nlinarith [sq_nonneg (a), sq_nonneg (a - 1), sq_nonneg (a + 1)]