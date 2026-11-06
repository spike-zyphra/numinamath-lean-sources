import Mathlib

theorem algebra_15145 {m : ℝ} (h : (m - 4) ^ 3 = (1 / 8) ^ (-1 : ℤ)) : m = 6 := by
  have h1 : (1 / 8 : ℝ) ^ (-1 : ℤ) = 8 := by
    norm_num
  rw [h1] at h

  have h2 : m - 4 = 2 := by
    have h3 : (m - 4) ^ 3 - 8 = 0 := by linarith
    have h4 : (m - 4 - 2) * ((m - 4) ^ 2 + (m - 4) * 2 + 4) = 0 := by
      ring_nf at h3 ⊢
      linarith
  
    cases' (mul_eq_zero.mp h4) with h5 h6
    · linarith
  
    · -- Show that the quadratic is positive definite
      have h7 : (m - 4) ^ 2 + (m - 4) * 2 + 4 > 0 := by 
        nlinarith [sq_nonneg ((m - 4) + 1)]
      linarith
  
  
  linarith