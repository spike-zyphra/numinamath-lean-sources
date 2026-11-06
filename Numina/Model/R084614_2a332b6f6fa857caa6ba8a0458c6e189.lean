import Mathlib

theorem algebra_21432 {a r : ℤ} (hr : r ≠ 0) (h4 : a * r^3 = 24) (h11 : a * r^10 = 3072) :
    r = 2 := by
  have eq1 : a * r^10 = (a * r^3) * r^7 := by
    ring_nf
  rw [h4] at eq1
  rw [h11] at eq1
  have h_eq : r^7 = 128 := by 
    nlinarith
  have h_eq2 : r^7 = 128 := h_eq
  have h_eq3 : r = 2 := by
    have h1 : r^7 = 128 := h_eq2
    have h2 : r^7 = 2^7 := by 
      rw [h1]
      all_goals norm_num
    have h3 : r = 2 := by
      have h4 : r^7 - 2^7 = 0 := by 
        calc 
          r^7 - 2^7 = (r^7 : ℤ) - (2^7 : ℤ) := by norm_num
          _ = (128 : ℤ) - (128 : ℤ) := by rw [h_eq2]; all_goals norm_num
          _ = (0 : ℤ) := by norm_num
      have eq : r^7 - 2^7 = (r - 2) * (r^6 + 2*r^5 + 4*r^4 + 8*r^3 + 16*r^2 + 32*r + 64) := by 
        ring_nf
      rw [eq] at h4
      cases' (mul_eq_zero.1 h4) with h5 h6
      · -- Case where r - 2 = 0, so r = 2
        linarith
      · -- Case where the polynomial factor is zero
        nlinarith [sq_nonneg (r^3), sq_nonneg (r^2 - 1), sq_nonneg (r + 1), sq_nonneg (r * (r + 1)), sq_nonneg (r * (r + 1) * (r + 2)), sq_nonneg (r * (r^2 + 1)), sq_nonneg (r * (r + 1)), sq_nonneg (r * (r - 1)), sq_nonneg (r^2 + r + 1)]
    exact h3
  exact h_eq3