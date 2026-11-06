import Mathlib

theorem number_theory_967 (m n : ℤ) (h1 : 3 * m + 2 = 5 * n + 3) (h2 : 3 * m + 2 > 30) (h3 : 5 * n + 3 < 40) : m * n = 84 := by
  have h4 : 3 * m = 5 * n + 1 := by 
    linarith 
  have h5 : n > 5 := by 
    omega 
  have h6 : n < 8 := by 
    omega 
  have h7 : n = 6 ∨ n = 7 := by 
    omega 
  rcases h7 with h | h 
  · 
    rw [show n = 6 by linarith] at h4 
    omega 
  · 
    rw [show n = 7 by linarith] at h4 
    have hm : m = 12 := by 
      omega 
    rw [show m = 12 by linarith, show n = 7 by linarith]
    all_goals norm_num