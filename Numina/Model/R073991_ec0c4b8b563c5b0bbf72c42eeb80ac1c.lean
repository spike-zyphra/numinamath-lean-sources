import Mathlib

theorem algebra_18941 {m n : ℝ} (hmn : m * n = 7) (hsum : m + n = 8) :
    |m - n| = 6 := by 
  have h1 : n = 8 - m := by linarith
  rw [h1] at hmn
  have h2 : m^2 - 8 * m + 7 = 0 := by 
    linarith 
  have h3 : (m - 7) * (m - 1) = 0 := by 
    ring_nf at h2 ⊢
    linarith 
  cases' (mul_eq_zero.mp h3) with hm1 hm2 
  · -- Case $m - 7 = 0$, so $m = 7$
    have hm : m = 7 := by linarith 
    have hn : n = 1 := by 
      rw [hm] at h1
      linarith 
    rw [hm, hn]
    norm_num 
  · -- Case $m - 1 = 0$, so $m = 1$
    have hm : m = 1 := by linarith 
    have hn : n = 7 := by 
      rw [hm] at h1
      linarith 
    rw [hm, hn]
    norm_num