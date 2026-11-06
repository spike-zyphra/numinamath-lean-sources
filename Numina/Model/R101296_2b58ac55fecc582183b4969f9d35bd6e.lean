import Mathlib

theorem algebra_328340 {n : ℤ} (hn : (n - 2003)^2 + (2004 - n)^2 = 1) :
    (2004 - n) * (n - 2003) = 0 := by
  have h1 : (n - 2003 : ℤ) + (2004 - n) = 1 := by
    ring
  have h2 : ((n - 2003 : ℤ) + (2004 - n)) ^ 2 = 1 := by
    rw [h1]
    all_goals norm_num
  have h3 : ((n - 2003 : ℤ) + (2004 - n)) ^ 2 = (n - 2003) ^ 2 + (2004 - n) ^ 2 + 2 * ((2004 - n) * (n - 2003)) := by
    ring
  rw [h3] at h2
  rw [hn] at h2
  linarith