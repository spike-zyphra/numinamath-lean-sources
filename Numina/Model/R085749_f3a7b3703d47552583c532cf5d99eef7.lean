import Mathlib

theorem number_theory_4397 (m n : ℤ) (h1 : 3*m+2=5*n+3) (h2 : 3*m+2>30) (h3 : 5*n+3 < 40) : m*n=84 := by
  have h4 : n > 5 := by
    omega
  have h5' : n < 8 := by 
    omega
  have hn : n = 6 ∨ n = 7 := by 
    omega
  rcases hn with (hn | hn)
  · -- Assume n = 6
    rw [hn] at h1
    omega
  · -- Assume n = 7
    rw [hn] at h1
    have hm : m = 12 := by 
      omega
    rw [hm, hn]
    all_goals norm_num