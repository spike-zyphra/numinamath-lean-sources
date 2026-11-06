import Mathlib

theorem algebra_272826 (d t : ℝ) (ht : t > 0) (h1 : d / 40 = t) (h2 : d / 50 = t - 5) :
    d = 1000 := by 
  have ht_eq : t = d / 40 := by
    linarith
  
  rw [ht_eq] at h2
  
  linarith