import Mathlib

theorem number_theory_10291 (k y: ℝ) (hp : 0.5 * (-8.4) +y = 14 ) (hq: -2 * (-8.4) +y = k ) : k = 35 := by
  have hy : y = 18.2 := by 
    norm_num at hp 
    linarith 
  rw [hy] at hq 
  norm_num at hq 
  linarith