import Mathlib

theorem algebra_17242 (pages : ℕ) (hpages : pages = 200) (ppm : ℕ) (hppm : ppm = 17) :
    round ((pages : ℝ) / ppm) = 12 := by 
  rw [hpages, hppm]
  norm_num [round_eq]