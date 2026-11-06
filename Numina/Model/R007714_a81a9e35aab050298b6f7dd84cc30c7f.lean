import Mathlib

theorem combinatorics_94732 
  (P : ℕ → ℝ) 
  (hP0 : P 0 = 1) 
  (hP : ∀ k : ℕ, P (k+1) = (1 - P k)/3) : 
  P 7 * 729 = 182 := by

  have hP1 : P 1 = 0 := by 
    rw [hP 0, hP0]
    norm_num

  have hP2 : P 2 = 1 / 3 := by 
    rw [hP 1, hP1]
    norm_num

  have hP3 : P 3 = 2 / 9 := by 
    rw [hP 2, hP2]
    norm_num

  have hP4 : P 4 = 7 / 27 := by 
    rw [hP 3, hP3]
    norm_num
  
  have hP5 : P 5 = 20 / 81 := by 
    rw [hP 4, hP4]
    norm_num

  have hP6 : P 6 = 61 / 243 := by 
    rw [hP 5, hP5]
    norm_num

  have hP7 : P 7 = 182 / 729 := by 
    rw [hP 6, hP6]
    norm_num
  
  rw [hP7]
  norm_num