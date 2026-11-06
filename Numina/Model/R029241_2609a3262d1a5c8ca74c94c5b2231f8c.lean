import Mathlib

theorem algebra_20717 (dozen cup needed : ℝ) (hd : dozen = 12) (h : 20 * dozen = 15 * cup) (h1 : 144 = needed * cup) : needed = 9 := by 
  have h2 : (20 * 12 : ℝ) = 15 * cup := by 
    rw [hd] at h 
    linarith 
  have h3 : cup = (16 : ℝ) := by 
    nlinarith 
  rw [h3] at h1 
  have h4 : needed = (9 : ℝ) := by 
    nlinarith 
  linarith