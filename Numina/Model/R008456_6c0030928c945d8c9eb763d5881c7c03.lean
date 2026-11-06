import Mathlib

theorem algebra_13772 (l : ℝ → ℝ) (a b x : ℝ) (hl : l = fun x => a * x + b) 
  (h1 : l 9 = 1) (h2 : l 5 = 5) (h3 : l x = 0):
  x = 10 := by
  have eq1 : a * 9 + b = 1 := by 
    rw [hl] at h1 
    simpa using h1
  have eq2 : a * 5 + b = 5 := by 
    rw [hl] at h2 
    simpa using h2
  have eq3 : a * x + b = 0 := by 
    rw [hl] at h3 
    simpa using h3

  have ha : a = -1 := by 
    linarith 
  have hb : b = 10 := by 
    rw [ha] at eq1 
    linarith 
  rw [ha, hb] at eq3 
  linarith