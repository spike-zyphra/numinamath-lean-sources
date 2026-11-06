import Mathlib

theorem algebra_232311 {l w h : ℝ} (hl : l = 20) (hw : w = 15) (hvol : l * w * h = 2 * (l * w + w * h + l * h)) :
    h = 60 / 23 := by
  rw [hl, hw] at hvol
  have eq1 : (20 : ℝ) * (15 : ℝ) * h = 2 * ((20 : ℝ) * (15 : ℝ) + (15 : ℝ) * h + (20 : ℝ) * h) := by
    linarith
  have eq2 : (300 : ℝ) * h = 600 + 70 * h := by 
    linarith [eq1]
  have eq3 : (230 : ℝ) * h = 600 := by 
    linarith [eq2]
  have eq4 : h = (60 / 23 : ℝ) := by 
    linarith
  linarith [eq4]