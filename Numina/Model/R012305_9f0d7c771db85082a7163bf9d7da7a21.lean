import Mathlib

theorem geometry_97257
  {l w x : ℝ} (hl : l > 0) (hw : w > 0)
  (h : l^2 + w^2 = x^2) (h1 : l = 2 * w) :
  l * w = 2 / 5 * x^2 := by

  have h2 : (2 * w) ^2 + w^2 = x^2 := by
    rw [show l = 2 * w by linarith [h1] ] at h
    linarith
  
  have h3 : 5 * (w ^2) = x^2 := by
    nlinarith

  have hw2 : w ^2 = x^2 / 5 := by 
    linarith
  
  have h4 : l * w = 2 * (w ^2) := by
    rw [show l = 2 * w by linarith [h1]]
    ring

  rw [h4]
  rw [hw2]
  ring