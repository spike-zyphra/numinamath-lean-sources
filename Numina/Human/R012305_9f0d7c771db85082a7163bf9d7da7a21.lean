import Mathlib

theorem geometry_97257
  {l w x : ℝ} (hl : l > 0) (hw : w > 0)
  (h : l^2 + w^2 = x^2) (h1 : l = 2 * w) :
  l * w = 2 / 5 * x^2 := by 

  have hw : x^2 = 5 * w^2 := by
    calc
      x ^2 = l^2 + w^2  := by linarith
      _ = (2*w)^2 + w^2 := by rw [h1]
      _ = 4*w^2 + w^2 := by ring
      _ = 5*w^2 := by ring

  calc       
    l*w  = (2*w)*w := by rw [h1]
    _ = 2*w^2 := by ring
    _ = 2/5 * (5*w^2) := by linarith
    _ = 2/5 * x^2 := by rw [hw]