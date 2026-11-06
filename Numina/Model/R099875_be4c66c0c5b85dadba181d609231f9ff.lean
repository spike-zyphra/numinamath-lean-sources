import Mathlib

theorem algebra_303380 {x y z : ℝ}
    (h₁ : 2006 * (x - y) + 2000 * (y - z) + 2008 * (z - x) = 0)
    (h₂ : 2000 ^ 2 * (x - y) + 2000 ^ 2 * (y - z) + 2000 ^ 2 * (z - x) = 2008) :
    z - y = 2008 := by 
  have eq1 : 2000 ^ 2 * (x - y) + 2000 ^ 2 * (y - z) + 2000 ^ 2 * (z - x) = 2000^2 * ((x - y) + (y - z) + (z - x)) := by
    ring
  have eq2 : (x - y) + (y - z) + (z - x) = 0 := by 
    ring
  rw [eq1] at h₂ 
  rw [eq2] at h₂ 
  linarith