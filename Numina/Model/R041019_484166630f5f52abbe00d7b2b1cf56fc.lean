import Mathlib

theorem other_47540 (v : ℝ) (h : v > 0) (h1 : 2 * v = 4 * (v - w)) (h2 : 4 * v = 6 * (v - w)) :
    w = 6 := by
  have eq1 : v = 2 * w := by
    linarith
  have eq2 : v = 3 * w := by
    linarith 
  -- Therefore from h1 and h2, we have from h1: v = 2 * w 
  -- From h2: v = 3 * w
  -- So 2 * w = 3 * w => w = 0
  have eq3 : w = 0 := by 
    linarith 
  have eq4 : v = 0 := by 
    linarith [eq1, eq3]
  linarith