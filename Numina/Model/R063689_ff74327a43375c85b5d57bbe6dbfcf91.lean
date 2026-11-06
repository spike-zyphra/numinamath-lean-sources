import Mathlib

theorem algebra_274015 (d p j : ℝ) (hp : p > 0) (hj : j > 0)
    (h : p = j + 200) (h1 : p / (8 * 60) = j / (18 * 60)) :
    d = 1000 := by 
  have h2 : 9 * p = 4 * j := by
    field_simp at h1
    linarith [h1]
  -- From 9p = 4j, solve for j
  have h3 : j = (9 / 4) * p := by 
    linarith [h2]
  rw [h3] at h 
  -- Now h becomes p = (9/4) * p + 200, which leads to contradiction
  nlinarith