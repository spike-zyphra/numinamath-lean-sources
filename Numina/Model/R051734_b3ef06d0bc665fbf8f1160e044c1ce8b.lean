import Mathlib

theorem algebra_310790 {x : ℝ} (hx : x ≠ 0) (h : x - 2008 / x = 5) :
    ((x - 2)^3 - (x - 1)^2 + 1) / (x - 2) = 2012 := by 
  have h1 : x^2 - 5 * x - 2008 = 0 := by
    field_simp [hx] at h 
    nlinarith 
  have h2 : (x - 2) ≠ 0 := by 
    by_contra h4 
    have h5 : x = 2 := by linarith 
    rw [h5] at h 
    norm_num [h5] at h1
    all_goals norm_num [h5] at h 
    all_goals linarith 
  have eq1 : (x - 2)^3 - (x - 1)^2 + 1 = (x - 2) * (x^2 - 5 * x + 4) := by 
    ring 
  have h3 : x^2 - 5 * x = 2008 := by 
    linarith [h1] 
  rw [eq1] 
  field_simp [h2] 
  linarith [h3]