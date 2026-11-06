import Mathlib

theorem algebra_102251 (v : ℝ) (h : v > 0) (h1 : 20 / v = 20 / (2 * v) + 40 / v) :
    20 / v = 40 := by 
  have h2 : 20 / v * v = (20 / (2 * v) + 40 / v) * v := by
    rw [h1]

  have h3 : 20 / v * v = 20 := by 
    field_simp at *
    all_goals linarith
  
  have h4 : (20 / (2 * v) + 40 / v) * v = 50 := by 
    have h5 : 20 / (2 * v) * v = 10 := by
      field_simp at *
      all_goals nlinarith

    have h6 : 40 / v * v = 40 := by 
      field_simp at *
      all_goals nlinarith

    calc
      (20 / (2 * v) + 40 / v) * v = (20 / (2 * v) * v) + (40 / v * v) := by ring
      _ = 10 + 40 := by rw [h5, h6]
      _ = 50 := by norm_num

  rw [h3] at h2
  rw [h4] at h2
  all_goals linarith