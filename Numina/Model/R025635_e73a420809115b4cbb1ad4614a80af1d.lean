import Mathlib

theorem algebra_308239 (d : ℝ) (h : d > 0) (h1 : 7.5 + 2.5 = d / (4 - d / 10)) (h2 : 7.5 - 2.5 = d / (4 + d / 10)) :
    d = 20 / 3 := by
  have eq1 : (7.5 + 2.5 : ℝ) = 10 := by norm_num
  have eq2 : (7.5 - 2.5 : ℝ) = 5 := by norm_num
  rw [eq1] at h1
  rw [eq2] at h2
  have eq4 : d = 40 := by
    have h5 : 4 + d / 10 ≠ 0 := by
      by_contra h3
      have eq5 : 4 + d / 10 = (0 : ℝ) := by linarith [h3]
      have eq6 : d / 10 = -4 := by linarith
      have eq7 : d = -40 := by
        linarith [eq6]
      nlinarith -- Contradicts h: d > 0
    have h6 : 5 = d / (4 + d / 10) := by
      linarith [h2]
    field_simp [h5] at h6 
    linarith 
  rw [eq4] at h1 
  norm_num at h1 
  all_goals linarith