import Mathlib

theorem algebra_8203 {a b : ℝ} (h : ∀ k : ℝ, {x : ℝ | (2 * k * x - a) / 7 = (x - b * k) / 3 + 1} = {8}) :
    3 * a - 7 * b = -29 := by
  have eq1 := h 0 
  have eq2 : (8 : ℝ) ∈ {x : ℝ | (2 * (0 : ℝ) * x - a) / 7 = (x - b * (0 : ℝ)) / 3 + 1} := by 
    rw [eq1]
    simp
  have eq3 : (2 * (0 : ℝ) * (8 : ℝ) - a) / 7 = ( (8 : ℝ) - b * (0 : ℝ) ) / 3 + 1 := by
    simpa using eq2 
  have eq4 : -a / 7 = (8 / 3 + 1) := by 
    norm_num at eq3 
    linarith 
  have eq5 : -a / 7 = 11 / 3 := by 
    norm_num at eq4 ⊢ 
    linarith 
  have ha1 : a = -77 / 3 := by 
    linarith 
  have eq11 := h 1 
  have eq12 : (8 : ℝ) ∈ {x : ℝ | (2 * (1 : ℝ) * x - a) / 7 = (x - b * (1 : ℝ)) / 3 + 1} := by 
    rw [eq11]
    simp 
  have eq13 : (2 * (1 : ℝ) * (8 : ℝ) - a) / 7 = ( (8 : ℝ) - b * (1 : ℝ) ) / 3 + 1 := by
    simpa using eq12 
  rw [ha1] at eq13 
  have hb1 : b = -48 / 7 := by 
    norm_num at eq13 
    linarith 
  rw [ha1, hb1]
  norm_num