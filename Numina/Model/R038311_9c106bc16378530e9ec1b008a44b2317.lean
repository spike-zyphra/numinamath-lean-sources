import Mathlib

theorem calculus_62019 (T : ℝ) (hT : T > 0) (h : 30 / T = 30 / (1.3 * T) + 30 / (1.7 * T)) :
    T = 111 / Real.sqrt 111 := by
  have h1 : T ≠ 0 := by linarith
  have eq1 : 30 = (30 / (1.3 : ℝ) + 30 / (1.7 : ℝ)) := by
    have eq2 : 30 / T = 30 / (1.3 * T) + 30 / (1.7 * T) := h
    have eq4 : 30 = (30 / (1.3 * T) + 30 / (1.7 * T)) * T := by 
      have eq5 : (30 / T = 30 / (1.3 * T) + 30 / (1.7 * T)) := h 
      field_simp [h1] at eq5 ⊢
      nlinarith
    have eq5 : (30 / (1.3 * T) + 30 / (1.7 * T)) * T = (30 / (1.3 : ℝ) + 30 / (1.7 : ℝ)) := by 
      field_simp [h1]
      <;> ring_nf
    rw [eq5] at eq4
    linarith
  norm_num at eq1
  all_goals linarith