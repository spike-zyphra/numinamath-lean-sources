import Mathlib

theorem algebra_12177 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b) (h : f 6 - f 2 = 12) :
    f 12 - f 2 = 30 := by
  rcases hf with ⟨a, b, hfab⟩
  have eq1 : f 6 = a * 6 + b := by
    rw [hfab]
    all_goals linarith 
  have eq2 : f 2 = a * 2 + b := by 
    rw [hfab]
    all_goals linarith 
  rw [eq1, eq2] at h 
  have ha : a = 3 := by
    linarith 
  have eq3 : f 12 = a * 12 + b := by
    rw [hfab]
    all_goals linarith 
  have eq4 : f 2 = a * 2 + b := by
    rw [hfab]
    all_goals linarith 
  rw [eq3, eq4] 
  rw [ha]
  all_goals linarith