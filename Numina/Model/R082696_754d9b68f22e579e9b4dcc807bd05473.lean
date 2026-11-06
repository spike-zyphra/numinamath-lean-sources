import Mathlib

theorem algebra_4883 {g : ℝ → ℝ} (hg : g = fun x => 3 * x - 4) (a : ℝ) (h : g a = 0) :
    a = 4 / 3 := by 
  rw [hg] at h 
  simp at h 
  linarith