import Mathlib

theorem algebra_10312 {g : ℝ → ℝ} (hg : g = fun x => 3 * x - 4) (a : ℝ) (ha : g a = 0) :
    a = 4 / 3 := by 
  have h1 : 3 * a - 4 = 0 := by
    rw [hg] at ha
    simp at ha
    linarith
  linarith