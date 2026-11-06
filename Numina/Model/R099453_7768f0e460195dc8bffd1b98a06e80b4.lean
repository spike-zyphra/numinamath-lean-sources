import Mathlib

theorem algebra_5785 {f g : ℝ → ℝ} {a : ℝ} (hf : f = fun x => x / 5 + 3) (hg : g = fun x => 4 - x)
    (h : f (g a) = 5) : a = -6 := by 
  have h1 : f (g a) = (4 - a) / 5 + 3 := by
    rw [hg]
    rw [hf]
    all_goals ring
  rw [h1] at h
  linarith