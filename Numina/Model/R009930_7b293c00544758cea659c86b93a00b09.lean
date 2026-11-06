import Mathlib

theorem algebra_10219 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2 - 2 * x + m)
    (hg : g = fun x => x ^ 2 - 2 * x + 4 * m) (h : 2 * f 4 = g 4) :
    m = 4 := by 
  rw [hf] at h 
  rw [hg] at h 
  simp at h 
  linarith