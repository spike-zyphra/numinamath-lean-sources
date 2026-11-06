import Mathlib

theorem algebra_317945 {f g : ℝ → ℝ} (hf : f.LeftInverse g) (hg : g.RightInverse f)
    (h : g 1 = 0) : f (1 / 3 * 6 - 2) = 1 := by
  have h1 : f 0 = 1 := by 
    have h2 : f (g 1) = 1 := hf 1
    rw [h] at h2
    linarith
  
  have h2 : (1 / 3 * 6 - 2 : ℝ) = 0 := by
    norm_num
  
  rw [h2]
  exact h1