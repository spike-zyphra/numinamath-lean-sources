import Mathlib

theorem algebra_12859 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) = x * f y) (hf : f 1 = 25) : f 79 = 1975 := by
  have hfx : ∀ x, f x = x * 25 := by 
    intro x
    have eq1 : f x = x * f 1 := by 
      specialize h x 1
      simp at h 
      linarith 
    rw [hf] at eq1 
    linarith 
  have h79 : f 79 = 79 * 25 := hfx 79 
  norm_num at h79 
  linarith