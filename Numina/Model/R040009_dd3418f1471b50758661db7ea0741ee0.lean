import Mathlib

theorem algebra_132915 {f : ℝ → ℝ} (h0 : f 0 = 1)
    (hf : ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) :
    ∀ x, f x = x + 1 := by
  have f1 : f 1 = 2 := by
    specialize hf 0 0 
    norm_num [h0] at hf 
    linarith 
  intro x 
  have h := hf x 0 
  simp [h0, f1] at h 
  have hx : f x = x + 1 := by 
    linarith 
  exact hx
  all_goals linarith