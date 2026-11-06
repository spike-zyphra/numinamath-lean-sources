import Mathlib

theorem algebra_16533 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) (h4 : f 4 = 5) :
    f 5 = 25 / 4 := by 
  have f1 : f 1 = 5 / 4 := by 
    have h1 : f 4 = 4 * f 1 := by 
      calc 
        f 4 = f (1 + 1 + 1 + 1) := by norm_num 
        _ = f (1 + 1 + 1) + f 1 := by rw [h]
        _ = f (1 + 1) + f 1 + f 1 := by rw [h]
        _ = f 1 + f 1 + f 1 + f 1 := by rw [h]
        _ = 4 * f 1 := by ring 
    rw [h4] at h1
    linarith 
  have h5 : f 5 = f 4 + f 1 := by 
    rw [←h]
    norm_num 
  rw [h4, f1] at h5 
  norm_num at h5 ⊢ 
  linarith