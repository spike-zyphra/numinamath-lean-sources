import Mathlib

theorem algebra_9213 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x < 0, f x = -x^2 + 2 * x) :
    f 3 = 15 := by
  have h3 : f (-3) = - f 3 := by
    specialize hodd 3
    norm_num at hodd ⊢
    linarith

  have h1 : f (-3) = - (-3) ^ 2 + 2 * (-3) := by 
    apply hf
    norm_num
  have h2 : f (-3) = -15 := by
    rw [h1]
    norm_num

  rw [h3] at h2
  linarith