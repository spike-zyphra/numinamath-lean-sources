import Mathlib

theorem algebra_8976 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x < 0, f x = x ^ 3 + x ^ 2) :
    f 2 = 4 := by
  have h1 : f (-2) = -4 := by
    specialize hf (-2) (by norm_num)
    rw [hf]
    norm_num
  have h2 : f (-2) = -f 2 := by
    specialize hodd 2
    linarith
  rw [h1] at h2
  linarith