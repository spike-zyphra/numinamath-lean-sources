import Mathlib

theorem algebra_100338 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (heven : ∀ x, f (x + 1) = f (-x + 1)) (hf : ∀ x ∈ Set.Icc (-1) 0, f x = x^3) :
    f (9 / 2) = 1 / 8 := by 
  have h1 : f (9 / 2) = f (-5 / 2) := by
    have h2 := heven (7 / 2)
    norm_num at h2 ⊢
    linarith
  have h3 : f (-5 / 2) = - f (5 / 2) := by
    have h4 := hodd (5 / 2)
    norm_num at h4 ⊢
    linarith
  have h4 : f (5 / 2) = f (-1 / 2) := by
    have h5 := heven (3 / 2)
    norm_num at h5 ⊢
    linarith
  have h5 : f (-1 / 2) = (-1 / 2) ^ 3 := by
    apply hf
    norm_num
  rw [h1, h3, h4, h5]
  norm_num