import Mathlib

theorem algebra_120953 (f : ℝ → ℝ) (h : ∀ x y, f (x ^ 2 + y) = f x + f (y ^ 2)) :
    f (-1) = 0 := by
  have h1 : f 0 = 0 := by
    specialize h 0 0 
    norm_num at h 
    linarith

  have eq1 : f (-1) = f 1 := by
    specialize h 0 (-1)
    norm_num at h
    linarith [h1]

  have h5 : f 1 = 0 := by
    specialize h 1 (-1)
    norm_num at h 
    linarith [h1]

  linarith [eq1, h5]