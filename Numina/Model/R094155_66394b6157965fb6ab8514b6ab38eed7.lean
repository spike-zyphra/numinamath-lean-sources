import Mathlib

theorem algebra_177582 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (h1 : f 1 = 3) :
    (f 1 ^ 2 + f 2) / f 1 + (f 2 ^ 2 + f 4) / f 3 + (f 3 ^ 2 + f 6) / f 5 + (f 4 ^ 2 + f 8) / f 7 = 24 := by
  have f2 : f 2 = 9 := by
    specialize h 1 1
    rw [show (1 + 1 : ℝ) = (2 : ℝ) by norm_num] at h
    rw [h1] at h
    norm_num at h ⊢
    linarith
  have f3 : f 3 = 27 := by
    specialize h 2 1
    rw [show (2 + 1 : ℝ) = (3 : ℝ) by norm_num] at h
    rw [f2, h1] at h
    norm_num at h ⊢
    linarith
  have f4 : f 4 = 81 := by
    specialize h 3 1
    rw [show (3 + 1 : ℝ) = (4 : ℝ) by norm_num] at h
    rw [f3, h1] at h
    norm_num at h ⊢
    linarith
  have f5 : f 5 = 243 := by
    specialize h 4 1
    rw [show (4 + 1 : ℝ) = (5 : ℝ) by norm_num] at h
    rw [f4, h1] at h
    norm_num at h ⊢
    linarith
  have f6 : f 6 = 729 := by
    specialize h 5 1
    rw [show (5 + 1 : ℝ) = (6 : ℝ) by norm_num] at h
    rw [f5, h1] at h
    norm_num at h ⊢
    linarith
  have f7 : f 7 = 2187 := by
    specialize h 6 1
    rw [show (6 + 1 : ℝ) = (7 : ℝ) by norm_num] at h
    rw [f6, h1] at h
    norm_num at h ⊢
    linarith
  have f8 : f 8 = 6561 := by
    specialize h 7 1
    rw [show (7 + 1 : ℝ) = (8 : ℝ) by norm_num] at h
    rw [f7, h1] at h
    norm_num at h ⊢
    linarith
  rw [show f 1 = (3 : ℝ) by linarith [h1], show f 2 = (9 : ℝ) by linarith [f2], show f 3 = (27 : ℝ) by linarith [f3], 
      show f 4 = (81 : ℝ) by linarith [f4], show f 5 = (243 : ℝ) by linarith [f5], show f 6 = (729 : ℝ) by linarith [f6], 
      show f 7 = (2187 : ℝ) by linarith [f7], show f 8 = (6561 : ℝ) by linarith [f8]]
  norm_num