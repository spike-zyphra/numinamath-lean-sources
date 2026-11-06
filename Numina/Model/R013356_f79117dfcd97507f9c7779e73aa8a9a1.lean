import Mathlib

theorem algebra_11458 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (hf : f 1 = 3) :
    (f 1 ^ 2 + f 2) / f 1 + (f 2 ^ 2 + f 4) / f 3 + (f 3 ^ 2 + f 6) / f 5 +
    (f 4 ^ 2 + f 8) / f 7 = 24 := by

  have f2 : f (2 : ℝ) = 9 := by
    specialize h 1 1
    have h1 : f (1 + 1) = f 1 * f 1 := by simpa using h
    rw [show (1 + 1 : ℝ) = 2 by norm_num] at h1
    rw [hf] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f3 : f (3 : ℝ) = 27 := by
    specialize h 2 1
    have h1 : f (2 + 1) = f (2) * f 1 := by simpa using h
    rw [show (2 + 1 : ℝ) = 3 by norm_num] at h1
    rw [f2, hf] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f4 : f (4 : ℝ) = 81 := by
    specialize h 2 2
    have h1 : f (2 + 2) = f 2 * f 2 := by simpa using h
    rw [show (2 + 2 : ℝ) = 4 by norm_num] at h1
    rw [f2] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f5 : f (5 : ℝ) = 243 := by
    specialize h 4 1
    have h1 : f (4 + 1) = f 4 * f 1 := by simpa using h
    rw [show (4 + 1 : ℝ) = 5 by norm_num] at h1
    rw [f4, hf] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f6 : f (6 : ℝ) = 729 := by
    specialize h 3 3
    have h1 : f (3 + 3) = f 3 * f 3 := by simpa using h
    rw [show (3 + 3 : ℝ) = 6 by norm_num] at h1
    rw [f3] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f7 : f (7 : ℝ) = 2187 := by
    specialize h 6 1
    have h1 : f (6 + 1) = f 6 * f 1 := by simpa using h
    rw [show (6 + 1 : ℝ) = 7 by norm_num] at h1
    rw [f6, hf] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have f8 : f (8 : ℝ) = 6561 := by
    specialize h 4 4
    have h1 : f (4 + 4) = f 4 * f 4 := by simpa using h
    rw [show (4 + 4 : ℝ) = 8 by norm_num] at h1
    rw [f4] at h1
    norm_num at h1 ⊢
    all_goals linarith

  have eq1 : (f 1 ^ 2 + f 2) / f 1 = 6 := by
    rw [show f 1 = 3 by linarith [hf], show f 2 = 9 by linarith [f2]]
    norm_num

  have eq2 : (f 2 ^ 2 + f 4) / f 3 = 6 := by
    rw [show f 2 = 9 by linarith [f2], show f 4 = 81 by linarith [f4], show f 3 = 27 by linarith [f3]]
    norm_num

  have eq3 : (f 3 ^ 2 + f 6) / f 5 = 6 := by
    rw [show f 3 = 27 by linarith [f3], show f 6 = 729 by linarith [f6], show f 5 = 243 by linarith [f5]]
    norm_num

  have eq4 : (f 4 ^ 2 + f 8) / f 7 = 6 := by
    rw [show f 4 = 81 by linarith [f4], show f 8 = 6561 by linarith [f8], show f 7 = 2187 by linarith [f7]]
    norm_num

  rw [eq1, eq2, eq3, eq4]
  norm_num