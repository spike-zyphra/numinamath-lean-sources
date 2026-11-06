import Mathlib

theorem algebra_314807 {f : ℕ → ℝ} (h : ∀ m n, f (m + n) = f m * f n) (h1 : f 1 = 3) :
    (f 1 ^ 2 + f (2 * 1)) / f (2 * 1 - 1) + (f 2 ^ 2 + f (2 * 2)) / f (2 * 2 - 1) +
    (f 3 ^ 2 + f (2 * 3)) / f (2 * 3 - 1) + (f 4 ^ 2 + f (2 * 4)) / f (2 * 4 - 1) = 24 := by

  have f2 : f 2 = 9 := by
    specialize h 1 1
    norm_num at h
    rw [h1] at h
    linarith

  have f3 : f 3 = 27 := by
    specialize h 2 1
    norm_num at h
    rw [f2, h1] at h
    linarith

  have f4 : f 4 = 81 := by
    specialize h 3 1
    norm_num at h
    rw [f3, h1] at h
    linarith

  have f5 : f 5 = 243 := by
    specialize h 4 1
    norm_num at h
    rw [f4, h1] at h
    linarith

  have f6 : f 6 = 729 := by
    specialize h 3 3
    norm_num at h
    rw [f3] at h
    linarith

  have f7 : f 7 = 2187 := by
    specialize h 6 1
    norm_num at h
    rw [f6, h1] at h
    linarith

  have f8 : f 8 = 6561 := by
    specialize h 4 4
    norm_num at h
    rw [f4] at h
    linarith

  have term1 : (f 1 ^ 2 + f (2 * 1)) / f (2 * 1 - 1) = 6 := by
    norm_num [h1, f2]
    <;> linarith

  have term2 : (f 2 ^ 2 + f (2 * 2)) / f (2 * 2 - 1) = 6 := by
    norm_num [f2, f4, f3]
    <;> linarith

  have term3 : (f 3 ^ 2 + f (2 * 3)) / f (2 * 3 - 1) = 6 := by
    norm_num [f3, f6, f5]
    <;> linarith

  have term4 : (f 4 ^ 2 + f (2 * 4)) / f (2 * 4 - 1) = 6 := by
    norm_num [f4, f8, f7]
    <;> linarith

  linarith [term1, term2, term3, term4]