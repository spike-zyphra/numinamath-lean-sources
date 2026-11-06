import Mathlib

theorem algebra_97375 (a : ℕ → ℝ) (ha : a 0 ≠ 0) (h : ∀ n, a (n + 2) = a n * a (n + 1))
    (h1 : a 7 = 1024) (h2 : a 6 = 64) (h3 : a 5 = 16) :
    a 0 = 1 / 4 := by
  have eq1 : a 7 = a 5 * a 6 := by 
    specialize h 5
    norm_num at h ⊢
    linarith [h]
  rw [h1, h2, h3] at eq1
  -- verify that 1024 = 16 * 64, which is true
  have h4 : a 4 = 4 := by 
    have eq2 : a 6 = a 4 * a 5 := by 
      specialize h 4
      norm_num at h ⊢
      linarith [h]
    rw [h2, h3] at eq2 
    -- solve 64 = a 4 * 16 to get a 4 = 4
    nlinarith
  have h5 : a 3 = 4 := by 
    have eq3 : a 5 = a 3 * a 4 := by 
      specialize h 3
      norm_num at h ⊢
      linarith [h]
    rw [h3, h4] at eq3 
    -- solve 16 = a 3 * 4 to get a 3 = 4
    nlinarith
  have h6 : a 2 = 1 := by 
    have eq4 : a 4 = a 2 * a 3 := by 
      specialize h 2
      norm_num at h ⊢
      linarith [h]
    rw [h4, h5] at eq4 
    -- solve 4 = a 2 * 4 to get a 2 = 1
    nlinarith
  have h7 : a 1 = 4 := by 
    have eq5 : a 3 = a 1 * a 2 := by 
      specialize h 1
      norm_num at h ⊢
      linarith [h]
    rw [h5, h6] at eq5 
    -- solve 4 = a 1 * 1 to get a 1 = 4
    nlinarith
  have eq6 : a 2 = a 0 * a 1 := by 
    specialize h 0
    norm_num at h ⊢
    linarith [h]
  rw [h6, h7] at eq6 
  -- solve 1 = a 0 * 4 to get a 0 = 1 / 4
  nlinarith