import Mathlib

theorem algebra_319434 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = f x + f y + 6 * x * y)
    (h' : f (-1) * f 1 ≥ 9) : f (2 / 3) = 4 / 3 := by
  have f0 : f 0 = 0 := by 
    specialize h 0 0
    norm_num at h
    linarith
  have eq1 : f 1 + f (-1) = 6 := by
    specialize h 1 (-1)
    norm_num [f0] at h 
    linarith
  have eq2 : f 1 = 3 := by 
    have h1 : f (-1) = 6 - f 1 := by linarith [eq1]
    rw [h1] at h'
    have h2 : (6 - f 1) * f 1 ≥ 9 := by linarith [h']
    have h3 : (f 1 - 3) ^ 2 ≤ 0 := by
      nlinarith 
    have h4 : (f 1 - 3) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (f 1 - 3)]
    have h5 : f 1 - 3 = 0 := by 
      nlinarith 
    linarith
  have eq3 : f (-1) = 3 := by 
    linarith [eq1, eq2]
  have eq4 : f 1 = f (2 / 3) + f (1 / 3) + 4 / 3 := by
    specialize h (2 / 3) (1 / 3)
    rw [show (2 / 3 : ℝ) + (1 / 3 : ℝ) = 1 by norm_num] at h 
    linarith
  have eq5 : f (2 / 3) + f (1 / 3) = 5 / 3 := by
    nlinarith [eq2, eq4]
  have eq6 : f (1 / 3) + f (-1 / 3) = 2 / 3 := by 
    specialize h (1 / 3) (-1 / 3)
    have eq8 : (1 / 3 : ℝ) + (-1 / 3 : ℝ) = (0 : ℝ) := by norm_num
    rw [eq8] at h 
    simp [f0] at h 
    linarith [h]
  have eq7 : f (1 / 3) = f (2 / 3) + f (-1 / 3) - 4 / 3 := by 
    specialize h (2 / 3) (-1 / 3)
    have eq8 : (2 / 3 : ℝ) + (-1 / 3 : ℝ) = (1 / 3 : ℝ) := by norm_num
    rw [eq8] at h 
    linarith [h]
  have eq8 : f (1 / 3) = 1 / 3 := by
    have eq9 : f (-1 / 3) = 2 / 3 - f (1 / 3) := by
      linarith [eq6]
    rw [eq9] at eq7
    linarith [eq7, eq5]
  have eq9 : f (2 / 3) = 4 / 3 := by
    linarith [eq5, eq8]
  exact eq9