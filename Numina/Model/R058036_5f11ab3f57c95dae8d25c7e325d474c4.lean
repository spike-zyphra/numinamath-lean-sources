import Mathlib

theorem algebra_8859
    {f : ℝ → ℝ}
    (hf : ∃ x, f x ≠ 0)
    (h : ∀ a b, f (a * b) = a * f b + b * f a)
    (he : f (Real.exp 1) = Real.exp 1) :
    f (-1) + f (-1 / Real.exp 1) = 1 / Real.exp 1 := by
  have h0 : f 0 = 0 := by
    specialize h 0 0
    norm_num at h
    exact h

  have h1 : f 1 = 0 := by
    specialize h 1 1
    norm_num at h
    linarith

  have h2 : f (1 / Real.exp 1) = -1 / Real.exp 1 := by
    have eq1 := h (Real.exp 1) (1 / Real.exp 1)
    have eq2 : (Real.exp 1 * (1 / Real.exp 1 : ℝ)) = (1 : ℝ) := by
      field_simp
    have eq3 : f (Real.exp 1 * (1 / Real.exp 1 : ℝ)) = f 1 := by
      rw [eq2]
    rw [eq3] at eq1
    rw [he] at eq1
    field_simp at eq1 ⊢
    linarith [h1]

  have h3 : f (-1) = 0 := by
    specialize h (-1) (-1)
    have eq1 : f ((-1 : ℝ) * (-1 : ℝ)) = f 1 := by
      norm_num
    rw [eq1] at h
    rw [h1] at h
    norm_num at h
    linarith

  have h4 : f (-1 / Real.exp 1) = 1 / Real.exp 1 := by
    have eq1 := h (Real.exp 1) (-1 / Real.exp 1)
    have eq2 : Real.exp 1 * (-1 / Real.exp 1) = (-1 : ℝ) := by
      field_simp
    have eq3 : f (Real.exp 1 * (-1 / Real.exp 1)) = f (-1) := by
      rw [eq2]
    rw [eq3] at eq1
    rw [h3, he] at eq1
    field_simp at eq1 ⊢
    linarith

  rw [h3, h4]
  all_goals norm_num
  all_goals field_simp at *
  all_goals linarith