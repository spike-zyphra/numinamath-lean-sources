import Mathlib

theorem calculus_23294 (x : Real) (h : Real.cos x + Real.cos (2 * x) + Real.cos (3 * x) = 3) :
    Real.sin x + Real.sin (2 * x) + Real.sin (3 * x) = 0 := by
  have h1 : Real.cos x ≤ 1 := by
    apply Real.cos_le_one
  have h1' : Real.cos (2 * x) ≤ 1 := by
    apply Real.cos_le_one
  have h1'' : Real.cos (3 * x) ≤ 1 := by
    apply Real.cos_le_one
  have h4 : Real.cos x = 1 ∧ Real.cos (2 * x) = 1 ∧ Real.cos (3 * x) = 1 := by
    constructor
    · -- First prove cos x = 1
      linarith [h, h1, h1', h1'']
    constructor
    · -- Then prove cos 2x = 1
      linarith [h, h1, h1', h1'']
    · -- Then prove cos 3x = 1
      linarith [h, h1, h1', h1'']
  have cosx1 : Real.cos x = 1 := h4.1
  have cos2x1 : Real.cos (2 * x) = 1 := h4.2.1
  have cos3x1 : Real.cos (3 * x) = 1 := h4.2.2
  have hsinx0 : Real.sin x = 0 := by
    have h : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [cosx1] at h
    have h2 : Real.sin x ^ 2 = 0 := by nlinarith
    have h3 : Real.sin x = 0 := by nlinarith
    exact h3
  have hsin2x0 : Real.sin (2 * x) = 0 := by
    have h : Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * x)
    rw [cos2x1] at h
    have h2 : Real.sin (2 * x) ^ 2 = 0 := by nlinarith
    have h3 : Real.sin (2 * x) = 0 := by nlinarith
    exact h3
  have hsin3x0 : Real.sin (3 * x) = 0 := by
    have h : Real.sin (3 * x) ^ 2 + Real.cos (3 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * x)
    rw [cos3x1] at h
    have h2 : Real.sin (3 * x) ^ 2 = 0 := by nlinarith
    have h3 : Real.sin (3 * x) = 0 := by nlinarith
    exact h3
  rw [hsinx0, hsin2x0, hsin3x0]
  all_goals norm_num
  all_goals nlinarith