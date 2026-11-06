import Mathlib

theorem calculus_14838 (x : ℝ) (h : Real.cos x - 4 * Real.sin x = 1) :
  Real.sin x + 4 * Real.cos x = -4 ∨ Real.sin x + 4 * Real.cos x = 4 := by 
  have h1 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have h2 : Real.cos x = 1 + 4 * Real.sin x := by 
    linarith [h]
  rw [h2] at h1
  have h3 : Real.sin x * (8 + 17 * Real.sin x) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- If $\sin x = 0$
    have h4' : Real.sin x = 0 := h4
    have h5' : Real.cos x = 1 := by 
      nlinarith [h4', h2]
    right
    rw [h4', h5']
    all_goals norm_num
  · -- If $8 + 17 \sin x = 0$
    have h4' : Real.sin x = -8 / 17 := by 
      linarith 
    have h5' : Real.cos x = -15 / 17 := by 
      nlinarith [h4', h2]
    left
    rw [h4', h5']
    all_goals norm_num