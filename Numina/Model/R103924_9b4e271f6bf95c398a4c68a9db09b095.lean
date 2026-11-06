import Mathlib

theorem algebra_12171 (x : ℝ) (h : Real.sin x + Real.cos x = Real.sqrt 2 / 2) :
    (Real.sin x)^3 + (Real.cos x)^3 = 5 * Real.sqrt 2 / 8 := by
  have h1 : Real.sin x + Real.cos x = Real.sqrt 2 / 2 := h
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : Real.sin x * Real.cos x = -1 / 4 := by
    have eq1 : (Real.sin x + Real.cos x) ^ 2 = 1 / 2 := by
      rw [h1]
      have h4 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        calc
          (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
          _ = (2) / 4 := by rw [Real.sq_sqrt]; linarith [show (0 : ℝ) ≤ 2 by norm_num]
          _ = 1 / 2 := by norm_num
      linarith
    have eq2 : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by ring
    rw [eq2] at eq1
    rw [h2] at eq1
    linarith
  have h5 : (Real.sin x)^3 + (Real.cos x)^3 = (Real.sin x + Real.cos x) * ((Real.sin x)^2 + (Real.cos x)^2 - Real.sin x * Real.cos x) := by
    ring
  rw [h5, h1, h2, h3]
  ring