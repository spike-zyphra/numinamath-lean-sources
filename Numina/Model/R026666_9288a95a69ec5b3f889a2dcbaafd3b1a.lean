import Mathlib

theorem algebra_227149 (f : ℝ → ℝ) (h : ∀ x1 x2, 0 < x1 → 0 < x2 → f (x1 * x2) = f x1 + f x2)
    (h8 : f 8 = 3) : f (Real.sqrt 2) = 1 / 2 := by
  have f2_eq1 : f 2 = 1 := by
    have h4 : f 4 = 2 * f 2 := by
      have h2_2 : f (2 * 2) = f (2) + f (2) := h 2 2 (by norm_num) (by norm_num)
      norm_num at h2_2
      linarith
    have h8_eq : f 8 = f 2 + f 4 := by
      have h2_4 : f (2 * 4) = f (2) + f (4) := h 2 4 (by norm_num) (by norm_num)
      norm_num at h2_4
      linarith
    rw [h4] at h8_eq
    rw [h8] at h8_eq
    linarith
  have h2 : f 2 = 1 := f2_eq1
  have hsqrt2 : f (Real.sqrt 2 * Real.sqrt 2) = f (Real.sqrt 2) + f (Real.sqrt 2) := h (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt2prod : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [hsqrt2prod] at hsqrt2
  have eq1 : f (2 : ℝ) = 2 * f (Real.sqrt 2) := by
    linarith
  rw [h2] at eq1
  linarith