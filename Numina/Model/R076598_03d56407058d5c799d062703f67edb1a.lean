import Mathlib

theorem algebra_193065 (θ : ℝ) (k : ℝ) (h : k = (3 * Real.sin θ + 5 * Real.cos θ) / (2 * Real.sin θ + Real.cos θ)) (h' : Real.tan θ = 3) : k = 2 := by

  have htan : Real.tan θ = Real.sin θ / Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at h'

  have h1 : Real.cos θ ≠ 0 := by
    by_contra h2
    rw [h2] at h'
    norm_num at h'

  have eq1 : Real.sin θ = 3 * Real.cos θ := by
    field_simp [h1] at h'
    -- Then to Real.sin θ * Real.sin θ + Real.cos θ ^ 2 = 1
    linarith

    -- that's expressed in tan θ = 3.
    -- Real.sin θ = 3 Real.cos θ.

    -- Real.sin θ ^ 2 = 9 * Real.cos θ ^ 2
  -- Real.sin θ ^ 2 * Real.cos θ  = 1.

  have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ

  have h3 : Real.sin θ ^ 2 = 9 * Real.cos θ ^ 2 := by 
    rw [eq1]
    nlinarith

  have h4 : Real.cos θ ^ 2 = 1 / 10 := by 
    nlinarith [h2, h3]

  -- Since Real.sin θ = 3 Real.cos θ.
  -- Compute numerator and denominator

  have h6 : 3 * Real.sin θ + 5 * Real.cos θ = 14 * Real.cos θ := by 
    rw [show Real.sin θ = 3 * Real.cos θ by linarith [eq1]]
    nlinarith

  have h7 : 2 * Real.sin θ + Real.cos θ = 7 * Real.cos θ := by
    rw [show Real.sin θ = 3 * Real.cos θ by linarith [eq1]]
    nlinarith

  rw [h, h6, h7]

  have h8 : Real.cos θ ≠ 0 := h1

  field_simp [show Real.cos θ ≠ 0 by exact h1]
  <;> nlinarith