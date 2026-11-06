import Mathlib

theorem algebra_162351 (α : ℝ) :
    (Real.cos α)^8 - (Real.sin α)^8 =
    Real.cos (2 * α) * (3 + Real.cos (4 * α)) / 4 := by
  have h1 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]

  have h2 : Real.cos (4 * α) = 2 * Real.cos (2 * α) ^ 2 - 1 := by
    have h3 : Real.cos (4 * α) = 2 * Real.cos (2 * α) ^ 2 - 1 := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [Real.cos_two_mul]
    linarith

  have h3 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith

  have h4 : (Real.cos α) ^ 4 + (Real.sin α) ^ 4 = (3 + Real.cos (4 * α)) / 4 := by
    have h5 : (Real.cos α) ^ 4 + (Real.sin α) ^ 4 = 1 - 2 * (Real.cos α ^ 2 * Real.sin α ^ 2) := by
      have h6 : (Real.cos α) ^ 4 + (Real.sin α) ^ 4 = ((Real.cos α ^ 2 + Real.sin α ^ 2) ^ 2 - 2 * (Real.cos α ^ 2 * Real.sin α ^ 2)) := by
        ring
      have h7 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
      rw [h7] at h6
      nlinarith

    have h8 : Real.cos (4 * α) = 1 - 8 * (Real.cos α ^ 2 * Real.sin α ^ 2) := by
      have h9 : Real.cos (4 * α) = 1 - 8 * (Real.cos α ^ 2 * Real.sin α ^ 2) := by
        have h10 : Real.cos (4 * α) = 2 * Real.cos (2 * α) ^ 2 - 1 := by
          have h3 : Real.cos (4 * α) = 2 * Real.cos (2 * α) ^ 2 - 1 := by
            rw [show 4 * α = 2 * (2 * α) by ring]
            rw [Real.cos_two_mul]
          linarith
        rw [h10]
        have h11 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
          rw [Real.cos_two_mul]
        rw [h11]
        have h12 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
          have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
          linarith
        nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.cos α ^ 2 - 1 / 2)]

      linarith

    nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.cos α ^ 2 - 1 / 2)]

  have h5 : (Real.cos α) ^ 8 - (Real.sin α) ^ 8 = Real.cos (2 * α) * ((Real.cos α) ^ 4 + (Real.sin α) ^ 4) := by
    have h6 : (Real.cos α) ^ 8 - (Real.sin α) ^ 8 = ((Real.cos α) ^ 4 - (Real.sin α) ^ 4) * ((Real.cos α) ^ 4 + (Real.sin α) ^ 4) := by
      ring
    rw [h6]
    have h7 : (Real.cos α) ^ 4 - (Real.sin α) ^ 4 = Real.cos (2 * α) := by
      have h8 : (Real.cos α) ^ 4 - (Real.sin α) ^ 4 = ((Real.cos α ^ 2 - Real.sin α ^ 2) * (Real.cos α ^ 2 + Real.sin α ^ 2)) := by
        ring
      rw [h8]
      have h9 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
      have h10 : Real.cos α ^ 2 - Real.sin α ^ 2 = Real.cos (2 * α) := by
        have h11 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
          rw [Real.cos_two_mul]
        nlinarith [h11, Real.sin_sq_add_cos_sq α]
      nlinarith [h9, h10]

    nlinarith [Real.sin_sq_add_cos_sq α, Real.cos_sq_add_sin_sq α]

  rw [h5, h4]
  all_goals
    nlinarith [Real.sin_sq_add_cos_sq α, Real.cos_sq_add_sin_sq α, sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.cos α ^ 2 - 1 / 2)]