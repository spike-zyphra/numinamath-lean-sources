import Mathlib

theorem algebra_164967 (α : ℝ) (h₀ : 2 * Real.tan α ^ 2 - 7 * Real.tan α + 3 = 0)
    (h₁ : Real.pi < α ∧ α < 5 * Real.pi / 4 ∨ 5 * Real.pi / 4 < α ∧ α < 3 * Real.pi / 2) :
    Real.sin (2 * α) = 4 / 5 ∨ Real.sin (2 * α) = 3 / 5 := by

  have h2 : (Real.tan α - 3) * (Real.tan α - 1 / 2) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp h2) with h3 h4
  
  · -- Case $\tan \alpha = 3$
    have htan : Real.tan α = 3 := by linarith

    have h5 : Real.sin α ≠ 0 := by
      by_contra h
      have htan' : Real.tan α = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      rw [htan'] at htan
      linarith

    have h6 : Real.cos α ≠ 0 := by
      by_contra h
      have htan' : Real.tan α = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      rw [htan'] at htan
      linarith

    have h7 : Real.sin (2 * α) = 3 / 5 := by
      have h7 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
        rw [Real.sin_two_mul]
      have h9 : Real.sin α = 3 * Real.cos α := by
        have htan' : Real.tan α = Real.sin α / Real.cos α := by
          rw [Real.tan_eq_sin_div_cos]
        rw [htan'] at htan
        have hcosn : Real.cos α ≠ 0 := h6
        field_simp [hcosn] at htan ⊢
        linarith

      have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [show Real.sin α = 3 * Real.cos α by linarith [h9]] at h10
      have h11 : Real.cos α ^ 2 = 1 / 10 := by
        nlinarith

      rw [h7]
      have h12 : 2 * Real.sin α * Real.cos α = 3 / 5 := by
        rw [show Real.sin α = 3 * Real.cos α by linarith [h9]]
        nlinarith [h11]
      linarith

    right
    linarith

  · -- Case $\tan \alpha = 1/2$
    have htan : Real.tan α = 1 / 2 := by linarith

    have h5 : Real.sin α ≠ 0 := by
      by_contra h
      have htan' : Real.tan α = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      rw [htan'] at htan
      linarith

    have h6 : Real.cos α ≠ 0 := by
      by_contra h
      have htan' : Real.tan α = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      rw [htan'] at htan
      linarith

    have h7 : Real.sin (2 * α) = 4 / 5 := by
      have h7 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
        rw [Real.sin_two_mul]
      have h9 : Real.sin α = 1 / 2 * Real.cos α := by
        have htan' : Real.tan α = Real.sin α / Real.cos α := by
          rw [Real.tan_eq_sin_div_cos]
        rw [htan'] at htan
        have hcosn : Real.cos α ≠ 0 := h6
        field_simp [hcosn] at htan ⊢
        nlinarith

      have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [show Real.sin α = 1 / 2 * Real.cos α by linarith [h9]] at h10
      have h11 : Real.cos α ^ 2 = 4 / 5 := by
        nlinarith

      rw [h7]
      have h12 : 2 * Real.sin α * Real.cos α = 4 / 5 := by
        rw [show Real.sin α = 1 / 2 * Real.cos α by linarith [h9]]
        nlinarith [h11]
      linarith

    left
    linarith