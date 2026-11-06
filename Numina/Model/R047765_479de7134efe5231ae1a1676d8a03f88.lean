import Mathlib

open Real


theorem algebra_206738 (α β γ : ℝ) (h₀ : Real.sin α + Real.sin β + Real.sin γ = 0)
    (h₁ : Real.cos α + Real.cos β + Real.cos γ = 0) :
    Real.tan (3 * α) = Real.tan (3 * β) ∧ Real.tan (3 * β) = Real.tan (3 * γ) := by

  have h2 : Real.sin γ = - Real.sin α - Real.sin β := by linarith
  have h3 : Real.cos γ = - Real.cos α - Real.cos β := by linarith

  have h5 : Real.cos (α - β) = -1 / 2 := by
    have h4 : Real.sin γ ^ 2 + Real.cos γ ^ 2 = 1 := Real.sin_sq_add_cos_sq γ
    rw [h2, h3] at h4
    have h7 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h8 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    have h9 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
      rw [Real.cos_sub]
    nlinarith [h9]

  have h10 : Real.sin (3 * α - 3 * β) = 0 := by
    have h13 : 3 * α - 3 * β = 3 * (α - β) := by ring
    rw [h13]
    have h14 : Real.sin (3 * (α - β)) = 0 := by
      have h15 : Real.sin (3 * (α - β)) = 3 * Real.sin (α - β) - 4 * Real.sin (α - β) ^ 3 := by
        rw [Real.sin_three_mul]
      have h19 : Real.sin (α - β) ^ 2 = 3 / 4 := by
        have h20 : Real.cos (α - β) ^ 2 + Real.sin (α - β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (α - β)
        rw [h5] at h20
        nlinarith
      rw [h15]
      have h20 : 3 - 4 * Real.sin (α - β) ^ 2 = 0 := by
        nlinarith
      have h21 : 3 * Real.sin (α - β) - 4 * Real.sin (α - β) ^ 3 = Real.sin (α - β) * (3 - 4 * Real.sin (α - β) ^ 2) := by
        ring
      rw [h21, h20]
      norm_num
    exact h14

  have h11 : Real.tan (3 * α) = Real.tan (3 * β) := by
    by_cases h15 : Real.cos (3 * α) = 0
    · -- When cos(3α) = 0, show cos(3β) = 0, so tan(3α) = tan(3β) (both undefined)
      have h16 : Real.cos (3 * β) = 0 := by
        by_contra h17
        have h17' : Real.cos (3 * β) ≠ 0 := by intro h18; apply h17; all_goals linarith
        have h18 : Real.sin (3 * α) * Real.cos (3 * β) = Real.cos (3 * α) * Real.sin (3 * β) := by
          have h12 : Real.sin (3 * α - 3 * β) = 0 := h10
          have h14 : Real.sin (3 * α - 3 * β) = Real.sin (3 * α) * Real.cos (3 * β) - Real.cos (3 * α) * Real.sin (3 * β) := by
            rw [Real.sin_sub]
          linarith [h12, h14]
        have h19 : Real.sin (3 * α) * Real.cos (3 * β) = 0 := by
          rw [h15] at h18
          nlinarith
        have h20 : Real.sin (3 * α) = 0 := by
          apply (mul_left_inj' (show Real.cos (3 * β) ≠ 0 by exact h17')).mp
          linarith
        have h21 : Real.sin (3 * α) ^ 2 + Real.cos (3 * α) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * α)
        rw [h20, h15] at h21
        nlinarith
      -- When cos(3α) = 0 and cos(3β) = 0, tan(3α) = tan(3β) (both undefined)
      have h17 : Real.tan (3 * α) = Real.tan (3 * β) := by
        rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
        simp [h15, h16]
      exact h17
    · -- When cos(3α) ≠ 0, show tan(3α) = tan(3β)
      by_cases h18 : Real.cos (3 * β) = 0
      · -- When cos(3β) = 0, show cos(3α) = 0
        have h19 : Real.cos (3 * α) = 0 := by
          by_contra h20
          have h20' : Real.cos (3 * α) ≠ 0 := by intro h21; apply h20; all_goals linarith
          have h21 : Real.sin (3 * α) * Real.cos (3 * β) = Real.cos (3 * α) * Real.sin (3 * β) := by
            have h12 : Real.sin (3 * α - 3 * β) = 0 := h10
            have h14 : Real.sin (3 * α - 3 * β) = Real.sin (3 * α) * Real.cos (3 * β) - Real.cos (3 * α) * Real.sin (3 * β) := by
              rw [Real.sin_sub]
            linarith [h12, h14]
          have  h22 : Real.sin (3 * β) * Real.cos (3 * α) = 0 := by
            rw [h18] at h21
            nlinarith
          have h23 : Real.sin (3 * β) = 0 := by
            apply (mul_left_inj' (show Real.cos (3 * α) ≠ 0 by exact h20')).mp
            linarith
          have h24 : Real.sin (3 * β) ^ 2 + Real.cos (3 * β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * β)
          rw [h23, h18] at h24
          nlinarith
        exfalso
        tauto
      · -- When cos(3α) ≠ 0 and cos(3β) ≠ 0, show tan(3α) = tan(3β)
        have h17 : Real.sin (3 * α) * Real.cos (3 * β) = Real.cos (3 * α) * Real.sin (3 * β) := by
          have h12 : Real.sin (3 * α - 3 * β) = 0 := h10
          have h14 : Real.sin (3 * α - 3 * β) = Real.sin (3 * α) * Real.cos (3 * β) - Real.cos (3 * α) * Real.sin (3 * β) := by
            rw [Real.sin_sub]
          linarith [h12, h14]
        have h19 : Real.tan (3 * α) = Real.tan (3 * β) := by
          rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
          have h20 : Real.cos (3 * α) ≠ 0 := h15
          have h21 : Real.cos (3 * β) ≠ 0 := h18
          field_simp [h20, h21]
          all_goals linarith
        exact h19

  have h12 : Real.tan (3 * β) = Real.tan (3 * γ) := by

    have h10' : Real.sin (3 * β - 3 * γ) = 0 := by
      have h13 : 3 * β - 3 * γ = 3 * (β - γ) := by ring
      rw [h13]
      have h14 : Real.sin (3 * (β - γ)) = 0 := by
        have h15 : Real.sin (3 * (β - γ)) = 3 * Real.sin (β - γ) - 4 * Real.sin (β - γ) ^ 3 := by
          rw [Real.sin_three_mul]
        have h19 : Real.sin (β - γ) ^ 2 = 3 / 4 := by
          have h10 : Real.cos (β - γ) = -1 / 2 := by
            have h7 : Real.sin γ = - Real.sin α - Real.sin β := by linarith
            have h8 : Real.cos γ = - Real.cos α - Real.cos β := by linarith
            have h9 : Real.cos (β - γ) = Real.cos β * Real.cos γ + Real.sin β * Real.sin γ := by
              rw [Real.cos_sub]
            rw [h9, h8, h7]
            have h10 : Real.cos (α - β) = -1 / 2 := h5
            have h11 : Real.cos α * Real.cos β + Real.sin α * Real.sin β = -1 / 2 := by
              have h12 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
                rw [Real.cos_sub]
              linarith [h10, h12]
            nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ]
          have h20 : Real.cos (β - γ) ^ 2 + Real.sin (β - γ) ^ 2 = 1 := Real.cos_sq_add_sin_sq (β - γ)
          rw [h10] at h20
          nlinarith
        rw [h15]
        have h20 : 3 - 4 * Real.sin (β - γ) ^ 2 = 0 := by
          nlinarith
        have h21 : 3 * Real.sin (β - γ) - 4 * Real.sin (β - γ) ^ 3 = Real.sin (β - γ) * (3 - 4 * Real.sin (β - γ) ^ 2) := by
          ring
        rw [h21, h20]
        norm_num
      exact h14

    by_cases h15 : Real.cos (3 * β) = 0
    · -- When cos(3β) = 0, show cos(3γ) = 0, so tan(3β) = tan(3γ) (both undefined)
      have h16 : Real.cos (3 * γ) = 0 := by
        by_contra h17
        have h17' : Real.cos (3 * γ) ≠ 0 := by intro h18; apply h17; all_goals linarith
        have h18 : Real.sin (3 * β) * Real.cos (3 * γ) = Real.cos (3 * β) * Real.sin (3 * γ) := by
          have h12 : Real.sin (3 * β - 3 * γ) = 0 := h10'
          have h14 : Real.sin (3 * β - 3 * γ) = Real.sin (3 * β) * Real.cos (3 * γ) - Real.cos (3 * β) * Real.sin (3 * γ) := by
            rw [Real.sin_sub]
          linarith [h12, h14]
        have h19 : Real.sin (3 * β) * Real.cos (3 * γ) = 0 := by
          rw [h15] at h18
          nlinarith
        have h20 : Real.sin (3 * β) = 0 := by
          apply (mul_left_inj' (show Real.cos (3 * γ) ≠ 0 by exact h17')).mp
          linarith
        have h21 : Real.sin (3 * β) ^ 2 + Real.cos (3 * β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * β)
        rw [h20, h15] at h21
        nlinarith
      -- When cos(3β) = 0 and cos(3γ) = 0, tan(3β) = tan(3γ) (both undefined)
      have h17 : Real.tan (3 * β) = Real.tan (3 * γ) := by
        rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
        simp [h15, h16]
      exact h17
    · -- When cos(3β) ≠ 0, show tan(3β) = tan(3γ)
      by_cases h18 : Real.cos (3 * γ) = 0
      · -- When cos(3γ) = 0, show cos(3β) = 0
        have h19 : Real.cos (3 * β) = 0 := by
          by_contra h20
          have h20' : Real.cos (3 * β) ≠ 0 := by intro h21; apply h20; all_goals linarith
          have h21 : Real.sin (3 * β) * Real.cos (3 * γ) = Real.cos (3 * β) * Real.sin (3 * γ) := by
            have h12 : Real.sin (3 * β - 3 * γ) = 0 := h10'
            have h14 : Real.sin (3 * β - 3 * γ) = Real.sin (3 * β) * Real.cos (3 * γ) - Real.cos (3 * β) * Real.sin (3 * γ) := by
              rw [Real.sin_sub]
            linarith [h12, h14]
          have  h22 : Real.sin (3 * γ) * Real.cos (3 * β) = 0 := by
            rw [h18] at h21
            nlinarith
          have h23 : Real.sin (3 * γ) = 0 := by
            apply (mul_left_inj' (show Real.cos (3 * β) ≠ 0 by exact h20')).mp
            linarith
          have h24 : Real.sin (3 * γ) ^ 2 + Real.cos (3 * γ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * γ)
          rw [h23, h18] at h24
          nlinarith
        exfalso
        tauto
      · -- When cos(3β) ≠ 0 and cos(3γ) ≠ 0, show tan(3β) = tan(3γ)
        have h17 : Real.sin (3 * β) * Real.cos (3 * γ) = Real.cos (3 * β) * Real.sin (3 * γ) := by
          have h12 : Real.sin (3 * β - 3 * γ) = 0 := h10'
          have h14 : Real.sin (3 * β - 3 * γ) = Real.sin (3 * β) * Real.cos (3 * γ) - Real.cos (3 * β) * Real.sin (3 * γ) := by
            rw [Real.sin_sub]
          linarith [h12, h14]
        have h19 : Real.tan (3 * β) = Real.tan (3 * γ) := by
          rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
          have h20 : Real.cos (3 * β) ≠ 0 := h15
          have h21 : Real.cos (3 * γ) ≠ 0 := h18
          field_simp [h20, h21]
          all_goals linarith
        exact h19

  constructor
  · exact h11
  · exact h12