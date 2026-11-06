import Mathlib

theorem algebra_9214 (α : ℝ) (h : Real.sin α ≠ 0) (h1 : 5 * (Real.sin α)^2 - 7 * Real.sin α - 6 = 0) :
    (Real.sin (-α - 3 * Real.pi / 2)) * (Real.sin (3 * Real.pi / 2 - α)) * (Real.tan (2 * Real.pi - α))^2 /
    ((Real.cos (Real.pi / 2 - α)) * (Real.cos (Real.pi / 2 + α)) * (Real.cos (Real.pi - α))^2) = 25 / 16 := by
  have h2 : Real.sin α = -3 / 5 := by 
    have h3 : 5 * (Real.sin α) ^ 2 - 7 * Real.sin α - 6 = 0 := by linarith
    have h4 : (Real.sin α - 2) * (Real.sin α + 3 / 5) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- Real.sin α - 2 = 0 
      have h7 : Real.sin α = 2 := by linarith 
      have h8 : Real.sin α ≤ 1 := by 
        apply Real.sin_le_one 
      nlinarith 
    · -- Real.sin α + 3 / 5 = 0 
      linarith 
  have h3 : Real.cos α ^ 2 = 16 / 25 := by
    have h6 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
    rw [h2] at h6 
    nlinarith 
  have h4 : Real.sin (-α - 3 * Real.pi / 2) = Real.cos α := by
    have h7 : Real.sin (-α - 3 * Real.pi / 2) = Real.sin (- (α + 3 * Real.pi / 2)) := by 
      ring_nf 
    rw [h7]
    have h8 : Real.sin (- (α + 3 * Real.pi / 2)) = - Real.sin (α + 3 * Real.pi / 2) := by
      rw [Real.sin_neg] 
    rw [h8]
    have h9 : Real.sin (α + 3 * Real.pi / 2) = - Real.cos α := by 
      have h10 : Real.sin (α + 3 * Real.pi / 2) = Real.sin α * Real.cos (3 * Real.pi / 2) + Real.cos α * Real.sin (3 * Real.pi / 2) := by 
        rw [Real.sin_add] 
      rw [h10]
      have h11 : Real.cos (3 * Real.pi / 2) = (0 : ℝ) := by 
        have h12 : Real.cos (3 * Real.pi / 2) = 0 := by
          have h13 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by 
            ring_nf 
          rw [h13]
          rw [Real.cos_add]
          norm_num [Real.cos_pi, Real.sin_pi]
        linarith 
      have h12 : Real.sin (3 * Real.pi / 2) = (-1 : ℝ) := by 
        have h13 : Real.sin (3 * Real.pi / 2) = -1 := by
          have h14 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by 
            ring_nf 
          rw [h14]
          rw [Real.sin_add]
          norm_num [Real.cos_pi, Real.sin_pi]
        linarith 
      rw [h11, h12]
      nlinarith 
    rw [h9]
    all_goals linarith 
  have h5 : Real.sin (3 * Real.pi / 2 - α) = - Real.cos α := by
    have h13 : Real.sin (3 * Real.pi / 2 - α) = Real.sin (3 * Real.pi / 2) * Real.cos α - Real.cos (3 * Real.pi / 2) * Real.sin α := by 
      rw [Real.sin_sub] 
    rw [h13]
    have h14 : Real.sin (3 * Real.pi / 2) = (-1 : ℝ) := by
      have h15 : Real.sin (3 * Real.pi / 2) = -1 := by 
        have h16 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by 
          ring_nf 
        rw [h16]
        rw [Real.sin_add]
        norm_num [Real.cos_pi, Real.sin_pi]
      linarith 
    have h15 : Real.cos (3 * Real.pi / 2) = (0 : ℝ) := by 
      have h16 : Real.cos (3 * Real.pi / 2) = 0 := by 
        have h17 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by 
          ring_nf 
        rw [h17]
        rw [Real.cos_add]
        norm_num [Real.cos_pi, Real.sin_pi]
      linarith 
    rw [h14, h15]
    all_goals nlinarith 
  have h6 : Real.tan (2 * Real.pi - α) = - Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos] 
    have h18 : Real.sin (2 * Real.pi - α) = - Real.sin α := by 
      rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi] 
      ring 
    have h19 : Real.cos (2 * Real.pi - α) = Real.cos α := by 
      rw [Real.cos_sub, Real.sin_two_pi, Real.cos_two_pi] 
      ring 
    rw [h18, h19] 
  have h7 : (Real.sin (-α - 3 * Real.pi / 2)) * (Real.sin (3 * Real.pi / 2 - α)) * (Real.tan (2 * Real.pi - α))^2 = - (Real.sin α) ^ 2 := by 
    rw [h4, h5, h6] 
    have h8 : Real.cos α ≠ 0 := by 
      by_contra h9 
      have h9 : Real.cos α = 0 := by linarith 
      have h9 : Real.cos α ^ 2 = 0 := by 
        nlinarith 
      nlinarith [ Real.sin_sq_add_cos_sq α, h2, h3, h9 ] 
    field_simp [h8]
    nlinarith
  have h8 : (Real.cos (Real.pi / 2 - α)) * (Real.cos (Real.pi / 2 + α)) * (Real.cos (Real.pi - α)) ^ 2 = - (Real.sin α) ^ 2 * (Real.cos α) ^ 2 := by 
    have h11 : Real.cos (Real.pi / 2 - α) = Real.sin α := by 
      rw [Real.cos_pi_div_two_sub] 
    have h12 : Real.cos (Real.pi / 2 + α) = - Real.sin α := by 
      rw [Real.cos_add] 
      norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two] 
    have h13 : Real.cos (Real.pi - α) = - Real.cos α := by 
      rw [Real.cos_pi_sub] 
    rw [h11, h12, h13] 
    all_goals nlinarith 
  rw [h7, h8] 
  have h8 : Real.cos α ≠ 0 := by 
    by_contra h9 
    have h9 : Real.cos α = 0 := by linarith 
    have h9 : Real.cos α ^ 2 = 0 := by 
      nlinarith 
    nlinarith [ Real.sin_sq_add_cos_sq α, h2, h3, h9 ] 
  field_simp [h8, h2, h3, h] 
  <;> nlinarith