import Mathlib

open Real Set

theorem calculus_23060 (α β γ : ℝ) (h₀ : α + β + γ = π)
  (h₁ : tan α * tan β = 1 / sin (π / 3))
  (h₂: cos α ≠ 0) (h₃: cos β ≠ 0) :
  cos α * cos β / cos γ = 2 * sqrt 3 + 3 := by
  have h4 : sin (π / 3) = Real.sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  have h5 : 1 / sin (π / 3) = 2 * Real.sqrt 3 / 3 := by
    rw [h4]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h6 : tan α * tan β = 2 * Real.sqrt 3 / 3 := by
    rw [h5] at h₁
    linarith
  have h7 : sin α * sin β = 2 * Real.sqrt 3 / 3 * (cos α * cos β) := by
    have htan : tan α = sin α / cos α := by rw [tan_eq_sin_div_cos]
    have htan2 : tan β = sin β / cos β := by rw [tan_eq_sin_div_cos]
    rw [htan, htan2] at h6
    field_simp [h₂, h₃] at h6 ⊢
    nlinarith
  have h8 : γ = π - (α + β) := by linarith [h₀]
  have h9 : cos γ = sin α * sin β - cos α * cos β := by
    rw [h8]
    have h10 : cos (π - (α + β)) = - cos (α + β) := by
      rw [cos_pi_sub]
    rw [h10]
    have h11 : cos (α + β) = cos α * cos β - sin α * sin β := by
      rw [cos_add]
    rw [h11]
    all_goals ring
  have h10 : cos α * cos β ≠ 0 := by
    apply mul_ne_zero
    exact h₂
    exact h₃
  have h11 : cos γ ≠ 0 := by
    by_contra h
    rw [h9] at h
    have h12 : sin α * sin β = cos α * cos β := by linarith
    have h13 : sin α * sin β = 2 * Real.sqrt 3 / 3 * (cos α * cos β) := by
      linarith [h7]
    have h14 : cos α * cos β ≠ 0 := h10
    have h15 : 2 * Real.sqrt 3 / 3 = 1 := by
      apply (mul_left_inj' h14).mp
      linarith [h13, h12]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  -- compute the desired expression
  rw [h9]
  have h_eq2 : sin α * sin β - cos α * cos β = ( (2 * Real.sqrt 3 - 3) / 3 ) * (cos α * cos β) := by
    have h_eq3 : sin α * sin β = 2 * Real.sqrt 3 / 3 * (cos α * cos β) := by
      linarith [h7]
    nlinarith
  have h_eq3 : cos α * cos β / (sin α * sin β - cos α * cos β) = 3 / (2 * Real.sqrt 3 - 3) := by
    rw [h_eq2]
    have h15 : cos α * cos β ≠ 0 := h10
    field_simp [show cos α ≠ 0 by exact h₂, show cos β ≠ 0 by exact h₃, 
      show (2 * Real.sqrt 3 - 3 : ℝ) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    ]
    <;> ring_nf 
  rw [h_eq3]
  have h_eq4 : (3 / (2 * Real.sqrt 3 - 3) : ℝ) = (2 * Real.sqrt 3 + 3 : ℝ) := by
    have h18 : (2 * Real.sqrt 3 - 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h18]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith [h_eq4]