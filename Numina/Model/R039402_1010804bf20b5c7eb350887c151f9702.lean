import Mathlib

theorem algebra_186024 (α : ℝ) :
    2 * (Real.cos (α / 2 - 3 * Real.pi / 2))^2 +
    Real.sqrt 3 * Real.cos (5 * Real.pi / 2 - α) - 1 =
    2 * Real.sin (α - Real.pi / 6) := by
  have h1 : Real.cos (α / 2 - 3 * Real.pi / 2) = - Real.sin (α / 2) := by
    have hcos : Real.cos (α / 2 - 3 * Real.pi / 2) = Real.cos (α / 2) * Real.cos (3 * Real.pi / 2) + Real.sin (α / 2) * Real.sin (3 * Real.pi / 2) := by 
      rw [Real.cos_sub]
    have hcos1 : Real.cos (3 * Real.pi / 2) = 0 := by 
      have h1 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
      rw [h1]
      have h3 : Real.cos (Real.pi + Real.pi / 2) = - Real.cos (Real.pi / 2) := by 
        rw [Real.cos_add]
        simp [Real.cos_pi, Real.sin_pi]
      have h5 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      rw [h3, h5]
      all_goals norm_num
    have hsin1 : Real.sin (3 * Real.pi / 2) = -1 := by 
      have h1 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
      rw [h1]
      have h3 : Real.sin (Real.pi + Real.pi / 2) = - Real.sin (Real.pi / 2) := by 
        rw [Real.sin_add]
        simp [Real.cos_pi, Real.sin_pi]
      have h5 : Real.sin (Real.pi / 2) = 1 := by 
        exact Real.sin_pi_div_two
      rw [h3, h5]
      all_goals norm_num
    rw [hcos, hcos1, hsin1]
    all_goals ring
  have h2 : Real.cos (5 * Real.pi / 2 - α) = Real.sin (α) := by 
    have hcos : Real.cos (5 * Real.pi / 2 - α) = Real.cos (Real.pi / 2 - α) := by 
      have h3 : 5 * Real.pi / 2 - α = Real.pi / 2 - α + 2 * Real.pi := by 
        linarith [Real.pi_pos]
      rw [h3]
      have h4 : Real.cos (Real.pi / 2 - α + 2 * Real.pi) = Real.cos (Real.pi / 2 - α) := by 
        rw [show Real.pi / 2 - α + 2 * Real.pi = (Real.pi / 2 - α) + 2 * Real.pi by ring]
        rw [Real.cos_add_two_pi]
      exact h4
    have hcos3 : Real.cos (Real.pi / 2 - α) = Real.sin (α) := by 
      rw [Real.cos_sub]
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    rw [hcos, hcos3]
    all_goals ring_nf 
  have h4 : 2 * (- Real.sin (α / 2))^2 = 1 - Real.cos α := by 
    have h_eq1 : 2 * (- Real.sin (α / 2))^2 = 2 * (Real.sin (α / 2) ^ 2) := by 
      ring
    have h_eq2 : Real.cos α = 1 - 2 * (Real.sin (α / 2) ^ 2) := by 
      have h1 : Real.cos α = 1 - 2 * (Real.sin (α / 2) ^ 2) := by 
        have h2 : Real.cos α = 2 * (Real.cos (α / 2) ^ 2) - 1 := by 
          have h3 : Real.cos α = 2 * (Real.cos (α / 2)) ^ 2 - 1 := by 
            rw [← Real.cos_two_mul]
            all_goals ring_nf
          linarith [h3]
        have h13 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq (α / 2)
        have h14 : Real.cos (α / 2) ^ 2 = 1 - Real.sin (α / 2) ^ 2 := by 
          linarith
        rw [h14] at h2
        linarith
      linarith [h1]
    linarith [h_eq1, h_eq2]

  have h5 : Real.sin (α - Real.pi / 6) = Real.sqrt 3 / 2 * Real.sin α - 1 / 2 * Real.cos α := by 
    rw [show α - Real.pi / 6 = α - Real.pi / 6 by ring]
    rw [Real.sin_sub]
    have h3 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have h4 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    simp [h3, h4]
    all_goals ring_nf 
  rw [h1, h2]
  nlinarith [h4, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]