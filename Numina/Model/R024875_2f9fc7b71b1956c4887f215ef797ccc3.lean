import Mathlib

theorem number_theory_291312 {f : ℝ → ℝ} (hf : ∀ x, f (Real.cos x) = Real.cos (17 * x)) :
    ∀ x, (f (Real.cos x))^2 + (f (Real.sin x))^2 = 1 := by
  intro x
  have h1 : f (Real.cos x) = Real.cos (17 * x) := hf x
  have h2 : f (Real.sin x) = Real.cos (17 * (Real.pi / 2 - x)) := by
    have h3 : Real.sin x = Real.cos (Real.pi / 2 - x) := by 
      rw [← Real.cos_pi_div_two_sub]
    rw [h3]
    apply hf
  rw [h1, h2]
  have h3 : Real.cos (17 * (Real.pi / 2 - x)) = Real.sin (17 * x) := by
    have h4 : 17 * (Real.pi / 2 - x) = 17 * (Real.pi / 2) - 17 * x := by
      ring
    rw [h4]
    have h5 : Real.cos (17 * (Real.pi / 2) - 17 * x) = Real.cos (17 * (Real.pi / 2)) * Real.cos (17 * x) + Real.sin (17 * (Real.pi / 2)) * Real.sin (17 * x) := by
      rw [Real.cos_sub]
    rw [h5]
    -- Real.cos (17 * (Real.pi / 2)) = 0
    have h6 : Real.cos (17 * (Real.pi / 2)) = 0 := by
      have h7 : 17 * (Real.pi / 2) = 8 * Real.pi + Real.pi / 2 := by
        linarith [Real.pi_pos]
      rw [h7]
      have h8 : Real.cos (8 * Real.pi + Real.pi / 2) = Real.cos (Real.pi / 2) := by
        have h9 : 8 * Real.pi + Real.pi / 2 = Real.pi / 2 + 4 * (2 * Real.pi) := by
          linarith [Real.pi_pos]
        rw [h9]
        have h11 : Real.cos (Real.pi / 2 + 4 * (2 * Real.pi)) = Real.cos (Real.pi / 2) := by
          have h14 : Real.pi / 2 + 4 * (2 * Real.pi) = Real.pi / 2 + (4 : ℕ) * (2 * Real.pi) := by
            rfl 
          rw [h14]
          rw [Real.cos_add_nat_mul_two_pi]
        exact h11
      rw [h8]
      norm_num
    -- Real.sin (17 * (Real.pi / 2)) = 1
    have h7 : Real.sin (17 * (Real.pi / 2)) = 1 := by 
      have h8 : 17 * (Real.pi / 2) = 8 * Real.pi + Real.pi / 2 := by 
        linarith [Real.pi_pos]
      rw [h8]
      have h9 : Real.sin (8 * Real.pi + Real.pi / 2) = Real.sin (Real.pi / 2) := by
        have h10 : 8 * Real.pi + Real.pi / 2 = Real.pi / 2 + 4 * (2 * Real.pi) := by
          linarith [Real.pi_pos]
        rw [h10]
        have h11 : Real.sin (Real.pi / 2 + 4 * (2 * Real.pi)) = Real.sin (Real.pi / 2) := by 
          have h14 : Real.pi / 2 + 4 * (2 * Real.pi) = Real.pi / 2 + (4 : ℕ) * (2 * Real.pi) := by 
            rfl
          rw [h14]
          rw [Real.sin_add_nat_mul_two_pi]
        exact h11
      rw [h9]
      norm_num
    rw [h6, h7]
    all_goals ring
  rw [h3]
  have h4 : Real.cos (17 * x) ^ 2 + Real.sin (17 * x) ^ 2 = 1 := by
    have h5 : Real.cos (17 * x) ^ 2 + Real.sin (17 * x) ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq (17 * x)
    linarith
  linarith [h4]
  all_goals linarith