import Mathlib

open Real Set
open scoped Real

theorem algebra_324918 : sqrt (9 + 8 * cos (π / 9)) - 1 / cos (π / 9) = 3 := by
  -- First, establish that cos(20°) > 0.
  have h1 : cos (π / 9) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · -- Show that 0 < π / 9
      linarith [Real.pi_pos]
    · -- Show that π / 9 < π / 2
      nlinarith [Real.pi_pos]
  -- Define h5 as the equality we need
  have h5 : sqrt (9 + 8 * cos (π / 9)) = 1 / cos (π / 9) + 3 := by
    -- First, establish that both sides square to the same value
    have h6 : (1 / cos (π / 9) + 3) ^ 2 = 9 + 8 * cos (π / 9) := by
      have h2 : (1 / cos (π / 9) + 3 : ℝ) ^ 2 = (1 / cos (π / 9)) ^ 2 + 6 * (1 / cos (π / 9)) + 9 := by 
        ring
      rw [h2] at *
      -- Show that (1 / cos (π / 9)) ^ 2 + 6 * (1 / cos (π / 9)) + 9 = 9 + 8 * cos (π / 9)
      -- First, derive the cubic for cos(π/9) from 3 * (π/9) = π/3
      have h7 : 8 * cos (π / 9) ^ 3 - 6 * cos (π / 9) - 1 = 0 := by 
        have h8 : cos (3 * (π / 9)) = 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) := by 
          rw [cos_three_mul]
        have h9 : 3 * (π / 9) = π / 3 := by ring_nf 
        rw [h9] at h8
        have h10 : cos (π / 3) = 1 / 2 := by
          rw [Real.cos_pi_div_three]
        rw [h10] at h8
        linarith
      have eq9 : (1 / cos (π / 9)) ^ 2 + 6 * (1 / cos (π / 9)) + 9 = 9 + 8 * cos (π / 9) := by 
        have eq3 : (1 / cos (π / 9)) ^ 2 = 1 / (cos (π / 9) ^ 2) := by 
          field_simp
        rw [eq3]
        have eq6 : 1 / (cos (π / 9) ^ 2) + 6 * (1 / cos (π / 9)) + 9 = 9 + 8 * cos (π / 9) := by
          have h7' : 8 * cos (π / 9) ^ 3 - 6 * cos (π / 9) - 1 = 0 := h7
          have eq8 : cos (π / 9) > 0 := h1
          field_simp [show cos (π / 9) ≠ 0 by linarith [eq8]] at *
          nlinarith [sq_pos_of_pos eq8, sq_nonneg (cos (π / 9) ^ 2 - 1), sq_nonneg (cos (π / 9) - 1 / 2)]
        linarith
      linarith 
    -- Verify positivity for sqrt and derivative expressions
    have h7 : sqrt (9 + 8 * cos (π / 9)) ≥ 0 := by positivity 
    have h8 : (1 / cos (π / 9) + 3 : ℝ) ≥ 0 := by 
      positivity
    -- Show equality by squaring and applying sqrt injectivity
    have h10 : (sqrt (9 + 8 * cos (π / 9))) ^ 2 = (1 / cos (π / 9) + 3) ^ 2 := by 
      rw [Real.sq_sqrt]
      all_goals nlinarith 
    have h11 : sqrt (9 + 8 * cos (π / 9)) = (1 / cos (π / 9) + 3 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg (9 + 8 * cos (π / 9)), show (0 : ℝ) ≤ (1 / cos (π / 9) + 3) by positivity]
    linarith 
  -- Now use the equality to solve the original expression
  rw [h5] 
  -- Simplify using h1
  field_simp [h1] 
  all_goals linarith