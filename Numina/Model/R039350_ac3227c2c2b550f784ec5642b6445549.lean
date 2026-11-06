import Mathlib

open Real Set
open scoped Real

theorem calculus_22639 {n : ℤ} (hn : -90 ≤ n ∧ n ≤ 90) :
    sin (n * π / 180) = sin (419 * π / 180) ↔ n = 59 := by 
  constructor
  · -- Forward implication: if sin(n * π / 180) = sin(419 * π / 180), then n = 59
    intro h_eq
    have h1 : -90 ≤ n := hn.1
    have h2 : n ≤ 90 := hn.2
    -- Show that sin(419 * π / 180) = sin(59 * π / 180)
    have h3 : sin (419 * π / 180) = sin (59 * π / 180) := by
      have h4 : 419 * π / 180 = 59 * π / 180 + 2 * π := by
        ring_nf
      rw [h4]
      have h5 : sin (59 * π / 180 + 2 * π) = sin (59 * π / 180) := by
        rw [sin_add, sin_two_pi, cos_two_pi]
        simp
      rw [h5]
    -- Now the equation becomes sin(n * π / 180) = sin(59 * π / 180)
    rw [h3] at h_eq
    -- Show both angles n * π / 180 and 59 * π / 180 are in [-π/2, π/2]
    have h4 : (n : ℝ) * π / 180 ≥ -Real.pi / 2 := by
      have h5 : n ≥ -90 := by linarith
      have h6 : n ≤ 90 := by linarith
      have h7 : (n : ℝ) * π / 180 ≥ (-90 : ℝ) * π / 180 := by
        have h8 : (n : ℝ) ≥ (-90 : ℝ) := by exact_mod_cast h5
        have h9 : (n : ℝ) * π / 180 ≥ (-90 : ℝ) * π / 180 := by
          apply (div_le_div_right (by linarith)).mpr
          nlinarith [Real.pi_pos]
        linarith
      have h8 : -Real.pi / 2 = (-90 : ℝ) * Real.pi / 180 := by
        ring_nf
      linarith [h7, h8]
    have h5 : (n : ℝ) * π / 180 ≤ Real.pi / 2 := by
      have h8 : n ≤ 90 := by linarith
      have h6 : (n : ℝ) * π / 180 ≤ (90 : ℝ) * π / 180 := by
        have h7 : (n : ℝ) ≤ (90 : ℝ) := by exact_mod_cast h8
        have h8 : (n : ℝ) * π / 180 ≤ (90 : ℝ) * π / 180 := by
          apply (div_le_div_right (by linarith)).mpr
          nlinarith [Real.pi_pos]
        linarith
      have h9 : Real.pi / 2 = (90 : ℝ) * Real.pi / 180 := by
        ring_nf
      linarith [h6, h9]
    have h6 : (59 : ℝ) * π / 180 ≥ -Real.pi / 2 := by
      have h7 : (59 : ℝ) * π / 180 ≥ (-90 : ℝ) * π / 180 := by
        have h8 : (59 : ℝ) ≥ (-90 : ℝ) := by norm_num
        have  h9 : (59 : ℝ) * π / 180 ≥ (-90 : ℝ) * π / 180 := by
          apply (div_le_div_right (by linarith)).mpr
          nlinarith [Real.pi_pos]
        linarith
      have h8 : -Real.pi / 2 = (-90 : ℝ) * Real.pi / 180 := by
        ring_nf
      linarith [h7, h8]
    have h7 : (59 : ℝ) * π / 180 ≤ Real.pi / 2 := by
      have h9 : (59 : ℝ) * π / 180 ≤ (90 : ℝ) * π / 180 := by
        have h10 : (59 : ℝ) ≤ (90 : ℝ) := by norm_num
        have h11 : (59 : ℝ) * π / 180 ≤ (90 : ℝ) * π / 180 := by
          apply (div_le_div_right (by linarith)).mpr
          nlinarith [Real.pi_pos]
        linarith
      have h8 : Real.pi / 2 = (90 : ℝ) * Real.pi / 180 := by
        ring_nf
      linarith [h9, h8]
    -- Use injective property of sin in [-π/2, π/2]
    have h8 : sin (n * π / 180) = sin (59 * π / 180) := h_eq
    have h9 : (n : ℝ) * π / 180 = (59 : ℝ) * π / 180 := by
      by_cases h18 : (n : ℝ) * π / 180 < (59 : ℝ) * π / 180
      · -- Case n * π / 180 < 59 * π / 180
        have h16 : sin (n * π / 180) < sin ((59 : ℝ) * π / 180) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [h18, Real.pi_pos]
        linarith [h8, h16]
      by_cases h19 : (n : ℝ) * π / 180 > (59 : ℝ) * π / 180
      · -- Case n * π / 180 > 59 * π / 180
        have h17 : sin (n * π / 180) > sin ((59 : ℝ) * π / 180) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [h19, Real.pi_pos]
        linarith [h8, h17]
      -- Case n * π / 180 = 59 * π / 180
      linarith
    -- Convert the equality of angles to equality of n and 59
    have h16 : (n : ℝ) = (59 : ℝ) := by
      have h17 : (n : ℝ) * π / 180 = (59 : ℝ) * π / 180 := h9
      have h18 : π ≠ 0 := Real.pi_ne_zero
      have h19 : (n : ℝ) = (59 : ℝ) := by
        field_simp [h18] at h17 ⊢
        linarith
      linarith
    -- Convert equality from real to integer
    exact_mod_cast h16
  · -- Backward direction: if n = 59, then sin(n * π / 180) = sin(419 * π / 180)
    intro h_eq
    rw [h_eq]
    -- Show sin(59 * π / 180) = sin(419 * π / 180)
    have h3 : sin (59 * π / 180) = sin (419 * π / 180) := by
      have h4 : 419 * π / 180 = 59 * π / 180 + 2 * π := by
        ring_nf
      rw [h4]
      have h5 : sin (59 * π / 180 + 2 * π) = sin (59 * π / 180) := by
        rw [sin_add, sin_two_pi, cos_two_pi]
        simp
      rw [h5]
    linarith [h3]