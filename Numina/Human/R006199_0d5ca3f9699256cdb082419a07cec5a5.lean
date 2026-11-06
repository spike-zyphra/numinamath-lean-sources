import Mathlib

open Real Set
open scoped Real

theorem algebra_12842 {α : ℝ} (hα : α ∈ Ioo (π / 2) π)
  (h : sin α - sqrt 3 * cos α = logb 2 (x ^ 2 - x + 2)) :
  -1 ≤ x ∧ x < 0 ∨ 1 < x ∧ x ≤ 2 := by
    have h1 : π / 2 < α := hα.left
    have h2 : α < π := hα.right

    have h3 : sin α - sqrt 3 * cos α = 2 * sin (α - π / 3) := by
      rw [sin_sub, sin_pi_div_three, cos_pi_div_three]
      ring
  
    rw [h3] at h

    have h4 : 1 < 2 * sin (α - π / 3) := by
      have h5 : π / 6 < α - π / 3 := by linarith [Real.pi_pos, h1]
      have h6 : α - π / 3 < 5 * π / 6 := by linarith [Real.pi_pos, h2]
      have h7 : sin (α - π / 3) > 1 / 2 := by
        have h12 : sin (α - π / 3) > 1 / 2 := by
          by_contra h16
          push_neg at h16
          have h17 : sin (π / 6) = 1 / 2 := by
            rw [sin_pi_div_six]
          by_cases h19 : α - π / 3 ≤ Real.pi / 2
          · -- If α - π/3 ≤ π/2, then we can use the fact that sin is increasing on [0, π/2]
            have h20 : sin (α - π / 3) > sin (π / 6) := by
              apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
              all_goals linarith [Real.pi_pos]
            linarith [h17, h20]
          · -- Otherwise, α - π/3 > π/2, and we use the fact that sin(π - θ) = sin(θ)
            push_neg at h19
            have h21 : sin (α - π / 3) = sin (Real.pi - (α - π / 3)) := by
              rw [← sin_pi_sub]
            have h22 : 0 < Real.pi - (α - π / 3) := by
              linarith [Real.pi_pos, h19]
            have h23 : Real.pi - (α - π / 3) < Real.pi / 2 := by
              linarith [Real.pi_pos, h19]
            have h24 : sin (Real.pi - (α - π / 3)) > sin (Real.pi / 6) := by
              apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
              all_goals linarith [Real.pi_pos]
            linarith [h17, h21, h24]
        linarith
      nlinarith [Real.sin_le_one (α - π / 3), Real.sin_sq_add_cos_sq (α - π / 3)]

    have h5 : 2 * sin (α - π / 3) ≤ 2 := by
      have h26 : sin (α - π / 3) ≤ 1 := Real.sin_le_one (α - π / 3)
      linarith

    have h6 : 1 < logb 2 (x ^ 2 - x + 2) := by linarith [h, h4]
    have h7 : logb 2 (x ^ 2 - x + 2) ≤ 2 := by linarith [h, h5]

    have h8 : x ^ 2 - x + 2 > 2 := by
      have h9 : logb 2 (x ^ 2 - x + 2) > 1 := by linarith [h6]
      have h10 : x ^ 2 - x + 2 > (2 : ℝ) := by
        by_contra h13
        push_neg at h13
        have h14 : logb 2 (x ^ 2 - x + 2) ≤ 1 := by
          have h15 : x ^ 2 - x + 2 ≤ (2 : ℝ) := by linarith
          have h16 : logb 2 (x ^ 2 - x + 2) ≤ logb 2 (2 : ℝ) := by
            apply logb_le_logb_of_le
            all_goals nlinarith [sq_nonneg (x - 1 / 2), Real.pi_pos]
          have h17 : logb 2 (2 : ℝ) = 1 := by
            rw [logb_self_eq_one]
            all_goals linarith
          linarith [h16, h17]
        linarith [h9, h14]
      nlinarith

    have h18 : x ^ 2 - x + 2 ≤ (4 : ℝ) := by
      have h19 : logb 2 (x ^ 2 - x + 2) ≤ 2 := by linarith [h7]
      have h20 : x ^ 2 - x + 2 ≤ (4 : ℝ) := by
        by_contra h21
        push_neg at h21
        have h22 : logb 2 (x ^ 2 - x + 2) > 2 := by
          have h24 : x ^ 2 - x + 2 > (4 : ℝ) := by linarith
          have h25 : logb 2 (4 : ℝ) = 2 := by
            rw [logb_eq_iff_rpow_eq] <;> norm_num
          have h26 : logb 2 (x ^ 2 - x + 2) > logb 2 (4 : ℝ) := by
            apply logb_lt_logb
            all_goals nlinarith [sq_nonneg (x - 1 / 2), Real.pi_pos]
          linarith [h25, h26]
        linarith [h19, h22]
      nlinarith

    have h27 : x * (x - 1) > 0 := by nlinarith

    have h28 : -1 ≤ x := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2)]

    have h29 : x ≤ 2 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2)]

    have h30 : x < 0 ∨ x > 1 := by
      by_contra h31
      push_neg at h31
      have h32 : x * (x - 1) ≤ 0 := by nlinarith
      linarith [h27, h32]

    cases h30 with
    | inl h31 =>
      left
      exact ⟨h28, h31⟩
    | inr h32 =>
      right
      exact ⟨h32, h29⟩