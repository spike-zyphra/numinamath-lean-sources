import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_210130 :
  IsGreatest {x | ∃ t : ℝ, x = sin (2 * t) + exp (abs (sin t + cos t))} (1 + exp (sqrt 2)) ∧
  IsLeast {x | ∃ t : ℝ, x = sin (2 * t) + exp (abs (sin t + cos t))} 0 := by

  constructor
  · -- Show that 1 + exp (sqrt 2) is the greatest element
    constructor
    · -- Show that 1 + exp (sqrt 2) is in the set
      use Real.pi / 4
      have h1 : sin (2 * (Real.pi / 4)) = 1 := by
        have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
        rw [h2]
        exact sin_pi_div_two
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact sin_pi_div_four
      have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact cos_pi_div_four
      have h4 : sin (Real.pi / 4) + cos (Real.pi / 4) = Real.sqrt 2 := by
        rw [h2, h3]
        ring
      rw [h1]
      rw [show abs (sin (Real.pi / 4) + cos (Real.pi / 4)) = Real.sqrt 2 by
        rw [h4]
        all_goals norm_num [abs_of_nonneg]
      ]
      all_goals linarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num)]
    · -- Show that 1 + exp (sqrt 2) is the greatest
      intro x hx
      rcases hx with ⟨t, ht⟩
      have h1 : -1 ≤ sin (2 * t) := by
        linarith [neg_one_le_sin (2 * t), sin_le_one (2 * t)]
      have h2 : sin (2 * t) ≤ 1 := by
        linarith [sin_le_one (2 * t)]
      have h3 : abs (sin t + cos t) ≤ Real.sqrt 2 := by
        have h4 : (sin t + cos t) ^ 2 ≤ 2 := by
          nlinarith [sq_nonneg (sin t - cos t), Real.sin_sq_add_cos_sq t]
        have h5 : abs (sin t + cos t) ≤ Real.sqrt 2 := by
          have h6 : (abs (sin t + cos t)) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            have h7 : (abs (sin t + cos t)) ^ 2 = (sin t + cos t) ^ 2 := by
              rw [sq_abs]
            have h8 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
            nlinarith [h7, h8, h4]
          have h9 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
          have h10 : abs (sin t + cos t) ≥ 0 := by positivity
          nlinarith [h6, Real.sqrt_nonneg 2, abs_nonneg (sin t + cos t)]
        exact h5
      have h4 : exp (abs (sin t + cos t)) ≤ exp (Real.sqrt 2) := by
        apply Real.exp_le_exp_of_le
        linarith [h3]
      have h4x : sin (2 * t) + exp (abs (sin t + cos t)) ≤ 1 + exp (Real.sqrt 2) := by
        nlinarith [h4, h4, h2]
      linarith [ht, h4x]
  · -- Show that 0 is the least element
    constructor
    · -- Show that 0 is in the set
      use 3 * Real.pi / 4
      have h6 : sin (2 * (3 * Real.pi / 4)) = -1 := by
        have h7 : 2 * (3 * Real.pi / 4) = 3 * Real.pi / 2 := by ring
        rw [h7]
        have h8 : sin (3 * Real.pi / 2) = -1 := by 
          have h9 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
          rw [h9]
          have h10 : sin (Real.pi + Real.pi / 2) = - sin (Real.pi / 2) := by
            rw [sin_add, sin_pi, cos_pi]
            ring
          have h11 : sin (Real.pi / 2) = 1 := sin_pi_div_two
          rw [h10, h11]
          all_goals norm_num
        exact h8
      have h7 : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
        have h8 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
        rw [h8]
        rw [sin_pi_sub]
        rw [sin_pi_div_four]
      have h8 : cos (3 * Real.pi / 4) = - Real.sqrt 2 / 2 := by
        have h9 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
        rw [h9]
        rw [cos_pi_sub]
        rw [cos_pi_div_four]
        all_goals ring_nf
      have h9 : sin (3 * Real.pi / 4) + cos (3 * Real.pi / 4) = (0 : ℝ) := by
        rw [h7, h8]
        ring_nf
      have h10 : abs (sin (3 * Real.pi / 4) + cos (3 * Real.pi / 4)) = (0 : ℝ) := by
        rw [h9]
        norm_num [abs_zero]
      rw [h6, h10]
      all_goals norm_num
    · -- Show that 0 is the least
      intro x hx
      rcases hx with ⟨t, ht⟩
      have h11 : exp (abs (sin t + cos t)) ≥ 0 := by positivity
      have h5 : sin (2 * t) ≥ - exp (abs (sin t + cos t)) := by
        have h6 : abs (sin t + cos t) ≥ 0 := abs_nonneg (sin t + cos t)
        have h7 : exp (abs (sin t + cos t)) ≥ exp (0 : ℝ) := by
          apply Real.exp_le_exp_of_le
          linarith [abs_nonneg (sin t + cos t)]
        have h8 : exp (0 : ℝ) = 1 := by
          simp [exp_zero]
        have h9 : exp (abs (sin t + cos t)) ≥ 1 := by
          linarith [h7, h8]
        have h6 : sin (2 * t) ≥ -1 := by
          linarith [neg_one_le_sin (2 * t)]
        linarith [h9, h6]
      linarith [ht, h5, h11]