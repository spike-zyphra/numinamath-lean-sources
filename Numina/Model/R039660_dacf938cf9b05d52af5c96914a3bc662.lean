import Mathlib

open Real Set
open scoped Real

theorem algebra_213638 (α β : ℝ) (h₀ : 0 < α) (h₁ : α < π / 2) (h₂ : 0 < β)
    (h₃ : β < π / 2) (h₄ : sin α ^ 2 + sin β ^ 2 = sin (α + β)) : α + β = π / 2 := by
  have h5 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]

  rw [h5] at h₄

  have h8 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith

  have h9 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith

  have h10 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith

  have h11 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith

  have h12 : sin α = cos β := by
    nlinarith [sq_nonneg (sin α - cos β), sq_nonneg (sin β - cos α),
      Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
      h8, h9, h10, h11, mul_pos h8 h9, mul_pos h8 h10, mul_pos h8 h11, mul_pos h9 h10, mul_pos h9 h11, mul_pos h10 h11]

  have h13 : sin β = cos α := by
    nlinarith [sq_nonneg (sin α - cos β), sq_nonneg (sin β - cos α),
      Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
      h8, h9, h10, h11, mul_pos h8 h9, mul_pos h8 h10, mul_pos h8 h11, mul_pos h9 h10, mul_pos h9 h11, mul_pos h10 h11]

  have h14 : α + β = π / 2 := by
    have h15 : sin α = sin (Real.pi / 2 - β) := by
      rw [show sin (Real.pi / 2 - β) = cos β by
        rw [sin_pi_div_two_sub]
      ]
      linarith [h12]

    have h17 : α = Real.pi / 2 - β := by
      have h18 : α < Real.pi / 2 := by
        linarith

      have h16 : 0 < Real.pi / 2 - β := by
        linarith [Real.pi_gt_31415, Real.pi_lt_31416, h₃]

      have h19 : Real.pi / 2 - β < Real.pi / 2 := by
        linarith [Real.pi_gt_31415, Real.pi_lt_31416, h₃]

      have h21 : α = Real.pi / 2 - β := by
        by_cases h22 : α < Real.pi / 2 - β
        · -- Let's assume that α < π/2 - β
          have h23 : sin α < sin (Real.pi / 2 - β) := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              linarith
          linarith [h15, h23]
        by_cases h23 : α > Real.pi / 2 - β
        · -- Let's assume that α > π/2 - β
          have h24 : sin α > sin (Real.pi / 2 - β) := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              linarith
          linarith [h15, h24]
        linarith

      linarith

    linarith [h17]

  linarith [h14]