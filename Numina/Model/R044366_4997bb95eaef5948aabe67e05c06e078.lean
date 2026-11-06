import Mathlib

open Real Set
open scoped Real

theorem algebra_184028 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : sin α ^ 2 + sin β ^ 2 = sin (α + β)) :
    α + β = π / 2 := by
  have h6 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h6] at h₂
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h9 : α + β > 0 := by nlinarith [h₀₁, h₁₁]
  have h9' : α + β < Real.pi := by
    nlinarith [h₀₂, h₁₂, Real.pi_gt_three]
  by_cases h : α + β > Real.pi / 2
  · -- Assume α + β > π/2.
    have h10 : sin α > cos β := by
      have h11 : α > Real.pi / 2 - β := by linarith
      have h12 : sin α > sin (Real.pi / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      rw [show sin (Real.pi / 2 - β) = cos β by
        rw [sin_pi_div_two_sub]
      ] at h12
      linarith
    have h11 : sin β > cos α := by
      have h12 : β > Real.pi / 2 - α := by linarith
      have h13 : sin β > sin (Real.pi / 2 - α) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      rw [show sin (Real.pi / 2 - α) = cos α by
        rw [sin_pi_div_two_sub]
      ] at h13
      linarith
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith), 
          Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith),
          h9, h9', h10, h11
        ]
  · -- Now, α + β ≤ π/2.
    by_cases h5 : α + β < Real.pi / 2
    · -- Assume α + β < π/2.
      have h14 : sin α < cos β := by
        have h15 : α < Real.pi / 2 - β := by linarith
        have h16 : sin α < sin (Real.pi / 2 - β) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_pos]
        rw [show sin (Real.pi / 2 - β) = cos β by
          rw [sin_pi_div_two_sub]
        ] at h16
        linarith
      have h15 : sin β < cos α := by
        have h16 : β < Real.pi / 2 - α := by linarith
        have h17 : sin β < sin (Real.pi / 2 - α) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_pos]
        rw [show sin (Real.pi / 2 - α) = cos α by
          rw [sin_pi_div_two_sub]
        ] at h17
        linarith
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith), 
          Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith),
          h9, h9', h14, h15
        ]
    · -- Now, α + β ≥ π/2.
      have h7 : α + β = Real.pi / 2 := by 
        nlinarith [h5, Real.pi_pos]
      exact_mod_cast h7