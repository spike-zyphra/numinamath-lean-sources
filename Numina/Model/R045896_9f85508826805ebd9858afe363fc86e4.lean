import Mathlib

open Real Set


theorem algebra_246845 (α β : ℝ) (h0 : α ∈ Ioo 0 (π / 2)) (h1 : β ∈ Ioo 0 (π / 2))
    (h2 : sin α ^ 2 + sin β ^ 2 = sin (α + β)) : α + β = π / 2 := by
  rcases h0 with ⟨hα1, hα2⟩
  rcases h1 with ⟨hβ1, hβ2⟩
  have h3 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  by_cases h : α + β < π / 2
  · -- Assume α + β < π / 2
    have h4 : α < π / 2 - β := by linarith 
    have h5 : sin α < cos β := by
      have h6 : sin α < sin (π / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith
      have h7 : sin (π / 2 - β) = cos β := by
        rw [show π / 2 - β = π / 2 - β by rfl]
        rw [sin_pi_div_two_sub]
      linarith
    have h8 : cos α > sin β := by
      have h9 : cos α > cos (π / 2 - β) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith
      have h10 : cos (π / 2 - β) = sin β := by
        rw [cos_pi_div_two_sub]
      linarith
    have h1004 : 0 < cos α := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      . -- Show -π/2 < α
        nlinarith [Real.pi_pos, hα1]
      . -- Show α < π/2
        linarith [Real.pi_pos, hα2]
    have h1005 : sin α ^ 2 + sin β ^ 2 < sin α * cos β + cos α * sin β := by 
      nlinarith [Real.sin_sq_add_cos_sq α, 
        Real.sin_sq_add_cos_sq β, 
        sq_nonneg (sin α - cos β), 
        sq_nonneg (sin β - cos α), 
        mul_pos (show 0 < sin α by apply sin_pos_of_pos_of_lt_pi; linarith; linarith) 
          (show 0 < sin β by apply sin_pos_of_pos_of_lt_pi; linarith; linarith), 
        h1004, 
        sq_pos_of_pos h1004, 
        sq_nonneg (sin α ^ 2 - sin β ^ 2), sq_nonneg (sin α - sin β)
      ]
    have h17 : sin α * cos β + cos α * sin β = sin (α + β) := by 
      rw [←h3]
    nlinarith [h2, h17, Real.sin_pos_of_pos_of_lt_pi (show 0 < α + β by linarith) (show α + β < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by nlinarith [Real.pi_pos] ) ]
  · -- Assume α + β ≥ π / 2 
    by_cases h' : α + β > π / 2
    · -- Assume α + β > π / 2
      have h4 : α > π / 2 - β := by linarith 
      have h5 : sin α > cos β := by 
        have h6 : sin α > sin (π / 2 - β) := by 
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith
        have h7 : sin (π / 2 - β) = cos β := by 
          rw [show π / 2 - β = π / 2 - β by rfl]
          rw [sin_pi_div_two_sub]
        linarith 
      have h8 : cos α < sin β := by 
        have h9 : cos α < cos (π / 2 - β) := by 
          apply Real.cos_lt_cos_of_nonneg_of_le_pi 
          all_goals linarith
        have h10 : cos (π / 2 - β) = sin β := by 
          rw [cos_pi_div_two_sub]
        linarith
      have h1004 : 0 < cos α := by
        apply Real.cos_pos_of_mem_Ioo 
        constructor
        . -- Show -π/2 < α 
          nlinarith [Real.pi_pos, hα1] 
        . -- Show α < π/2 
          linarith [Real.pi_pos, hα2]
      have h1005 : sin α ^ 2 + sin β ^ 2 > sin α * cos β + cos α * sin β := by
        nlinarith [Real.sin_sq_add_cos_sq α, 
          Real.sin_sq_add_cos_sq β, 
          sq_pos_of_pos h1004, 
          sq_nonneg (sin α - cos β), 
          sq_nonneg (sin β - cos α), 
          mul_pos (show 0 < sin α by apply sin_pos_of_pos_of_lt_pi; linarith; linarith) 
            (show 0 < sin β by apply sin_pos_of_pos_of_lt_pi; linarith; linarith), 
          h1004, 
          sq_nonneg (sin α ^ 2 - sin β ^ 2), sq_nonneg (sin α - sin β)
        ]
      have h17 : sin α * cos β + cos α * sin β = sin (α + β) := by 
        rw [←h3]
      nlinarith [h2, h17, Real.sin_pos_of_pos_of_lt_pi (show 0 < α + β by linarith) (show α + β < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by nlinarith [Real.pi_pos] ) ]
    · -- Assume α + β = π / 2 
      have h6 : α + β = π / 2 := by linarith
      linarith