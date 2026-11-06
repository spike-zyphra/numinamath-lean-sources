import Mathlib

open Real Set
open scoped Real

theorem inequalities_172684 (α β γ : Real) (h : α ∈ Ioo 0 π)
  (h' : β ∈ Ioo 0 π) (h'' : γ ∈ Ioo 0 π) (h''' : α + β + γ = π) :
  cos α / (sin β * sin γ) + cos β / (sin γ * sin α) + cos γ / (sin α * sin β) ≤ 3 := by
  rcases h with ⟨h1, h2⟩
  rcases h' with ⟨h3, h4⟩
  rcases h'' with ⟨h5, h6⟩
  have h7 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h8 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h9 : sin γ > 0 := by
    have h10 : γ < π := by linarith
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h10 : sin α * sin β * sin γ > 0 := by
    positivity
  have h11 : cos α / (sin β * sin γ) + cos β / (sin γ * sin α) + cos γ / (sin α * sin β) - 3 ≤ 0 := by
    have h10' : sin α * sin β * sin γ > 0 := h10
    have h13 : (cos α / (sin β * sin γ) + cos β / (sin γ * sin α) + cos γ / (sin α * sin β) - 3) =
      (cos α * sin α + cos β * sin β + cos γ * sin γ - 3 * (sin α * sin β * sin γ)) / (sin α * sin β * sin γ) := by
      field_simp [mul_ne_zero (ne_of_gt h7) (ne_of_gt h8), mul_ne_zero (ne_of_gt h8) (ne_of_gt h9), mul_ne_zero (ne_of_gt h7) (ne_of_gt h9)]
      all_goals ring
    rw [h13]
    have h14 : cos α * sin α + cos β * sin β + cos γ * sin γ - 3 * (sin α * sin β * sin γ) ≤ 0 := by
      have h74 : cos α * sin α + cos β * sin β + cos γ * sin γ ≤ 3 * (sin α * sin β * sin γ) := by
        have h61 : cos α * sin α + cos β * sin β + cos γ * sin γ = (1 / 2) * (sin (2 * α) + sin (2 * β) + sin (2 * γ)) := by
          have h62 : cos α * sin α = (1 / 2) * sin (2 * α) := by 
            have : sin (2 * α) = 2 * sin α * cos α := by rw [sin_two_mul]
            nlinarith 
          have h63 : cos β * sin β = (1 / 2) * sin (2 * β) := by 
            have : sin (2 * β) = 2 * sin β * cos β := by rw [sin_two_mul]
            nlinarith 
          have h64 : cos γ * sin γ = (1 / 2) * sin (2 * γ) := by 
            have : sin (2 * γ) = 2 * sin γ * cos γ := by rw [sin_two_mul]
            nlinarith 
          nlinarith [h62, h63, h64]
        rw [h61]
        have h65 : sin (2 * α) + sin (2 * β) + sin (2 * γ) = 4 * (sin α * sin β * sin γ) := by
          have h66 : γ = π - (α + β) := by linarith [h''']
          have h67 : sin (2 * γ) = - sin (2 * (α + β)) := by
            rw [show 2 * γ = 2 * (π - (α + β)) by nlinarith [h66]]
            have h78 : sin (2 * (π - (α + β)) ) = - sin (2 * (α + β)) := by
              have h79 : 2 * (π - (α + β)) = 2 * π - 2 * (α + β) := by ring
              rw [h79]
              have h80 : sin (2 * π - 2 * (α + β) ) = - sin (2 * (α + β) ) := by
                rw [sin_sub, sin_two_pi, cos_two_pi]
                norm_num
              linarith [h80]
            linarith [h78]
          have h68 : sin (2 * α) + sin (2 * β) + sin (2 * γ) = 4 * (sin α * sin β * sin γ) := by
            rw [h67]
            have h69 : sin (2 * α) + sin (2 * β) - sin (2 * (α + β)) = 4 * (sin α * sin β * sin γ) := by
              have h69 : sin (2 * (α + β)) = sin (2 * α + 2 * β) := by ring_nf 
              rw [h69]
              have h70 : sin (2 * α + 2 * β) = sin (2 * α) * cos (2 * β) + cos (2 * α) * sin (2 * β) := by 
                rw [sin_add]
              rw [h70]
              have h71 : cos (2 * α) = 1 - 2 * sin α ^ 2 := by 
                rw [cos_two_mul, sin_sq]
                all_goals nlinarith
              have h72 : cos (2 * β) = 1 - 2 * sin β ^ 2 := by 
                rw [cos_two_mul, sin_sq]
                all_goals nlinarith
              have h73 : sin (2 * α) = 2 * sin α * cos α := by 
                rw [sin_two_mul]
              have h74 : sin (2 * β) = 2 * sin β * cos β := by 
                rw [sin_two_mul]
              rw [h73, h74, h71, h72]
              have h75 : sin γ = sin (α + β) := by 
                have h67 : γ = π - (α + β) := by linarith [h''']
                rw [h67]
                have h78 : sin (π - (α + β)) = sin (α + β) := by 
                  rw [sin_pi_sub]
                linarith [h78]
              have h77 : sin (α + β) = sin α * cos β + cos α * sin β := by 
                rw [sin_add]
              have h78 : sin γ = sin α * cos β + cos α * sin β := by
                linarith [h75, h77]
              nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h7 h8, mul_pos h7 h9, mul_pos h8 h9, sq_nonneg (cos α - cos β), sq_nonneg (sin α - sin β)]
            linarith
          linarith
        have h73 : (1 / 2) * (sin (2 * α) + sin (2 * β) + sin (2 * γ)) ≤ 3 * (sin α * sin β * sin γ) := by
          nlinarith [show sin (2 * α) + sin (2 * β) + sin (2 * γ) = 4 * (sin α * sin β * sin γ) from h65, mul_pos h7 h8, mul_pos h7 h9, mul_pos h8 h9]
        linarith
      nlinarith
    apply div_nonpos_of_nonpos_of_nonneg h14 (by positivity)
  linarith