import Mathlib

open Real Set
open scoped Real

theorem inequalities_65943 (α β γ : Real) (h : α ∈ Ioo 0 π)
  (h' : β ∈ Ioo 0 π) (h'' : γ ∈ Ioo 0 π) (h''' : α + β + γ = π) :
  8 / (3 + 2 * cos γ) ≤ 1 / sin α + 1 / sin β := by
  rcases h with ⟨h1, h2⟩
  rcases h' with  ⟨h3, h4⟩
  rcases h'' with  ⟨h5, h6⟩
  have h7 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h8 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h10 : 3 + 2 * cos γ > 0 := by
    have h11 : -1 ≤ cos γ := by
      apply neg_one_le_cos
    nlinarith [cos_le_one γ, h11]

  have h11 : cos γ = -cos (α + β) := by
    have h13 : γ = π - (α + β) := by linarith [h''']
    rw [h13]
    have h12 : cos (π - (α + β)) = -cos (α + β) := by
      rw [cos_pi_sub]
    exact h12

  have h13 : cos (α + β) = cos α * cos β - sin α * sin β := by
    exact cos_add α β

  have h14 : cos γ = sin α * sin β - cos α * cos β := by
    rw [h11, h13]
    all_goals
      ring
  have h18 : (sin α + sin β) * (3 + 2 * cos γ) ≥ 8 * sin α * sin β := by
    rw [show cos γ = sin α * sin β - cos α * cos β by linarith [h14]]
    have h19 : 0 < sin α := by linarith [h7]
    have h20 : 0 < sin β := by linarith [h8]
    have h21 : (sin α + sin β) * (3 + 2 * (sin α * sin β - cos α * cos β)) ≥ 8 * sin α * sin β := by
      nlinarith [sq_nonneg (sin α - sin β), sq_nonneg (sin α + sin β - 2 * sin α * sin β), 
          sq_nonneg (cos α - cos β), sq_nonneg (sin α - cos α), sq_nonneg (sin β - cos β),
          sq_nonneg (sin α * sin β - cos α * cos β), sq_nonneg (sin α + sin β - 1), sq_nonneg (sin α - sin β), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          sq_nonneg (sin α ^ 2 - sin β ^ 2), sq_nonneg (cos α - cos β), mul_pos h7 h8, 
          mul_pos (show 0 < Real.pi - α by linarith [h1, h2]) (show 0 < Real.pi - β by linarith [h3, h4]), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β
          ]
    linarith
  have h19 : (1 / sin α + 1 / sin β) - 8 / (3 + 2 * cos γ) ≥ 0 := by
    have h19' : (1 / sin α + 1 / sin β) - 8 / (3 + 2 * cos γ) = 
      ( (sin α + sin β) * (3 + 2 * cos γ) - 8 * (sin α * sin β) ) / ( sin α * sin β * (3 + 2 * cos γ) ) := by
      field_simp
      <;> ring
    rw [h19']
    have h21 : sin α * sin β * (3 + 2 * cos γ) > 0 := by
      positivity
    have h20 : (sin α + sin β) * (3 + 2 * cos γ) - 8 * (sin α * sin β) ≥ 0 := by 
      nlinarith [h18]
    apply div_nonneg
    all_goals linarith [h20, h21]
  linarith