import Mathlib

open Real Set
open scoped Real

theorem inequalities_146897 (α β γ : Real) (h : α ∈ Ioo 0 π)
  (h' : β ∈ Ioo 0 π) (h'' : γ ∈ Ioo 0 π) (h''' : α + β + γ = π) :
  cos (2*α) + cos (2*β) - cos (2*γ) ≤ 3 / 2 := by
  rcases h with ⟨hα1, hα2⟩
  rcases h' with ⟨hβ1, hβ2⟩
  rcases h'' with ⟨hγ1, hγ2⟩
  have h1 : γ = π - (α + β) := by 
    linarith 
  have h2 : 2 * γ = 2 * π - 2 * (α + β) := by 
    rw [h1]
    ring 
  have h3 : cos (2 * γ) = cos (2 * (α + β)) := by 
    have h4 : 2 * γ = 2 * π - 2 * (α + β) := h2 
    rw [h4]
    have h5 : cos (2 * π - 2 * (α + β)) = cos (2 * (α + β)) := by 
      rw [cos_two_pi_sub]
    exact_mod_cast h5
  have h4 : cos (2 * (α + β)) = cos (2 * α) * cos (2 * β) - sin (2 * α) * sin (2 * β) := by 
    rw [show 2 * (α + β) = 2 * α + 2 * β by ring]
    rw [cos_add]
  -- Express the original expression
  have eq1 : cos (2 * α) + cos (2 * β) - cos (2 * γ) =
      cos (2 * α) + cos (2 * β) - (cos (2 * α) * cos (2 * β) - sin (2 * α) * sin (2 * β)) := by 
    rw [h3, h4]
  -- Rewrite the goal
  rw [eq1]
  have h6 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by 
    have : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (2 * α)
    linarith
  have h7 : sin (2 * β) ^ 2 + cos (2 * β) ^ 2 = 1 := by 
    have : sin (2 * β) ^ 2 + cos (2 * β) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (2 * β)
    linarith
  nlinarith [sq_nonneg (cos (2 * α) - cos (2 * β)), sq_nonneg (sin (2 * α) - sin (2 * β)), 
          sq_nonneg (cos (2 * α) + cos (2 * β) - 1), 
          sq_nonneg (sin (2 * α) + sin (2 * β) - (Real.sqrt 3)), 
          sq_nonneg (cos (2 * α) + cos (2 * β) + 1), 
          sq_nonneg (sin (2 * α) - sin (2 * β)), 
          Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (2 * β), 
          mul_nonneg (show (0 : ℝ) ≤ (1 : ℝ) by norm_num) (show (0 : ℝ) ≤ (1 : ℝ) by norm_num), 
          sq_nonneg (cos (2 * α) - (-1 / 2)), sq_nonneg (cos (2 * β) - (-1 / 2)), 
          sq_nonneg (sin (2 * α) - Real.sqrt 3 / 2), sq_nonneg (sin (2 * β) - Real.sqrt 3 / 2), 
          Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (2 * β), 
          sq_nonneg (cos (2 * α) + cos (2 * β) + 1), sq_nonneg (sin (2 * α) + sin (2 * β) - (Real.sqrt 3 / 2) * 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        ]