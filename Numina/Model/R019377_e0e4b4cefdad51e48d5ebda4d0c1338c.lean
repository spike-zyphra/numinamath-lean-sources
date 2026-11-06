import Mathlib

open Real

theorem algebra_152340 (x y z α : ℝ) (h₀ : α = arccos (5 / 9)) (h₁ : y - x = α)
    (h₂ : z - y = α) (h₃ : (1 + cos y) ^ 2 = (1 + cos x) * (1 + cos z)) :
    cos y = -7 / 9 := by
  have h4 : x = y - α := by linarith
  have h5 : z = y + α := by linarith
  have h6 : cos x = cos y * cos α + sin y * sin α := by
    rw [h4]
    rw [cos_sub]
  have h7 : cos z = cos y * cos α - sin y * sin α := by 
    rw [h5]
    rw [cos_add]
  have h8 : cos α = 5 / 9 := by
    rw [h₀]
    have h11 : cos (arccos (5 / 9)) = 5 / 9 := by
      rw [cos_arccos]
      all_goals 
        norm_num
    linarith [h11]
  have h17 : sin α ^ 2 = 56 / 81 := by 
    calc
      sin α ^ 2 = 1 - cos α ^ 2 := by 
        have h14 : sin α ^ 2 + cos α ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq α
        linarith [h14]
      _ = 1 - (5 / 9)^2 := by 
        rw [h8]
      _ = 56 / 81 := by 
        norm_num
  rw [h6, h7] at h₃
  nlinarith [h8, h17, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq α, sq_nonneg (sin y ^ 2 - (1 - cos y ^ 2) ^ 2), sq_nonneg (sin α ^ 2 - (1 - cos α ^ 2) ^ 2)]