import Mathlib

theorem algebra_598580 (x : Fin 3 → ℝ) (h1 : x 0 + (1 / 2) * x 1 + (1 / 3) * x 2 = 1)
    (h2 : x 0 ^ 2 + (1 / 2) * x 1 ^ 2 + (1 / 3) * x 2 ^ 2 = 3) :
    x 2 ≥ -21 / 11 := by 
  have eq1 : x 0 = 1 - (1 / 2) * x 1 - (1 / 3) * x 2 := by 
    linarith 
  have h3 : (1 - (1 / 2) * x 1 - (1 / 3) * x 2) ^ 2 + (1 / 2) * x 1 ^ 2 + (1 / 3) * x 2 ^ 2 = 3 := by 
    rw [eq1] at h2 
    linarith 
  nlinarith [sq_nonneg (x 1 - (2 / 3 - 2 / 9 * x 2)), sq_nonneg ((1 / 2) * x 1 - 1 / 3), sq_nonneg ((x 1 - (2 / 3 - 2 / 9 * x 2)) / (2 / 3)), sq_nonneg ((x 2 + 21 / 11) * (11 / 11)), sq_nonneg (x 1 - 24 / 11)]