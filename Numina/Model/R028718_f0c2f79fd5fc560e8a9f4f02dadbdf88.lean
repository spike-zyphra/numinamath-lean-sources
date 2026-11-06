import Mathlib

theorem algebra_70055 {x y z : ℝ} (h₀ : x = y^3 + y - 8) (h₁ : y = z^3 + z - 8)
    (h₂ : z = x^3 + x - 8) :
    (x, y, z) = (2, 2, 2) := by
  simp [Prod.ext_iff] at *
  have h_eq1 : x = 2 := by 
    nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4),
        sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), 
        h₀, h₁, h₂, 
        mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (y - 2)), 
        mul_nonneg (sq_nonneg (y - 2)) (sq_nonneg (z - 2)), 
        mul_nonneg (sq_nonneg (z - 2)) (sq_nonneg (x - 2))]
  have h_eq2 : y = 2 := by 
    nlinarith [sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4), sq_nonneg (x^2 - 4),
        sq_nonneg (y - 2), sq_nonneg (z - 2), sq_nonneg (x - 2), 
        h₀, h₁, h₂, 
        mul_nonneg (sq_nonneg (y - 2)) (sq_nonneg (z - 2)), 
        mul_nonneg (sq_nonneg (z - 2)) (sq_nonneg (x - 2)), 
        mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (y - 2))]
  have h_eq3 : z = 2 := by 
    nlinarith [sq_nonneg (z^2 - 4), sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4),
        sq_nonneg (z - 2), sq_nonneg (x - 2), sq_nonneg (y - 2), 
        h₀, h₁, h₂, 
        mul_nonneg (sq_nonneg (z - 2)) (sq_nonneg (x - 2)), 
        mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (y - 2)), 
        mul_nonneg (sq_nonneg (y - 2)) (sq_nonneg (z - 2))]
  constructor
  · -- Show x = 2
    linarith [h_eq1]
  constructor
  · -- Show y = 2
    linarith [h_eq2]
  · -- Show z = 2
    linarith [h_eq3]