import Mathlib

theorem algebra_598628 {x y z : ℝ} (h₀ : x + y + z = 3) (h₁ : x^2 + y^2 + z^2 = 3)
    (h₂ : x^5 + y^5 + z^5 = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by 
  have h3 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
    nlinarith [h₀, h₁]
  have hx1 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hy1 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hz1 : (z - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hx : x - 1 = 0 := by 
    rwa [sq_eq_zero_iff] at hx1
  have hy : y - 1 = 0 := by 
    rwa [sq_eq_zero_iff] at hy1
  have hz : z - 1 = 0 := by 
    rwa [sq_eq_zero_iff] at hz1
  constructor
  · linarith
  constructor
  · linarith
  · linarith