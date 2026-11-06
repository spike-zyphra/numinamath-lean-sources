import Mathlib

theorem algebra_269167 {x y z : ℝ} (h1 : x + y + z = 3) (h2 : x^2 + y^2 + z^2 = 3) (h3 : x^5 + y^5 + z^5 = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have h4 : (x - 1)^2 + (y - 1)^2 + (z - 1)^2 = 0 := by
    nlinarith
  have h5 : x - 1 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have h6 : y - 1 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have h7 : z - 1 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  constructor
  · linarith
  constructor
  · linarith
  · linarith