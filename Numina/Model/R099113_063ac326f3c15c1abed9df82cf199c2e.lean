import Mathlib

theorem algebra_320909 (x y z : ℝ) :
    (y - z) ^ 2 + (z - x) ^ 2 + (x - y) ^ 2 =
    (y + z - 2 * x) ^ 2 + (z + x - 2 * y) ^ 2 + (x + y - 2 * z) ^ 2 →
    x = y ∧ y = z := by
  intro h
  have h1 : (x - y) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
      sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  have h11 : x - y = 0 := by
    apply pow_eq_zero 
    exact h1
  have h2 : (y - z) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
      sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  have h22 : y - z = 0 := by
    apply pow_eq_zero 
    exact h2
  constructor
  · -- Proof that x = y 
    linarith
  · -- Proof that y = z 
    linarith