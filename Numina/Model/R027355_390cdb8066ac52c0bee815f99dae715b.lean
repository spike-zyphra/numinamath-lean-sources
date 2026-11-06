import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_600855 :
  (∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x + y + z = 2 → x^2 * y^2 + y^2 * z^2 + z^2 * x^2 + x * y * z ≤ 1) ∧
  (∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 2 ∧ x^2 * y^2 + y^2 * z^2 + z^2 * x^2 + x * y * z = 1) := by 
  constructor
  · -- Prove the first part.
    intro x y z hx hy hz h1
    have h2 : z = 2 - x - y := by linarith
    have hx1 : x ≥ 0 := by linarith
    have hy1 : y ≥ 0 := by linarith
    have hz1 : z ≥ 0 := by linarith
    rw [show z = 2 - x - y by linarith [h1, h2]]
    have h4 : 0 ≤ (2 - x - y : ℝ) := by nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((2 - x - y) - 1), 
      mul_nonneg hx1 hy1, 
      mul_nonneg hy1 (show (0:ℝ) ≤ 2 - x - y by nlinarith), 
      mul_nonneg hx1 (show (0:ℝ) ≤ 2 - x - y by nlinarith), 
      sq_nonneg (x * y - (y * (2 - x - y))), 
      sq_nonneg (x * y - (x * (2 - x - y))), 
      sq_nonneg (y * (2 - x - y) - (x * (2 - x - y))), 
      sq_nonneg (x - y), 
      sq_nonneg (x - (2 - x - y)), 
      sq_nonneg (y - (2 - x - y))]
  · -- For the second part, proving existence of the equality points.
    use 1, 1, 0
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num