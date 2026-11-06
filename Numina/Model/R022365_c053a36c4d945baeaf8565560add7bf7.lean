import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20453 :
  IsGreatest {f | ∃ x y : ℝ, x ∈ Icc (-1) 1 ∧ y ∈ Icc (-1) 1 ∧ f = x * sqrt (1 - y ^ 2) + y * sqrt (1 - x ^ 2)} 1 := by
  constructor
  · -- Show 1 is in the set
    use 0, 1
    constructor
    · norm_num [mem_Icc]
    constructor
    · norm_num [mem_Icc]
    · -- Compute f(0, 1)
      have h1 : sqrt (1 - (1 : ℝ) ^ 2) = sqrt (0 : ℝ) := by norm_num
      have h2 : sqrt (1 - (0 : ℝ) ^ 2) = sqrt (1 : ℝ) := by norm_num
      rw [h1, h2]
      simp [sqrt_zero, sqrt_one]
      all_goals norm_num
  · -- Show 1 is the greatest element
    intro f hf
    rcases hf with ⟨x, y, hx, hy, h_eq⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : 0 ≤ 1 - y^2 := by nlinarith
    have h4 : 0 ≤ 1 - x^2 := by nlinarith
    have h2 : sqrt (1 - y^2) ≥ 0 := by positivity
    have h3 : sqrt (1 - x^2) ≥ 0 := by positivity
    have h5 : x * sqrt (1 - y^2) + y * sqrt (1 - x^2) ≤ 1 := by
      nlinarith [sq_nonneg (x - sqrt (1 - y ^ 2)), sq_nonneg (y - sqrt (1 - x ^ 2)), 
        sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), 
        Real.sqrt_nonneg (1 - y^2), Real.sqrt_nonneg (1 - x^2), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y ^ 2 by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith), 
        mul_nonneg (Real.sqrt_nonneg (1 - y^2)) (Real.sqrt_nonneg (1 - x^2)), 
        mul_self_nonneg (x - y), mul_self_nonneg (sqrt (1 - y^2) - sqrt (1 - x^2)), 
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith), 
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 1 - y^2 by nlinarith), 
        mul_nonneg (show 0 ≤ (1 : ℝ) - y^2 by nlinarith) (show 0 ≤ (1 : ℝ) - x^2 by nlinarith)]
    nlinarith [h_eq, h5]