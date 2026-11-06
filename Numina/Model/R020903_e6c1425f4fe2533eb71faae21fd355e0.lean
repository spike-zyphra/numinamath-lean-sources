import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11856 :
  IsGreatest {f | ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ f = x * sqrt (1 - y) + y * sqrt (1 - x)} 1 := by
  constructor
  · -- Show that 1 belongs to the set.
    use 1, 0
    constructor
    · -- Show that 1 is in Icc 0 1
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 0 is in Icc 0 1
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that 1 = 1 * sqrt (1 - 0) + 0 * sqrt (1 - 1)
      have h1 : sqrt (1 - (0 : ℝ)) = 1 := by
        rw [show (1 - (0 : ℝ)) = (1 : ℝ) by ring]
        rw [Real.sqrt_one]
      have h2 : sqrt (1 - (1 : ℝ)) = 0 := by
        rw [show (1 - (1 : ℝ)) = (0 : ℝ) by ring]
        simp
      rw [h1, h2]
      all_goals norm_num
  · -- Show that 1 is greatest in the set.
    intro f hf
    rcases hf with ⟨x, y, hx, hy, h_eq⟩
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    have h_eq' : f = x * sqrt (1 - y) + y * sqrt (1 - x) := by linarith [h_eq]
    rw [h_eq']
    have h1 : sqrt (1 - y) ≤ 1 := by
      have h2 : 1 - y ≥ 0 := by linarith
      have h3 : sqrt (1 - y) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h4 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      have h5 : sqrt (1 - y) ≤ (1 : ℝ) := by linarith [h3, h4]
      linarith
    have h2 : sqrt (1 - x) ≤ 1 := by
      have h3 : 1 - x ≥ 0 := by linarith
      have h4 : sqrt (1 - x) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h5 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      have h6 : sqrt (1 - x) ≤ (1 : ℝ) := by linarith [h4, h5]
      linarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (sqrt (1 - y) - 1), sq_nonneg (sqrt (1 - x) - 1),
      Real.sqrt_nonneg (1 - y), Real.sqrt_nonneg (1 - x),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by linarith),
      mul_nonneg (Real.sqrt_nonneg (1 - y)) (Real.sqrt_nonneg (1 - x)),
      mul_nonneg (sub_nonneg.2 hx0) (sub_nonneg.2 hy0),
      mul_nonneg (sub_nonneg.2 (show (0 : ℝ) ≤ 1 - x by linarith)) (sub_nonneg.2 (show (0 : ℝ) ≤ 1 - y by linarith))
    ]