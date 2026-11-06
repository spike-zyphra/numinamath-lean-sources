import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_305495 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ t = x * sqrt (1 - y) + y * sqrt (1 - x)} 1 := by
  constructor
  · -- Show 1 is in the set
    use 0, 1
    constructor
    · -- Show 0 ∈ [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 1 ∈ [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show 1 = 0 * √(1 - 1) + 1 * √(1 - 0)
      have h1 : sqrt (1 - (1 : ℝ)) = 0 := by
        rw [show (1 - (1 : ℝ) ) = (0 : ℝ) by norm_num]
        simp
      have h2 : sqrt (1 - (0 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      norm_num
  · -- Show 1 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, hx, hy, ht⟩
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    have h3 : 0 ≤ x := by linarith
    have h4 : x ≤ 1 := by linarith
    have h5 : 0 ≤ y := by linarith
    have h6 : y ≤ 1 := by linarith
    have h7 : sqrt (1 - y) ≥ 0 := Real.sqrt_nonneg (1 - y)
    have h8 : sqrt (1 - x) ≥ 0 := Real.sqrt_nonneg (1 - x)
    have h9 : x * sqrt (1 - y) ≤ (x^2 + (1 - y)) / 2 := by
      nlinarith [Real.sqrt_nonneg (1 - y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by nlinarith), sq_nonneg (x - Real.sqrt (1 - y)), sq_nonneg (sqrt (1 - y) - (1 - y) / Real.sqrt (1 - y)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ Real.sqrt (1 - y) by positivity)]
    have h10 : y * sqrt (1 - x) ≤ (y^2 + (1 - x)) / 2 := by
      nlinarith [Real.sqrt_nonneg (1 - x), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by nlinarith), sq_nonneg (y - Real.sqrt (1 - x)), sq_nonneg (sqrt (1 - x) - (1 - x) / Real.sqrt (1 - x)), mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ Real.sqrt (1 - x) by positivity)]
    have h11 : x * sqrt (1 - y) + y * sqrt (1 - x) ≤ 1 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by nlinarith), h9, h10, mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), sq_nonneg (x - y), sq_nonneg (x + y - 1)]
    linarith [ht, h11]