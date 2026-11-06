import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_16059 : IsGreatest {y : ℝ | ∃ x, y = sqrt (25 + x) + sqrt (25 - x) ∧ -25 ≤ x ∧ x ≤ 25} 10 := by
  constructor
  · -- Show that 10 is in the set
    use 0
    constructor
    · -- Show that when x = 0, sqrt (25 + 0) + sqrt (25 - 0) = 10
      have h1 : sqrt (25 + (0 : ℝ)) = 5 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (25 - (0 : ℝ)) = 5 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    constructor
    · -- Show that -25 ≤ (0 : ℝ)
      norm_num
    · -- Show that (0 : ℝ) ≤ 25
      norm_num
  · -- Show that for any element y in the set, y ≤ 10
    intro y hy
    rcases hy with ⟨x, rfl, hx1, hx2⟩
    have h1 : sqrt (25 + x) + sqrt (25 - x) ≤ 10 := by
      have h5 : (sqrt (25 + x) + sqrt (25 - x)) ^ 2 = 50 + 2 * sqrt ((25 + x) * (25 - x)) := by
        have h6 : (sqrt (25 + x)) ^ 2 = 25 + x := Real.sq_sqrt (by linarith)
        have h7 : (sqrt (25 - x)) ^ 2 = 25 - x := Real.sq_sqrt (by linarith)
        have h8 : sqrt (25 + x) * sqrt (25 - x) = sqrt ((25 + x) * (25 - x)) := by 
          rw [← Real.sqrt_mul (by linarith)]
        nlinarith [Real.sqrt_nonneg (25 + x), Real.sqrt_nonneg (25 - x)]
      have h15 : (sqrt (25 + x) + sqrt (25 - x)) ^ 2 ≤ 100 := by
        have h11 : sqrt ((25 + x) * (25 - x)) ≤ 25 := by
          have h12 : (25 + x) * (25 - x) ≤ 25 ^ 2 := by nlinarith [sq_nonneg x]
          have h13 : sqrt ((25 + x) * (25 - x)) ≤ sqrt (25 ^ 2 : ℝ) := Real.sqrt_le_sqrt (by linarith)
          have h14 : sqrt ((25 : ℝ) ^ 2) = 25 := Real.sqrt_sq (by norm_num)
          linarith
        nlinarith [Real.sqrt_nonneg ((25 + x) * (25 - x))]
      have h16 : sqrt (25 + x) + sqrt (25 - x) ≤ 10 := by
        nlinarith [Real.sqrt_nonneg (25 + x), Real.sqrt_nonneg (25 - x), h15, show (sqrt (25 + x) + sqrt (25 - x)) ^ 2 ≤ 100 by nlinarith [h15]]
      linarith
    linarith