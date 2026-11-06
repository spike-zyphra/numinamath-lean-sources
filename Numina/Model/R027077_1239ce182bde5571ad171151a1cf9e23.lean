import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_326096 : range (λ x => 4 * cos x + cos (2 * x)) = {y | -3 ≤ y ∧ y ≤ 5} := by
  ext y 
  simp [mem_range, mem_setOf_eq]
  constructor
  · -- Assume y in range 
    intro hy 
    rcases hy with ⟨x, hx⟩
    have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by 
      constructor 
      · linarith [neg_one_le_cos x] 
      · linarith [cos_le_one x] 
    have h2 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
      rw [cos_two_mul] 
    rw [h2] at hx
    constructor
    · -- Show that -3 ≤ y 
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), h1.1, h1.2]
    · -- Show that y ≤ 5 
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), h1.1, h1.2]
  · -- Assume -3 ≤ y ≤ 5 
    rintro ⟨hy1, hy2⟩
    use Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )
    have h5 : -1 ≤ (-1 + Real.sqrt (6 + 2 * y) / 2 ) ∧ (-1 + Real.sqrt (6 + 2 * y) / 2 ) ≤ 1 := by
      constructor
      · -- Show that -1 ≤ -1 + sqrt(6 + 2y)/2 
        nlinarith [Real.sqrt_nonneg (6 + 2 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 6 + 2 * y by linarith), hy1, hy2]
      · -- Show that -1 + sqrt(6 + 2y)/2 ≤ 1 
        nlinarith [Real.sqrt_nonneg (6 + 2 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 6 + 2 * y by linarith), hy1, hy2]
    have h6 : Real.cos (Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )) = -1 + Real.sqrt (6 + 2 * y) / 2 := by
      apply Real.cos_arccos 
      all_goals 
        nlinarith [Real.sqrt_nonneg (6 + 2 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 6 + 2 * y by linarith), hy1, hy2]
    have h7 : 4 * Real.cos (Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )) + Real.cos (2 * Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )) = y := by
      have h8 : Real.cos (2 * Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )) = 2 * (Real.cos (Real.arccos (-1 + Real.sqrt (6 + 2 * y) / 2 )) )^2 - 1 := by
        rw [cos_two_mul]
        <;> simp [Real.cos_sq]
        <;> nlinarith
      rw [h8, h6]
      nlinarith [Real.sqrt_nonneg (6 + 2 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 6 + 2 * y by linarith), hy1, hy2]
    simpa using h7