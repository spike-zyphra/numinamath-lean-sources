import Mathlib

open Real Set
open scoped BigOperators


theorem algebra_9053 : range (λ x => cos (2 * x) - 8 * cos x) = {y | -7 ≤ y ∧ y ≤ 9} := by
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · -- Assume y in range
    intro hy
    rcases hy with ⟨x, hx⟩
    have h1 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by 
      rw [cos_two_mul]
    rw [h1] at hx
    have h2 : -1 ≤ cos x ∧ cos x ≤ 1 := by
      constructor
      · apply neg_one_le_cos
      · apply cos_le_one
    have h3 : -7 ≤ y := by
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), hx, h2.1, h2.2]
    have h4 : y ≤ 9 := by
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), hx, h2.1, h2.2]
    constructor <;> linarith
  · -- Assume y in the set
    rintro ⟨hy1, hy2⟩
    use Real.arccos (2 - Real.sqrt ((y + 9) / 2))
    have h1 : cos (2 * (Real.arccos (2 - Real.sqrt ((y + 9) / 2)))) = 2 * (cos (Real.arccos (2 - Real.sqrt ((y + 9) / 2)))) ^ 2 - 1 := by
      rw [cos_two_mul]
    have h4 : cos (Real.arccos (2 - Real.sqrt ((y + 9) / 2))) = 2 - Real.sqrt ((y + 9) / 2) := by 
      apply Real.cos_arccos
      nlinarith [Real.sqrt_nonneg ((y + 9) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (y + 9) / 2 by linarith)]
      nlinarith [Real.sqrt_nonneg ((y + 9) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (y + 9) / 2 by linarith)]
    rw [h1, h4]
    nlinarith [Real.sqrt_nonneg ((y + 9) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (y + 9) / 2 by linarith), Real.sqrt_nonneg ((y + 9) / 2)]