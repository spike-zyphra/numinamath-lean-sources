import Mathlib

open Real Set

theorem algebra_16806 : IsLeast {y : ℝ | ∃ x, 1 < x ∧ y = (x + 8) / sqrt (x - 1)} 6 := by
  constructor
  · -- Show 6 is in the set
    use 10
    constructor
    · norm_num
    · -- Show that (10 + 8)/sqrt(10-1) = 6
      have h1 : sqrt (10 - 1 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
  · -- Show 6 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx1, heq⟩
    have h4 : (x + 8) / sqrt (x - 1) ≥ 6 := by
      have hx2 : 0 < x - 1 := by
        linarith
      have h3 : 0 < sqrt (x - 1) := by
        apply Real.sqrt_pos.mpr
        linarith
      have h5 : (x + 8) ≥ 6 * sqrt (x - 1) := by
        have h7 : sqrt (x - 1) ^ 2 = (x - 1) := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (x - 1), sq_nonneg (sqrt (x - 1) - 3), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      have h8 : (x + 8) / sqrt (x - 1) ≥ 6 := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith
      exact h8
    linarith [heq, h4]