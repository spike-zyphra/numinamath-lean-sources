import Mathlib

open Real Set

theorem calculus_18606 :
  IsLeast {d | ∃ P Q : EuclideanSpace ℝ (Fin 3), d = dist P Q ∧ P 1 = -P 0 + 1 ∧ P 2 = 0 ∧ Q 2 = -2 * Q 0 + 1 ∧ Q 1 = 0} (1 / 3) := by
  constructor
  · -- Show that 1/3 is in the set
    use ![7 / 9, 2 / 9, (0 : ℝ)]
    use ![5 / 9, (0 : ℝ), -1 / 9]
    constructor
    · -- Show that 1/3 = dist P Q
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      have h1 : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      linarith [h1]
    all_goals norm_num
  · -- Show that 1/3 is the least element in the set
    intro d
    intro h
    rcases h with ⟨P, Q, h_eq, hp1, hp2, hq1, hq0⟩
    have h2 : dist P Q ≥ 1 / 3 := by
      have h3 : dist P Q = Real.sqrt (∑ i : Fin 3, (P i - Q i) ^ 2) := by
        simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      rw [h3]
      have h4 : ∑ i : Fin 3, (P i - Q i) ^ 2 ≥ (1 / 9 : ℝ) := by
        have h5 : P 1 = -P 0 + 1 := hp1
        have h6 : P 2 = (0 : ℝ) := hp2
        have h7 : Q 2 = -2 * Q 0 + 1 := hq1
        have h8 : Q 1 = (0 : ℝ) := hq0
        have h9 : ∑ i : Fin 3, (P i - Q i) ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 + (P 2 - Q 2) ^ 2 := by
          simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        rw [h9]
        rw [h5, h6, h7, h8]
        nlinarith [sq_nonneg (P 0 - 7 / 9 : ℝ), sq_nonneg (Q 0 - 5 / 9 : ℝ), sq_nonneg (P 0 - 2 * Q 0), sq_nonneg ((P 0 : ℝ) - (Q 0 : ℝ)), sq_nonneg ((P 0 : ℝ) - 7 / 9), sq_nonneg ((Q 0 : ℝ) - 5 / 9)]
      have h14 : Real.sqrt (∑ i : Fin 3, (P i - Q i) ^ 2) ≥ Real.sqrt (1 / 9 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h15 : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      linarith [h14, h15]
    linarith [h_eq, h2]