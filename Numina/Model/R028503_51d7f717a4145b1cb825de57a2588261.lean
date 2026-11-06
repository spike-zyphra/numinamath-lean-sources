import Mathlib

open Real Set

theorem algebra_11570 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x + 27) + sqrt (13 - x) + sqrt x) :
    IsGreatest {y | ∃x : ℝ, 0 ≤ x ∧ x ≤ 13 ∧ y = f x} 11 := by
  constructor
  · -- Show that 11 is attained, by x = 9
    use 9
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Calculate f(9)
      rw [hf]
      have h1 : sqrt (9 + 27) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (13 - 9) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : sqrt (9 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      simp [h1, h2, h3]
      all_goals linarith
  · -- Show that no greater value is in the set
    intro y hy
    rcases hy with ⟨x, hx1, hx2, hy⟩
    rw [hf] at hy
    have h3 : sqrt (x + 27) + sqrt (13 - x) + sqrt x ≤ 11 := by
      nlinarith [sq_nonneg (sqrt (x + 27) - 6), sq_nonneg (sqrt (13 - x) - 2), sq_nonneg (sqrt x - 3),
        Real.sqrt_nonneg (x + 27), Real.sqrt_nonneg (13 - x), Real.sqrt_nonneg x,
        Real.sq_sqrt (show (0 : ℝ) ≤ x + 27 by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ (13 - x : ℝ) by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith),
        mul_nonneg (Real.sqrt_nonneg (x + 27)) (Real.sqrt_nonneg (13 - x)),
        mul_nonneg (Real.sqrt_nonneg (x + 27)) (Real.sqrt_nonneg x),
        mul_nonneg (Real.sqrt_nonneg (13 - x)) (Real.sqrt_nonneg x),
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ x by linarith),
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith),
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (13 - x : ℝ) by linarith),
        Real.sqrt_le_sqrt (show (0 : ℝ) ≤ x + 27 by linarith)
      ]
    simp at hy
    nlinarith [h3, Real.sqrt_nonneg (x + 27), Real.sqrt_nonneg (13 - x), Real.sqrt_nonneg x]