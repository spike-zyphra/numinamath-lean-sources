import Mathlib

theorem algebra_14588 (P : ℝ × ℝ) (hP : P = (4, 3)) (r : ℝ) (hr : r = 10) :
    IsGreatest {d | ∃ x y, d = Real.sqrt (x^2 + y^2) ∧ (x - P.1)^2 + (y - P.2)^2 ≤ r^2} 15 := by
  subst_vars
  constructor
  · -- Show that 15 is in the set
    use 12, 9
    have h1 : Real.sqrt ((12 : ℝ) ^ 2 + (9 : ℝ) ^ 2) = 15 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      all_goals norm_num
      all_goals norm_num
      all_goals norm_num
      all_goals norm_num
    constructor
    · -- Show that distance is 15
      rw [h1]
      all_goals norm_num
    · -- Show that constraint is satisfied
      norm_num
  · -- Show that 15 is greatest in the set
    intro d hd
    rcases hd with ⟨x, y, h_eq, h_ineq⟩
    have h1 : (x - (4 : ℝ)) ^ 2 + (y - (3 : ℝ)) ^ 2 ≤ (10 : ℝ) ^ 2 := by
      simpa using h_ineq
    have h2 : Real.sqrt (x ^ 2 + y ^ 2) ≤ 15 := by
      have h3 : x ^ 2 + y ^ 2 ≤ 225 := by
        nlinarith [sq_nonneg (x - 12), sq_nonneg (y - 9),
                  sq_nonneg (x * 3 - y * 4), sq_nonneg (y * 4 - x * 3),
                  sq_nonneg (x + y), sq_nonneg (x - 4 * x), sq_nonneg (y - 4 * y), sq_nonneg (3 * x - 4 * y)]
      have h4 : Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (225: ℝ) := Real.sqrt_le_sqrt (by linarith [h3])
      have h7 : Real.sqrt (225: ℝ) = 15 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [h7, h4]
    rw [h_eq]
    nlinarith [h2]
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num