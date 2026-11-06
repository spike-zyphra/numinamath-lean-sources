import Mathlib

theorem algebra_164941 :
  {x : ℝ | x ≤ 3 ∧ x ≥ 2 ∧ Real.sqrt (x - 2) + Real.sqrt (3 - x) = x ^ 2 - 5 * x + 7} = {2, 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x in {x | x ≤ 3 ∧ x ≥ 2 ∧ Real.sqrt (x - 2) + Real.sqrt (3 - x) = x ^ 2 - 5 * x + 7}
    rintro ⟨hx1, hx2, heq⟩
    have h1 : x ≤ 3 := hx1
    have h2 : x ≥ 2 := hx2
    have h3 : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
    have h4 : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
    have h5 : Real.sqrt (x - 2) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h6 : Real.sqrt (3 - x) ^ 2 = 3 - x := by
      rw [Real.sq_sqrt]
      linarith
    by_cases h : x < 2.5
    · -- Assume x < 2.5
      have h7 : x < (2.5 : ℝ) := h
      have h8 : x = 2 := by
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (3 - x),
          sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (3 - x) - 1),
          Real.sq_sqrt (show x - 2 ≥ 0 by linarith),
          Real.sq_sqrt (show 3 - x ≥ 0 by linarith),
          mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (3 - x)),
          sq_nonneg (x - 2), sq_nonneg (x - 3)]
      left
      linarith
    · -- Assume x ≥ 2.5
      have h8 : x ≥ (2.5 : ℝ) := by linarith
      by_cases h8 : x < 3
      · -- Assume x < 3
        have h7 : x < (3 : ℝ) := h8
        -- Show contradiction
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (3 - x),
          sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (3 - x) - 1),
          Real.sq_sqrt (show x - 2 ≥ 0 by linarith),
          Real.sq_sqrt (show 3 - x ≥ 0 by linarith),
          mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (3 - x)),
          sq_nonneg (x - 2), sq_nonneg (x - 3)]
      · -- Assume x = 3
        have h9 : x = (3 : ℝ) := by linarith
        right
        linarith
  · -- Show that 2 and 3 are in the left side.
    rintro (h | h)
    · -- Assume x = 2
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Verify $\sqrt{2-2}+\sqrt{3-2}=2^2-5 \cdot 2+7$.
        have h1 : Real.sqrt (2 - 2 : ℝ) = 0 := by
          rw [Real.sqrt_eq_zero']
          all_goals norm_num
        have h2 : Real.sqrt (3 - (2 : ℝ)) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1, h2]
        all_goals norm_num
    · -- Assume x = 3
      rw [h]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Verify $\sqrt{3-2}+\sqrt{3-3}=3^2-5 \cdot 3+7$.
        have h1 : Real.sqrt (3 - 2 : ℝ) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : Real.sqrt (3 - 3 : ℝ) = 0 := by
          rw [Real.sqrt_eq_zero']
          all_goals norm_num
        rw [h1, h2]
        all_goals norm_num