import Mathlib

open Real

theorem algebra_156823 :
    {x : ℝ | x > 0 ∧ x ^ (logb 10 x) = 100 * x} = {100, 0.1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x > 0 ∧ x ^ (logb 10 x) = 100 * x, prove x = 100 ∨ x = 0.1
    intro h
    rcases h with ⟨hx_pos, heq⟩
    have h1 : logb 10 (x ^ (logb 10 x)) = logb 10 (100 * x) := by
      rw [heq]
    have h2 : logb 10 (x ^ (logb 10 x)) = logb 10 x * (logb 10 x) := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h3 : logb 10 (100 * x) = logb 10 (100 : ℝ) + logb 10 x := by
      rw [logb_mul (by norm_num) (by linarith)]
    have h4 : logb 10 (100 : ℝ) = (2 : ℝ) := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2, h3, h4] at h1
    have h5 : (logb 10 x - 2) * (logb 10 x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where $\log_{10} x = 2$
      have h8 : logb 10 x = (2 : ℝ) := by linarith
      have h9 : x = (10 : ℝ) ^ (logb 10 x) := by
        field_simp at *
        all_goals linarith
      rw [h8] at h9
      have h10 : x = (100 : ℝ) := by
        norm_num at h9 ⊢
        linarith
      left
      norm_num at h10 ⊢
      linarith
    · -- Case where $\log_{10} x = -1$
      have h11 : logb 10 x = (-1 : ℝ) := by linarith
      have h12 : x = (10 : ℝ) ^ (logb 10 x) := by
        field_simp at *
        all_goals linarith
      rw [h11] at h12
      have h13 : x = (0.1 : ℝ) := by
        rw [h12]
        norm_num
      right
      rw [h13]
      all_goals norm_num
  · -- Assume x = 100 ∨ x = 0.1, prove x > 0 ∧ x ^ (logb 10 x) = 100 * x
    rintro (h | h)
    · -- Case x = 100
      rw [h]
      constructor
      · norm_num
      · -- Check that 100^(logb 10 100) = 100 * 100
        have h4 : logb 10 (100 : ℝ) = (2 : ℝ) := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4]
        norm_num
    · -- Case x = 0.1
      rw [h]
      constructor
      · norm_num
      · -- Check that 0.1^(logb 10 0.1) = 100 * 0.1
        have h4 : logb 10 (0.1 : ℝ) = (-1 : ℝ) := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4]
        norm_num