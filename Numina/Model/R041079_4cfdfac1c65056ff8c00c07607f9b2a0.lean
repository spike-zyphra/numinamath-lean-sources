import Mathlib

theorem algebra_162182 (p : ℝ) (h : ∃ r, 2 * p - 1 = r * (|p - 8|) ∧ 4 * p + 5 = r * (2 * p - 1)) :
    p = -1 ∨ p = 39 / 8 := by
  rcases h with ⟨r, h1, h2⟩
  by_cases h3 : p - 8 ≥ 0
  · -- case where p ≥ 8, so |p - 8| = p - 8
    have h4 : |p - 8| = p - 8 := by
      rw [abs_of_nonneg]
      linarith
    rw [h4] at h1
    by_cases h5 : p - 8 = 0
    · -- Case p = 8
      have hp8 : p = 8 := by linarith
      rw [hp8] at h1
      norm_num at h1
      all_goals nlinarith
    · -- Case p ≠ 8
      have hr : r = (2 * p - 1) / (p - 8) := by
        have hpne8 : p - 8 ≠ 0 := by
          intro h'
          apply h5
          linarith
        field_simp [hpne8]
        linarith [h1]
      have eq1 : 4 * p + 5 = r * (2 * p - 1) := h2
      rw [hr] at eq1
      have hpne8 : p - 8 ≠ 0 := by
        intro h'
        apply h5
        linarith
      field_simp [hpne8] at eq1
      nlinarith [sq_nonneg (p - 8), sq_nonneg (2 * p - 1)]
  · -- case where p < 8, so |p - 8| = 8 - p
    have h4 : |p - 8| = 8 - p := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [h4] at h1
    by_cases h5 : (8 - p : ℝ) = 0
    · -- Case p = 8, which contradicts as p < 8
      have hp8 : p = 8 := by linarith
      linarith
    · -- Case p ≠ 8
      have hr : r = (2 * p - 1) / (8 - p) := by
        have hpne8 : (8 - p : ℝ) ≠ 0 := by
          intro h'
          apply h5
          linarith
        field_simp [hpne8]
        linarith [h1]
      have eq1 : 4 * p + 5 = r * (2 * p - 1) := h2
      rw [hr] at eq1
      have hpne8 : (8 - p : ℝ) ≠ 0 := by
        intro h'
        apply h5
        linarith
      field_simp [hpne8] at eq1
      have h39 : (p + 1) * (p - 39 / 8) = 0 := by
        nlinarith [sq_nonneg (p - 8), sq_nonneg (2 * p - 1), sq_nonneg (p + 1), sq_nonneg (p - 39 / 8)]
      cases' (mul_eq_zero.1 h39) with hp1 hp2
      · left
        linarith
      · right
        linarith