import Mathlib

theorem algebra_162036 (p : ℝ) (h : ∃ r, 2 * p = r * (4 * p + 5) ∧ |p - 3| = r * 2 * p) :
    p = -1 ∨ p = 15 / 8 := by
  rcases h with ⟨r, h1, h2⟩
  by_cases h3 : p - 3 ≥ 0
  · -- p - 3 ≥ 0, so |p - 3| = p - 3
    have h4 : p ≥ 3 := by linarith
    have h5 : |p - 3| = p - 3 := by
      rw [abs_of_nonneg h3]
    rw [h5] at h2
    by_cases hp0 : p = 0
    · -- p = 0
      rw [hp0] at h1 h2
      norm_num at h1 h2
      all_goals linarith
    -- p ≠ 0
    have hpne : p ≠ 0 := by
      by_contra hp0
      rw [hp0] at h1 h2
      norm_num at h1 h2
    have h6 : r = (p - 3) / (2 * p) := by
      field_simp [hpne]
      linarith
    rw [h6] at h1
    have h8 : 2 * p * (2 * p) = (p - 3) * (4 * p + 5) := by
      field_simp [hpne] at h1
      nlinarith
    nlinarith
  · -- p - 3 < 0, so |p - 3| = 3 - p
    have h4 : p < 3 := by linarith
    have h5 : |p - 3| = 3 - p := by
      rw [abs_of_neg (show p - 3 < 0 by linarith)]
      all_goals linarith
    rw [h5] at h2
    by_cases hp0 : p = 0
    · -- p = 0
      rw [hp0] at h1 h2
      norm_num at h1 h2
      all_goals linarith
    -- p ≠ 0
    have hpne : p ≠ 0 := by
      by_contra hp0
      rw [hp0] at h1 h2
      norm_num at h1 h2
    have h7 : r = (3 - p) / (2 * p) := by
      field_simp [hpne]
      linarith
    rw [h7] at h1
    have h8 : 2 * p * (2 * p) = (3 - p) * (4 * p + 5) := by
      field_simp [hpne] at h1
      nlinarith
    have h9 : (p + 1) * (p - 15 / 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- p + 1 = 0
      left
      linarith
    · -- p - 15 / 8 = 0
      right
      linarith