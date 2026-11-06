import Mathlib

open Real Set

theorem algebra_189822 (m : ℝ) (hm : m > 0) :
    m^(m^2) > (m^m)^2 ↔ (0 < m ∧ m < 1) ∨ (2 < m) := by
  constructor
  · -- Assume m^(m ^2) > (m ^ m) ^2, prove (0 < m ∧ m < 1) ∨ (2 < m)
    intro h
    have h1 : (m ^ m) ^ 2 = m ^ (2 * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring
      all_goals linarith
    rw [h1] at h
    by_cases h2 : m < 1
    · -- 0 < m < 1
      have h3 : m ^ 2 < (2 * m) := by
        by_contra h9
        push_neg at h9
        have h9' : m ^ (m ^ 2) ≤ m ^ (2 * m) := by
          apply Real.rpow_le_rpow_of_exponent_ge
          all_goals nlinarith
        linarith
      have h4 : 0 < m := hm
      left
      constructor <;> linarith
    · -- m ≥ 1
      have h2' : m ≥ (1 : ℝ) := by linarith
      by_cases h3 : m > (2 : ℝ)
      · -- m > 2
        right
        linarith
      · -- 1 ≤ m ≤ 2
        have h4 : m ≤ (2 : ℝ) := by linarith
        have h5 : m ^ (m ^ 2) ≤ m ^ (2 * m) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals nlinarith [sq_nonneg (m - 1), sq_nonneg (m - 2)]
        linarith
  · -- Assume (0 < m ∧ m < 1) ∨ (2 < m), prove m^(m^2) > (m^m)^2
    rintro (h | h)
    · -- 0 < m ∧ m < 1
      rcases h with ⟨h1, h2⟩
      have h1' : (m ^ m) ^ 2 = m ^ (2 * m) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring
        all_goals linarith
      rw [h1']
      have h3 : m ^ 2 < (2 * m) := by nlinarith
      have h4 : m ^ (m ^ 2) > m ^ (2 * m) := by
        have h5 : m < (1 : ℝ) := by linarith
        have h6 : m > (0 : ℝ) := by linarith
        -- apply the strict antitone of the rpow
        have h7 : m ^ (m ^ 2) > m ^ (2 * m) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals nlinarith
        linarith
      linarith
    · -- 2 < m
      have h1' : (m ^ m) ^ 2 = m ^ (2 * m) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring
        all_goals linarith
      rw [h1']
      have h2 : m ^ 2 > (2 * m) := by nlinarith [sq_nonneg (m - 2)]
      have h3 : m ^ (m ^ 2) > m ^ (2 * m) := by
        have h4 : m > (1 : ℝ) := by linarith
        -- apply the strict mono of the rpow
        have h6 : m ^ (m ^ 2) > m ^ (2 * m) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals nlinarith
        linarith
      linarith