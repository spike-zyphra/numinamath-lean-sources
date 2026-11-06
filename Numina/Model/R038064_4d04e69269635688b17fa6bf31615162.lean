import Mathlib

theorem inequalities_605334 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    11 * a * b ≤ a ^ 3 - b ^ 3 ∧ a ^ 3 - b ^ 3 ≤ 12 * a * b ↔ (a, b) = (5, 2) := by
  constructor
  · -- Forward implication: if (a, b) satisfies both inequalities, then (a, b) = (5, 2).
    rintro ⟨h1, h2⟩
    have h3 : a > b := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - 3 * b), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
    have h4 : a - b < 4 := by
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - 5 * b), sq_nonneg (a - 5), sq_nonneg (b - 2), sq_nonneg (a - 2), sq_nonneg (b - 5), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
    have h5 : a - b = 1 ∨ a - b = 2 ∨ a - b = 3 := by omega
    rcases h5 with (h5 | h5 | h5)
    · -- Case a - b = 1.
      have h6 : a = b + 1 := by omega
      rw [h6] at h1 h2
      have h7 : b ≤ 2 := by
        nlinarith [sq_nonneg (b - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (b * (b - 1) : ℤ), sq_nonneg (b * (b - 2) : ℤ), sq_nonneg (b ^ 2 - 2 * b : ℤ), mul_pos (show 0 < (b : ℤ) by linarith) (show 0 < (b : ℤ) by linarith), mul_pos ha hb]
      interval_cases b <;> try { omega }
    · -- Case a - b = 2.
      have h6 : a = b + 2 := by omega
      rw [h6] at h1 h2
      have h7 : b ≤ 2 := by
        nlinarith [sq_nonneg (b - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (b * (b - 1) : ℤ), sq_nonneg (b * (b - 2) : ℤ), sq_nonneg (b ^ 2 - 2 * b : ℤ), mul_pos (show 0 < (b : ℤ) by linarith) (show 0 < (b : ℤ) by linarith), mul_pos ha hb]
      interval_cases b <;> try { omega }
    · -- Case a - b = 3.
      have h6 : a = b + 3 := by omega
      rw [h6] at h1 h2
      have h7 : b = 2 := by
        nlinarith [sq_nonneg (b - 2 : ℤ), sq_nonneg (b : ℤ), sq_nonneg (b * (b - 2) : ℤ), sq_nonneg (b ^ 2 - 4 : ℤ), sq_nonneg (b : ℤ), mul_pos ha hb, sq_nonneg (b ^ 2 - 4 * b : ℤ)]
      have h8 : a = 5 := by
        nlinarith
      simp [h8, h7]
  · -- Backward implication: if (a, b) = (5, 2), then both inequalities hold.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    · norm_num