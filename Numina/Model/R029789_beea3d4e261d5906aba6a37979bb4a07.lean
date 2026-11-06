import Mathlib
theorem algebra_607250 (a b c : ℝ) :
    2 * a ^ 2 + 20 * b ^ 2 + 5 * c ^ 2 + 8 * a * b - 4 * b * c - 4 * a * c ≥ 0 ∧
    (2 * a ^ 2 + 20 * b ^ 2 + 5 * c ^ 2 + 8 * a * b - 4 * b * c - 4 * a * c = 0 ↔
      (a = 0 ∧ b = 0 ∧ c = 0)):= by
  constructor
  · -- Prove the inequality ≥ 0
    nlinarith [sq_nonneg (a + 2 * b - c), sq_nonneg (b + c / 6), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c),
      sq_nonneg (2 * b - c)]
  · -- Prove the equality case
    constructor
    · -- Forward implication: if the expression is 0, then (a, b, c) = (0, 0, 0)
      intro heq
      have h1 : 2 * a ^ 2 + 20 * b ^ 2 + 5 * c ^ 2 + 8 * a * b - 4 * b * c - 4 * a * c ≥ 0 := by linarith
      have h2 : 2 * (a + 2 * b - c) ^ 2 + 12 * b ^ 2 + 4 * b * c + 3 * c ^ 2 = 0 := by
        nlinarith [heq]
      have h3 : (a + 2 * b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a + 2 * b - c), sq_nonneg (b + c / 6), sq_nonneg (c)]
      have h4 : a + 2 * b - c = 0 := by
        nlinarith
      have h5 : 12 * b ^ 2 + 4 * b * c + 3 * c ^ 2 = 0 := by
        nlinarith [h2, h3, sq_nonneg (a + 2 * b - c)]
      -- Now, from h4, c = a + 2b
      have h6 : c = a + 2 * b := by linarith
      rw [h6] at h5
      -- Now we have quadratic in terms of b and a
      have h7 : 3 * a ^ 2 + 16 * a * b + 32 * b ^ 2 = 0 := by
        nlinarith
      have h8 : b ^ 2 = 0 := by
        nlinarith [sq_nonneg (a + 8 * b / 3), sq_nonneg (b), sq_nonneg (a), sq_nonneg (b + c / 6)]
      have hb : b = 0 := by
        nlinarith
      have ha : a = 0 := by
        nlinarith [hb]
      have hc : c = 0 := by
        nlinarith [ha, hb, h6]
      exact ⟨ha, hb, hc⟩
    · -- Reverse implication: (a, b, c) = (0, 0, 0) implies the expression is 0
      rintro ⟨ha, hb, hc⟩
      rw [ha, hb, hc]
      norm_num