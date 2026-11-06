import Mathlib

theorem algebra_305503 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^3 + b^3 = 1) :
    1 < a + b ∧ a + b ≤ 4 ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Prove that 1 < a + b
    nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a + b - 1),
      mul_pos ha hb, mul_pos ha ha, mul_pos hb hb, sq_nonneg (a - b), sq_nonneg (a + b), h]
  · -- Prove that a + b ≤ 4 ^ ((1 : ℝ) / 3)
    have h1 : (a + b) ^ 3 ≤ 4 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b - 1 / 4), sq_nonneg (a - b), mul_pos ha hb, mul_pos ha (show 0 < a^2 by positivity), mul_pos hb (show 0 < b^2 by positivity), sq_nonneg (a^3 - b^3), h, sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1)]
    have h2 : 4 ^ ((1 : ℝ) / 3) ≥ (a + b) := by
      have h3 : (a + b) ^ 3 ≤ (4 : ℝ) := h1
      have h4 : (4 : ℝ) ^ ((1 : ℝ) / 3) ≥ (a + b) := by
        have h5 : (4 ^ ((1 : ℝ) / 3) ) ^ 3 = (4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        nlinarith [sq_nonneg ((4 ^ ((1 : ℝ) / 3) ) - (a + b)), sq_nonneg ((4 ^ ((1 : ℝ) / 3) )^2 - (a + b) ^ 2), sq_nonneg ((4 ^ ((1 : ℝ) / 3) ) ^ 2 - (a + b)^2), Real.rpow_nonneg (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) (1 / 3)]
      linarith
    linarith