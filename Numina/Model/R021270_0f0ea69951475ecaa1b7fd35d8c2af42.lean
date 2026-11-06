import Mathlib

open Real
open scoped BigOperators

theorem inequalities_245567 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  (O P : ℝ) (hO : O = 2 * (a + b)) (hP : P = a * b) :
  O ≥ 24 * P / (O + P + 1) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < O + P + 1 := by
    rw [hO, hP]
    nlinarith [mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h3 : O ≥ 24 * P / (O + P + 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    -- Show $O \cdot (O + P + 1) \geq 24 \cdot P$.
    rw [hO, hP]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b - 2),
      sq_nonneg (2 * (a + b) - 4), sq_nonneg ((a * b) - 1), mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a * b - (a + b)), sq_nonneg (a * b - 1)]
  linarith