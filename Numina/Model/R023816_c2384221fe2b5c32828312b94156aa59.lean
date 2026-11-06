import Mathlib

open Real

theorem inequalities_328457 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 2 - sqrt (a * b) ≥ sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 ∧
    sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 ≥ sqrt (a * b) - 2 * a * b / (a + b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
  have h3 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)
  have h4 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ sqrt (a * b) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  constructor
  · -- Prove first inequality
    have h5 : (a + b) / 2 - sqrt (a * b) ≥ sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 := by
      nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2),
        Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity),
        sq_nonneg (a - b), sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)), sq_nonneg (a + b - 2 * sqrt (a * b)), sq_nonneg (a + b - 2 * sqrt ((a ^ 2 + b ^ 2) / 2)), mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)
      ]
    linarith
  · -- Prove second inequality
    have h7 : 0 < a + b := by linarith
    have h8 : 0 < (a + b) := by linarith
    have h11 : sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) ≥ sqrt (a * b) * (a + b) + (a - b) ^ 2 / 2 := by
      nlinarith [sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - sqrt (a * b) ^ 2), sq_nonneg (a - b), sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)), Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)), mul_pos ha hb, sq_nonneg (a - b)]
    have h12 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 ≥ sqrt (a * b) - 2 * a * b / (a + b) := by
      have h13 : 0 < (a + b) := by linarith
      have h14 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 - (sqrt (a * b) - 2 * a * b / (a + b)) ≥ 0 := by
        have h15 : sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (sqrt (a * b) * (a + b) + (a - b) ^ 2 / 2) ≥ 0 := by
          linarith [h11]
        have h16 : (sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (sqrt (a * b) * (a + b) + (a - b) ^ 2 / 2)) / (a + b) ≥ 0 := by
          apply div_nonneg
          linarith [h15]
          linarith
        have h17 : sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / 2 - (sqrt (a * b) - 2 * a * b / (a + b)) = (sqrt ((a ^ 2 + b ^ 2) / 2) * (a + b) - (sqrt (a * b) * (a + b) + (a - b) ^ 2 / 2)) / (a + b) := by
          field_simp
          <;> ring_nf
          <;> field_simp
        rw [h17]
        all_goals nlinarith [h16]
      nlinarith
    linarith