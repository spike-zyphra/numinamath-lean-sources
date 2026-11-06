import Mathlib

open Real

theorem inequalities_202625 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b)^2 / (2 * (a + b)) ≤ sqrt ((a^2 + b^2) / 2) - sqrt (a * b) ∧
    sqrt ((a^2 + b^2) / 2) - sqrt (a * b) ≤ (a - b)^2 / (a + b) := by
  have hab : 0 < a * b := mul_pos ha hb
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have h1 : (a ^ 2 + b ^ 2) / 2 ≥ 0 := by positivity
  have h2 : (a * b) ≥ 0 := by positivity
  have h3 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ sqrt (a * b) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (a - b)]
  have h9 : sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b) ≥ 0 := by linarith
  constructor
  · -- Prove the left inequality: (a - b)^2 / (2 * (a + b)) ≤ sqrt ((a^2 + b^2) / 2) - sqrt (a * b)
    have h10 : (a - b) ^ 2 / (2 * (a + b)) ≤ sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b) := by
      have h11 : 0 < 2 * (a + b) := by nlinarith
      have h14 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≥ (a - b) ^ 2 / (2 * (a + b)) := by
        have h15 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (2 * (a + b)) ≥ (a - b) ^ 2 := by
          have h16 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (2 * (a + b)) =
              2 * (a + b) * sqrt ((a ^ 2 + b ^ 2) / 2) - 2 * (a + b) * sqrt (a * b) := by ring
          rw [h16]
          nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity), 
            Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
            sq_nonneg (a - b), 
            sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)), 
            mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)) (Real.sqrt_nonneg (a * b)), 
            sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - (a ^ 2 + b ^ 2) / 2), 
            sq_nonneg (sqrt (a * b) ^ 2 - (a * b)), 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
          ]
        have h180 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≥ (a - b) ^ 2 / (2 * (a + b)) := by
          have h100 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (2 * (a + b)) ≥ (a - b) ^ 2 := h15
          have h181 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≥ (a - b) ^ 2 / (2 * (a + b)) := by
            apply (div_le_iff₀ (by positivity)).mpr
            linarith
          linarith
        linarith
      linarith
    linarith
  · -- Prove the right inequality: sqrt ((a^2 + b^2) / 2) - sqrt (a * b) ≤ (a - b)^2 / (a + b)
    have h17 : sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b) ≤ (a - b) ^ 2 / (a + b) := by
      have h18 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≤ (a - b) ^ 2 / (a + b) := by
        have h100 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (a + b) ≤ (a - b) ^ 2 := by
          have h101 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (a + b) =
              (a + b) * sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) * sqrt (a * b) := by ring
          rw [h101]
          nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity), 
            Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
            sq_nonneg (a - b), sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)), 
            mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)) (Real.sqrt_nonneg (a * b)), 
            sq_nonneg (sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - (a ^ 2 + b ^ 2) / 2), 
            sq_nonneg (sqrt (a * b) ^ 2 - (a * b)), 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
          ]
        have h181 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≤ (a - b) ^ 2 / (a + b) := by
          have h182 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) * (a + b) ≤ (a - b) ^ 2 := h100
          have h183 : (sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b)) ≤ (a - b) ^ 2 / (a + b) := by
            apply (le_div_iff₀ (by positivity)).mpr
            linarith
          linarith
        linarith
      linarith
    linarith