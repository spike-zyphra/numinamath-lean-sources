import Mathlib

theorem inequalities_58130 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    2 ≤ (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2 ∧
    (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2 ≤ (1 + a) * (1 + b) * (1 + c) := by 
  have hc' : c = 1 - a - b := by linarith
  rw [hc']
  constructor
  · -- Prove 2 ≤ (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - (1 - a - b) ^ 2) ^ 2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            mul_nonneg ha hb, mul_nonneg ha (show 0 ≤ (1 - a - b : ℝ) by nlinarith), 
            mul_nonneg hb (show 0 ≤ (1 - a - b : ℝ) by nlinarith)]
  · -- Prove (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - (1 - a - b) ^ 2) ^ 2 ≤ (1 + a) * (1 + b) * (1 + (1 - a - b))
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            mul_nonneg ha hb, mul_nonneg ha (show 0 ≤ (1 - a - b : ℝ) by nlinarith), 
            mul_nonneg hb (show 0 ≤ (1 - a - b : ℝ) by nlinarith)]