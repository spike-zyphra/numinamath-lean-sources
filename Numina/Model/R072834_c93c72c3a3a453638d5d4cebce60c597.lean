import Mathlib

theorem inequalities_600682 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    9 * a * b * c ≤ a * b + b * c + c * a ∧
    a * b + b * c + c * a ≤ (1 + 9 * a * b * c) / 4 := by
  constructor
  · -- Proof of the first inequality: 9abc ≤ ab + bc + ca
    have h1 : c = 1 - a - b := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), 
           mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
           mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith)]
  · -- Proof of the second inequality: ab + bc + ca ≤ (1 + 9abc) / 4
    have h1 : c = 1 - a - b := by linarith
    rw [h1]
    have h2 : a * b + b * (1 - a - b) + (1 - a - b) * a ≤ (1 + 9 * a * b * (1 - a - b)) / 4 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
                 sq_nonneg (a + b - 1/2), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg (1 - a - b - 1/2),
                 mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith),
                 mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith),
                 sq_nonneg (a - b), sq_nonneg (a + b - 1/2), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b))]
    linarith