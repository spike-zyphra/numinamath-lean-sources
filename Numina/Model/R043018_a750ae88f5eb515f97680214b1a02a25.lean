import Mathlib

theorem inequalities_602589 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    9 * a * b * c ≤ a * b + b * c + c * a ∧
    a * b + b * c + c * a ≤ (1 / 4) * (1 + 9 * a * b * c) := by
  constructor
  · -- Prove that 9 * a * b * c ≤ a * b + b * c + c * a
    have h1 : c = 1 - a - b := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
      mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - a - b by nlinarith),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a - b by nlinarith)]
  · -- Prove that a * b + b * c + c * a ≤ (1 / 4) * (1 + 9 * a * b * c)
    have h1 : c = 1 - a - b := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
      sq_nonneg (a + b - 1/2), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), 
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
      mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - a - b by nlinarith), 
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a - b by nlinarith)]