import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_109485 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  (h : a + b + c = 3) :
  9 ≤ 2*(a^2+b^2+c^2)+3*a*b*c ∧
  2*(a^2+b^2+c^2)+3*a*b*c ≤ 18 := by 
  have h1 : c = 3 - a - b := by linarith
  constructor 
  · -- Prove the lower bound 
    rw [show c = 3 - a - b by linarith [h1]]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)), 
      sq_nonneg (a + b - (3 - a - b)), 
      mul_nonneg ha hb, mul_nonneg ha (show (0 : ℝ) ≤ (3 - a - b) by nlinarith), 
      mul_nonneg (show (0 : ℝ) ≤ (3 - a - b) by nlinarith) hb, 
      mul_nonneg (show (0 : ℝ) ≤ (3 - a - b) by nlinarith) (show (0 : ℝ) ≤ (3 - a - b) by nlinarith), 
      sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg ((3 - a - b) - 0)
    ]
  · -- Prove the upper bound 
    rw [show c = 3 - a - b by linarith [h1]]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)), 
      sq_nonneg (a + b - (3 - a - b)), 
      mul_nonneg ha hb, mul_nonneg ha (show (0 : ℝ) ≤ (3 - a - b) by nlinarith), 
      mul_nonneg (show (0 : ℝ) ≤ (3 - a - b) by nlinarith) hb, 
      mul_nonneg (show (0 : ℝ) ≤ (3 - a - b) by nlinarith) (show (0 : ℝ) ≤ (3 - a - b) by nlinarith), 
      sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg ((3 - a - b) - 0), 
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ (3 - a - b) by nlinarith), 
      mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ (3 - a - b) by nlinarith)
    ]