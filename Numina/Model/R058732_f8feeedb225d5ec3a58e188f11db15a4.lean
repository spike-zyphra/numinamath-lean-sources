import Mathlib

theorem inequalities_325980 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    0 ≤ a * b + b * c + c * a - 2 * a * b * c ∧ a * b + b * c + c * a - 2 * a * b * c ≤ 7 / 27 := by
  constructor
  · -- Prove the left part of the conjunction: $0 \leq ab + bc + ca - 2abc$
    have h1 : c = 1 - a - b := by linarith 
    rw [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), sq_nonneg (a), sq_nonneg (b), sq_nonneg (1 - a - b)]
  
  · -- Prove the right part of the conjunction: $ab + bc + ca - 2abc \leq 7/27$
    have h1 : c = 1 - a - b := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ((1 - a - b) - 1/3), mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), sq_nonneg (a), sq_nonneg (b), sq_nonneg (1 - a - b)]