import Mathlib

theorem inequalities_75739 (a b c : ℤ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    a * (a - 1) + b * (b - 1) + c * (c - 1) ≤ (a + b + c - 4) * (a + b + c - 5) + 4 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a + b + c - 6)]