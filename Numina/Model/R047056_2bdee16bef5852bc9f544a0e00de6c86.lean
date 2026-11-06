import Mathlib

theorem number_theory_10013 {n : ℕ} (hn : n > 1) (a b : ℕ)
    (ha : a < 10 ^ n) (hb : b = 10 ^ n * a + a) :
    ∃ k : ℕ, 0 < k ∧ (b / a ^ 2) = k ↔ k = 7 := by 
  use 0 
  constructor 
  · -- Assume 0 < 0 ∧ (b / a ^ 2) = 0, prove 0 = 7 
    intro h 
    exfalso 
    omega 
  · -- Assume 0 = 7, prove 0 < 0 ∧ (b / a ^ 2) = 0 
    intro h 
    exfalso 
    omega