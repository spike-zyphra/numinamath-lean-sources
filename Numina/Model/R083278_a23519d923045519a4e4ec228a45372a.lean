import Mathlib

theorem number_theory_43420 (a b : ℕ) (_ : 0 < a) (hb : 0 < b) :
    19 ∣ 11 * a + 2 * b ↔ 19 ∣ 18 * a + 5 * b := by 
  constructor
  · -- Assume 19 divides 11a + 2b, prove 19 divides 18a + 5b
    intro h
    omega
  · -- Assume 19 divides 18a + 5b, prove 19 divides 11a + 2b
    intro h
    omega