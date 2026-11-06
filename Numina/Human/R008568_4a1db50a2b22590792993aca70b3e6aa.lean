import Mathlib

theorem number_theory_323859 {a b : ℕ} (ha : a = ∏ x ∈ (Nat.divisors 2005), x)
    (hb : b = ∏ x ∈ (Nat.divisors a), x) :
    b = 2005^9 := by 
  have a_eq : a = 2005^2 := by 
    rw [ha]
    native_decide
  rw [a_eq] at hb
  rw [hb]
  native_decide