import Mathlib

theorem number_theory_323859 {a b : ℕ} (ha : a = ∏ x ∈ (Nat.divisors 2005), x)
    (hb : b = ∏ x ∈ (Nat.divisors a), x) :
    b = 2005^9 := by
  have ha2 : a = 2005 ^ 2 := by
    rw [ha]
    native_decide
  rw [hb, ha2]
  native_decide