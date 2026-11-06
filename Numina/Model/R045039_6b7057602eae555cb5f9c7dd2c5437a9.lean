import Mathlib

theorem number_theory_4556
    (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    Nat.lcm a b = a * b / Nat.gcd a b := by 
  have h1 : a > 0 := hab.1
  have h2 : b > 0 := hab.2
  have h3 : a * b = a * b := by rfl
  have h4 : Nat.gcd a b = Nat.gcd a b := by rfl
  have h5 : Nat.lcm a b = a * b / Nat.gcd a b := by 
    rfl
  exact h5