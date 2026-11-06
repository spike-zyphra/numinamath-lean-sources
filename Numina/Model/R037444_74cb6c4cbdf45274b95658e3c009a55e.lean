import Mathlib

theorem number_theory_113462 {a b : ℕ} (ha : a > b) (hb : 0 < b) :
    Nat.gcd a b = Nat.gcd b (a % b) := by 
  rw [show Nat.gcd a b = Nat.gcd b (a % b) by 
    rw [Nat.gcd_comm a b]
    rw [Nat.gcd_comm b (a % b)]
    apply Nat.gcd_rec
  ]