import Mathlib

theorem number_theory_62954 (a : Fin 19 → ℕ) (ha : ∀ i j k l, i ≠ j → k ≠ l → Nat.gcd (a i) (a j) - Nat.gcd (a k) (a l) < 180) :
    ∃ i j, a i = a j := by
  use 0, 0
  all_goals simp