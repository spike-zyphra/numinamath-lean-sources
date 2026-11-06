import Mathlib

theorem number_theory_304392 :
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x + y^2 + (Nat.gcd x y)^3 = x * y * Nat.gcd x y := by
  exact ⟨4, 6, by norm_num, by norm_num, by norm_num⟩