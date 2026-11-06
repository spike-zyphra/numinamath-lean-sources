import Mathlib

theorem number_theory_86472 (a b : ℕ) :
    (Nat.factorial a * Nat.factorial b) ∣ Nat.factorial (a + b) := by
  apply Nat.factorial_mul_factorial_dvd_factorial_add