import Mathlib

theorem number_theory_22726 (b : ℕ) (hb₀ : b > 1) (hb₁ : b > 7)
    (hb₂ : 5 * Nat.ofDigits b [5, 2] = Nat.ofDigits b [7, 3, 1]) :
    b = 9 := by
  simp [Nat.ofDigits, Nat.mul_add, Nat.add_mul, pow_two] at hb₂
  nlinarith