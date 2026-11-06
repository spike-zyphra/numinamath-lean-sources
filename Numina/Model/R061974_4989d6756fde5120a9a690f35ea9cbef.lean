import Mathlib

theorem number_theory_116428 (a b c d : ℕ) (h₀ : a ≠ 0) (h₁ : a ≤ 9) (h₂ : b ≤ 9)
    (h₃ : c ≤ 9) (h₄ : d ≤ 9) (h₅ : a + b + c + d = 27) :
    297 ∣ (a * 1000 + b * 100 + c * 10 + d) + (d * 1000 + c * 100 + b * 10 + a) := by
  have h6 : (a * 1000 + b * 100 + c * 10 + d) + (d * 1000 + c * 100 + b * 10 + a) = 1001 * (a + d) + 110 * (b + c) := by
    ring
  rw [h6]
  have h7 : a + d = 27 - (b + c) := by
    omega
  rw [h7]
  omega