import Mathlib

theorem number_theory_211307 (a b c d : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : b ≠ c) (h₄ : b ≠ d) (h₅ : c ≠ d) (h₆ : 1000 * a + 100 * b + 10 * c + d +
    1000 * d + 100 * c + 10 * b + a = 10477) :
    a = 7 ∧ b = 4 ∧ c = 3 ∧ d = 0 := by
  have h7 : a ≤ 9 := by
    omega
  have h8 : b ≤ 9 := by
    omega
  have h9 : c ≤ 9 := by
    omega
  have h10 : d ≤ 9 := by
    omega
  have h11 : a ≤ 9 := by
    omega
  have h12 : b ≤ 9 := by
    omega
  have h13 : c ≤ 9 := by
    omega
  have h14 : d ≤ 9 := by
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega