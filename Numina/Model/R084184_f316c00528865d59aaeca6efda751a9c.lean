import Mathlib

theorem algebra_14446 (a b c d : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : b ≠ c) (h₄ : b ≠ d) (h₅ : c ≠ d) (h₆ : a ≤ 3) (h₇ : b ≤ 3) (h₈ : c ≤ 3) (h₉ : d ≤ 3) :
    c * a ^ b - d ≤ 9 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega