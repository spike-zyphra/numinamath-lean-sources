import Mathlib

theorem number_theory_190925 (a b c : ℕ) (h₀ : a ≠ 0) (h₁ : a ≤ 9) (h₂ : b ≤ 9) (h₃ : c ≤ 9)
    (h₄ : (10 * a + b) * (10 * c + c) * (100 * a + 10 * b + c) =
    100000 * a + 10000 * b + 1000 * c + 100 * a + 10 * b + c) :
    137 = 100 * a + 10 * b + c ∨ 911 = 100 * a + 10 * b + c := by
  have h5 : a ≤ 9 := h₁
  have h6 : b ≤ 9 := h₂
  have h7 : c ≤ 9 := h₃
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega