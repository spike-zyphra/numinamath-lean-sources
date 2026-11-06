import Mathlib

theorem number_theory_7627 (a b c d : ℕ) (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : d < 10)
    (h₄ : a ≠ b) (h₅ : a ≠ c) (h₆ : a ≠ d) (h₇ : b ≠ c) (h₈ : b ≠ d) (h₉ : c ≠ d)
    (h₁₀ : a * b * c * d = 2016) : a + b + c + d = 28 := by
  interval_cases a <;> interval_cases b 
  <;> try { 
      omega 
    }
  <;> interval_cases c <;> omega