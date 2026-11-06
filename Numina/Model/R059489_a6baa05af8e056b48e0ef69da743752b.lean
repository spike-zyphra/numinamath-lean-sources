import Mathlib

theorem number_theory_250816 (d1 d2 m1 m2 y1 y2 : ℕ)
    (h₀ : d1 < 10) (h₁ : d2 < 10) (h₂ : m1 < 10) (h₃ : m2 < 10)
    (h₄ : y1 < 100) (h₅ : y2 < 100) (h₆ : d1 = 6 * d2) (h₇ : m1 = m2)
    (h₈ : y1 = 1900 + (d1 * 100 + m1 * 10 + y1)) (h₉ : y2 = 1900 + (d2 * 100 + m2 * 10 + y2)) :
    y1 = 1900 ∧ m1 = 4 ∧ d1 = 1 := by 
  omega