import Mathlib

theorem number_theory_202102 (A B C D : ℕ) (h₀ : 1 ≤ A) (h₁ : A ≤ 9) (h₂ : 0 ≤ B) (h₃ : B ≤ 9)
    (h₄ : 1 ≤ C) (h₅ : C ≤ 9) (h₆ : 0 ≤ D) (h₇ : D ≤ 9) :
    1000 * A + 100 * B + 10 * C + D = (10 * A + B) * (C * 10 + D) + (10 * A + B) ^ 2 ↔
    (1296 = 1000 * A + 100 * B + 10 * C + D ∨ 3468 = 1000 * A + 100 * B + 10 * C + D) := by
  constructor
  · -- Forward implication
    intro h
    have h2 : A ≤ 9 := h₁
    have h3 : B ≤ 9 := h₃
    have h4 : C ≤ 9 := h₅
    have h5 : D ≤ 9 := h₇
    interval_cases A <;> interval_cases B <;> interval_cases C <;> omega
  · -- Backward implication
    rintro (h | h)
    · -- Case 1: 1296 = ... 
      have h1 : 1000 * A + 100 * B + 10 * C + D = 1296 := by 
        omega
      have h2 : (10 * A + B) * (C * 10 + D) + (10 * A + B) ^ 2 = 1296 := by 
        have h6 : A = 1 := by
          omega
        have h7 : B = 2 := by
          omega
        have h8 : C = 9 := by
          omega
        have h9 : D = 6 := by
          omega
        simp [h6, h7, h8, h9]
      omega
    · -- Case 2: 3468 = ... 
      have h1 : 1000 * A + 100 * B + 10 * C + D = 3468 := by 
        omega
      have h2 : (10 * A + B) * (C * 10 + D) + (10 * A + B) ^ 2 = 3468 := by 
        have h6 : A = 3 := by
          omega
        have h7 : B = 4 := by
          omega
        have h8 : C = 6 := by
          omega
        have h9 : D = 8 := by
          omega
        simp [h6, h7, h8, h9]
      omega