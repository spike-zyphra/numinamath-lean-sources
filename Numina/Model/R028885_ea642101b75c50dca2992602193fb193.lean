import Mathlib

theorem number_theory_262315 (n : ℕ) :
    IsSquare (n + 100) ∧ IsSquare (n + 164) ↔ n = 125 := by
  constructor
  · -- Assume both n + 100 and n + 164 are squares, prove n = 125
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    have h_eq1 : a ^ 2 = n + 100 := by linarith
    have h_eq2 : b ^ 2 = n + 164 := by linarith
    have h_eq3 : b ^ 2 = a ^ 2 + 64 := by
      nlinarith
    have h1 : b > a := by
      by_contra h
      push_neg at h
      have h2 : b ≤ a := by linarith
      have : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg (b - a)]
      omega
    have h2 : b ≤ 32 := by
      nlinarith [sq_nonneg (b - a), sq_nonneg (b + a), h_eq3]
    have h3 : a ≤ 32 := by
      nlinarith [sq_nonneg (b - a), sq_nonneg (b + a), h_eq3]
    interval_cases a <;> try { 
      have hb2 : b ≤ 32 := by nlinarith
      interval_cases b <;> omega
    }
  · -- Assume n = 125, prove both n + 100 and n + 164 are squares
    intro h
    rw [h]
    constructor
    · -- Show 125 + 100 is a square
      native_decide
    · -- Show 125 + 164 is a square
      native_decide