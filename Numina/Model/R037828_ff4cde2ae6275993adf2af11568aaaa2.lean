import Mathlib

theorem number_theory_175575 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    IsSquare (5000 + n) ∧ IsSquare (n * 10 + 1) ↔ n = 476 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₀, h₀₁⟩
  constructor
  · -- Assume both conditions hold
    rintro ⟨h1, h2⟩
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    have h4 : a ≤ 77 := by
      nlinarith
    have h5 : a ≥ 71 := by
      nlinarith
    have h7 : b ≤ 99 := by
      nlinarith
    have h8 : b ≥ 32 := by
      nlinarith
    interval_cases a <;> try { 
      omega 
    } 
    <;> try { 
      interval_cases b <;> omega 
    }
  · -- Assume n = 476 and prove both conditions
    intro h
    rw [h]
    constructor
    · -- Show that 5000 + 476 is a perfect square
      native_decide
    · -- Show that 476 * 10 + 1 is a perfect square
      native_decide