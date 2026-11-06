import Mathlib

theorem number_theory_133405 (y : ℤ) :
    ∃ x : ℝ, ⌊(x + 23) / 8⌋ = y ∧ ⌊Real.sqrt x⌋ = y ↔ y = 4 := by
  use 16
  constructor
  · -- Assume both conditions hold, prove y = 4
    intro h
    rcases h with ⟨h1, h2⟩
    norm_num at h1 h2
    all_goals omega
  · -- Assume y = 4, prove both conditions hold
    intro h_eq
    rw [show y = 4 by linarith [h_eq]]
    constructor
    · -- Compute floor of (16 + 23) / 8
      norm_num [Int.floor_eq_iff]
    · -- Compute floor of Real.sqrt 16
      have h3 : Real.sqrt (16 : ℝ) = 4 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      norm_num [h3, Int.floor_eq_iff]