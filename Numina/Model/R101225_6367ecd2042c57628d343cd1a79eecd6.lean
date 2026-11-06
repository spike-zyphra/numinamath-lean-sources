import Mathlib

theorem inequalities_276811 (a b : ℝ) (h₀ : |a| < b) : -b < a ∧ a < b := by
  cases' abs_cases a with ha ha
  · -- Case where a ≥ 0: in this case |a| = a
    constructor
    · linarith 
    · linarith 
  · -- Case where a < 0: in this case |a| = -a
    constructor
    · linarith
    · linarith