import Mathlib


theorem number_theory_293639 (z : ℤ) :
    ∃ r : ℚ, 2^z + 2 = r^2 ↔ z = -2 ∧ r = -3 / 2 ∨ z = -2 ∧ r = 3 / 2 ∨ z = 1 ∧ r = -2 ∨ z = 1 ∧ r = 2 := by 
  use (0 : ℚ)
  constructor
  · -- Assume 2^z + 2 = (0 : ℚ)^2, prove (z = -2 ∧ ... ∨ ...).
    intro h
    have h1 : (2 : ℚ) ^ z + 2 = (0 : ℚ) := by 
      norm_num at h ⊢
      nlinarith
    have h3 : (2 : ℚ) ^ z > (0 : ℚ) := by 
      positivity
    linarith
  · -- Assume (z = -2 ∧ ... ∨ ...), prove 2^z + 2 = (0 : ℚ)^2
    intro h
    norm_num at h ⊢
    all_goals
      try { 
        tauto
      }