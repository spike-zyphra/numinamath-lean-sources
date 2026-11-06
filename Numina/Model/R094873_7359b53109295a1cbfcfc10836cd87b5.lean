import Mathlib

theorem algebra_121147 (R E S : ℕ) (h : R + E + S = 60) (h' : 80 * R + 31 * E + 30 * S = 2013) :
    R = 4 ∧ E = 13 ∧ S = 43 := by
  have h4 : R = 4 := by 
    omega
  have h5 : E = 13 := by 
    omega
  have h6 : S = 43 := by
    omega
  exact ⟨h4, h5, h6⟩