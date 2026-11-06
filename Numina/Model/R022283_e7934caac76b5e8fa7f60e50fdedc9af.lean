import Mathlib

theorem number_theory_274479 (a b : ℤ) (ha : a % 4 = 0) (hb : b % 4 = 0) :
    Even ((a + b) / 2) := by 
  have h5 : ∃ k, a = 4 * k := by 
    refine' ⟨a / 4, by omega⟩
  rcases h5 with ⟨k, h6⟩
  have h7 : ∃ m, b = 4 * m := by 
    refine' ⟨b / 4, by omega⟩
  rcases h7 with ⟨m, h8⟩
  have h9 : (a + b) / 2 = 2 * (k + m) := by 
    rw [h6, h8]
    omega
  rw [h9]
  exact ⟨k + m, by ring⟩