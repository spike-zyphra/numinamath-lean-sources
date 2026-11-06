import Mathlib

theorem number_theory_318006 (x : ℤ) (h : x % 3 = 2 ∧ x % 5 = 3 ∧ x % 7 = 4) :
    ∃ k, x = 105 * k + 53 := by
  rcases h with ⟨h1, h2, h3⟩
  have h4 : x % 3 = 2 := h1
  have h5 : x % 5 = 3 := h2
  have h6 : x % 7 = 4 := h3
  have h7 : (x - 53) % 3 = 0 := by
    omega
  have h8 : (x - 53) % 5 = 0 := by
    omega
  have h9 : (x - 53) % 7 = 0 := by
    omega
  have h10 : (x - 53) % 105 = 0 := by 
    have h3_5 : (x - 53) % 3 = 0 := h7
    have h5_5 : (x - 53) % 5 = 0 := h8
    have h7_5 : (x - 53) % 7 = 0 := h9
    omega
  have h11 : ∃ k : ℤ, x - 53 = 105 * k := by 
    refine' ⟨(x - 53) / 105, by omega⟩
  rcases h11 with ⟨k, hk⟩
  use k
  linarith