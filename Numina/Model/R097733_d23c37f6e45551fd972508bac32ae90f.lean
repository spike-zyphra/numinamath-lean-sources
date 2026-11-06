import Mathlib

theorem number_theory_320539 : ¬∃ n, Odd n ∧ Odd (n + 2) ∧ Odd (n + 4) ∧ Odd (n + 6) ∧ n + (n + 2) + (n + 4) + (n + 6) = 100 := by 
  rintro ⟨n, ⟨h_odd_n, h_odd_n2, h_odd_n4, h_odd_n6, h_eq⟩⟩
  -- expand the sum 
  have h_eq' : 4 * n + 12 = 100 := by
    linarith [h_eq]
  -- solve for n 
  have hn : n = 22 := by 
    omega 
  -- contradiction since 22 is even 
  rcases h_odd_n with ⟨k, hk⟩
  rw [hn] at hk 
  omega