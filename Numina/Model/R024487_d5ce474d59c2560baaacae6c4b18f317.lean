import Mathlib

theorem number_theory_7506
    (n : ℕ)
    (hn : 2 ≤ n) :
    1 ≤ (Nat.totient n) ∧ (Nat.totient n) ≤ n - 1 := by
  constructor
  · -- Show that 1 ≤ Nat.totient n
    have h1 : n ≥ 2 := hn 
    have h4 : Nat.totient n > 0 := by 
      apply Nat.totient_pos.mpr 
      linarith
    linarith 
  · -- Show that Nat.totient n ≤ n - 1
    have h7 : (Nat.totient n) ≤ n - 1 := by
      have h8 : n ≥ 2 := hn 
      have h9 : (Nat.totient n) < n := by 
        apply Nat.totient_lt
        all_goals linarith
      have h10 : (Nat.totient n) ≤ n - 1 := by 
        omega 
      exact h10 
    exact h7