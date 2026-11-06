import Mathlib

theorem number_theory_323590 (p k : ℕ) [hp : Fact (Nat.Prime p)] (hk : 1 ≤ k ∧ k < p) :
    p ∣ p.choose k := by 
  have h1 : 1 ≤ k := hk.1
  have h2 : k < p := hk.2
  have h3 : p.Prime := hp.1
  apply Nat.Prime.dvd_choose_self
  exact h3
  all_goals linarith