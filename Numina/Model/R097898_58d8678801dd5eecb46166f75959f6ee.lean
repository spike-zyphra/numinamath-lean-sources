import Mathlib

theorem number_theory_237594 (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ p - 1) :
    p ∣ Nat.choose p k := by 
  have h1 : 1 ≤ k := hk.1
  have h2 : k ≤ p - 1 := hk.2
  have h3 : k < p := by
    omega
  have h4 : p ∣ Nat.choose p k := by 
    apply hp.dvd_choose_self
    all_goals omega
  exact h4