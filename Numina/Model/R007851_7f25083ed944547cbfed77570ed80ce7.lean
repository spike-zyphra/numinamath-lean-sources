import Mathlib

theorem number_theory_4502 {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k ∧ k < p) : p ∣ p.choose k := by 
  have h1 : 1 ≤ k := hk.1
  have h2 : k < p := hk.2
  apply Nat.Prime.dvd_choose_self hp
  all_goals
    omega