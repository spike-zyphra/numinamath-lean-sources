import Mathlib

theorem number_theory_226283 (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k ∧ k ≤ p - 1) :
    p ∣ Nat.choose p k := by
  apply Nat.Prime.dvd_choose_self
  exact hp
  all_goals omega