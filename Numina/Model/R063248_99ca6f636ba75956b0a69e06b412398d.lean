import Mathlib

theorem number_theory_101128 (n : ℕ) (hn : Nat.Prime n) :
    ∀ k, 0 < k → k < n → n ∣ Nat.choose n k := by 
  intro k hk1 hk2
  apply Nat.Prime.dvd_choose_self hn
  all_goals omega