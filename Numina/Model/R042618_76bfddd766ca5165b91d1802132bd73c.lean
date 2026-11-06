import Mathlib

theorem number_theory_605986 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
(hne : a * d ≠ b * c) (hgcd : Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1) :
∃ k, ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m ∣ k ∧ Nat.gcd (a * n + b) (c * n + d) = m := by 
  use 0
  intro n hn
  use Nat.gcd (a * n + b) (c * n + d)
  constructor
  · -- Show 0 < m 
    have h1 : 0 < a * n + b := by
      nlinarith
    have h2 : 0 < c * n + d := by
      nlinarith
    have h3 : 0 < Nat.gcd (a * n + b) (c * n + d) := by
      apply Nat.gcd_pos_of_pos_left
      linarith
    linarith
  constructor
  · -- Show m ∣ k = 0
    simp
  · -- Show Nat.gcd (a * n + b) (c * n + d) = m 
    rfl