import Mathlib

theorem number_theory_7841 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a > n ∧ b > n ∧ c > n ∧
      IsSquare (a ^ 2 + b ^ 2) ∧
      IsSquare (b ^ 2 + c ^ 2) ∧
      IsSquare (c ^ 2 + a ^ 2) := by 
  intro n
  use 44 * (n + 1)
  use 117 * (n + 1)
  use 240 * (n + 1)
  constructor 
  · -- Show that a > n.
    ring_nf
    omega 
  constructor
  · -- Show that b > n.
    ring_nf 
    omega 
  constructor
  · -- Show that c > n.
    ring_nf 
    omega 
  constructor
  · -- Show that a^2 + b^2 is a perfect square.
    have h11 : IsSquare ((44 * (n + 1)) ^ 2 + (117 * (n + 1)) ^ 2) := by 
      use 125 * (n + 1)
      all_goals
        ring_nf 
    exact h11
  constructor
  · -- Show that b^2 + c^2 is a perfect square.
    have h22 : IsSquare ((117 * (n + 1)) ^ 2 + (240 * (n + 1)) ^ 2) := by 
      use 267 * (n + 1)
      all_goals
        ring_nf 
    exact h22
  · -- Show that c^2 + a^2 is a perfect square.
    have h33 : IsSquare ((240 * (n+1)) ^ 2 + (44 * (n+1)) ^ 2) := by 
      use 244 * (n + 1)
      all_goals
        ring_nf 
    exact h33