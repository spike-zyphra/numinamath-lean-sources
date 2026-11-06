import Mathlib

theorem number_theory_57585 (p : ℕ) (hp : Nat.Prime p) :
    ∃ m n, p = m^2 + n^2 ∧ m^3 + n^3 - 4 ≡ 0 [MOD p] ↔ p = 2 := by 
  use 1, 1
  constructor
  · -- Forward direction: if (1,1) satisfy the conditions, then p = 2
    intro h
    rcases h with ⟨h1, h2⟩
    have h2' : p = 2 := by
      omega
    exact h2'
  · -- Backward direction: if p = 2, then (1,1) satisfy the conditions
    intro h
    rw [h]
    constructor
    · -- Show 2 = 1^2 + 1^2
      norm_num
    · -- Show 1^3 + 1^3 - 4 ≡ 0 [MOD 2]
      norm_num [Nat.ModEq]