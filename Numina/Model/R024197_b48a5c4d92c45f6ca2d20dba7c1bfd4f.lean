import Mathlib

theorem number_theory_60252 (k : ℤ) :
    ∃ f : ℕ → ℤ, f 1995 = 1996 ∧ ∀ x y, f (x * y) = f x + f y + k * f (Nat.gcd x y) ↔ k = -1 := by
  use fun n => 1996
  constructor
  · -- Show f 1995 = 1996
    simp
  · -- Show the bi-implication
    intro x y
    constructor
    · -- Assume f (x * y) = f x + f y + k * f (Nat.gcd x y), prove k = -1
      intro h
      simp at h
      linarith
    · -- Assume k = -1, prove f (x * y) = f x + f y + k * f (Nat.gcd x y)
      intro h
      simp [h]
      all_goals linarith