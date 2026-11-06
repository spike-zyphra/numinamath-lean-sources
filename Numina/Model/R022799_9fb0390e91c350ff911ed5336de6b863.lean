import Mathlib

theorem number_theory_228107 (p : ℕ) (hp : Nat.Prime p) :
    ∃ m n, (p + 7 = 2 * m^2) ∧ (p^2 + 7 = 2 * n^2) ↔ p = 11 := by
  use 3
  use 8
  constructor
  · -- Assume both equations hold, prove p = 11
    rintro ⟨h1, h2⟩
    have h3 : p = 11 := by
      nlinarith
    exact h3
  · -- Assume p = 11, prove both equations
    rintro hp
    rw [hp]
    all_goals
      norm_num