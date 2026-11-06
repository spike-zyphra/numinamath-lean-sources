import Mathlib

theorem algebra_283054 (w b : ℕ) (hw : w = 15) (hb : b = 7) :
    IsLeast {x | ∃ w' b' : ℕ, w' = w + x ∧ b' = b + x ∧ w' + b' = 2 * (w + b)} 11 := by
  constructor
  · -- We check that 11 is indeed in the set
    use 15 + 11, 7 + 11
    all_goals simp [hw, hb]
    <;> omega
  · -- We prove that 11 is the smallest element in the set
    intro x hx
    rcases hx with ⟨w', b', hw'_eq, hb'_eq, hsum_eq⟩
    simp only [hw, hb] at hw'_eq hb'_eq hsum_eq
    omega