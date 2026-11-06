import Mathlib

/- Show that if \( a \) and \( b \) are positive integers and \( a \mid b \), then \( a \leqslant b \).-/
theorem number_theory_4746 (a b : ℕ) (_ : 0 < a) (h₁ : 0 < b) (h₂ : a ∣ b) : a ≤ b :=
  -- exact `Nat.le_of_dvd` in Mathlib
  Nat.le_of_dvd h₁ h₂
