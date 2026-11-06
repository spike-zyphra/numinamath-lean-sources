import Mathlib

theorem number_theory_127905 (a b c d : ℤ) (hab : a ∣ b) (hcd : c ∣ d) : a * c ∣ b * d := by 
  rcases hab with ⟨k1, hk1⟩
  rcases hcd with ⟨k2, hk2⟩
  use k1 * k2
  rw [show b * d = (a * c) * (k1 * k2) by
    rw [hk1, hk2]
    ring]