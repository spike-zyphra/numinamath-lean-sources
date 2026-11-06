import Mathlib

theorem number_theory_180387 {b : ℕ} (hb : b = 2013^2013 + 2) :
    ¬Nat.Coprime (b^3 + 1) (b^2 + 2) := by
  rw [hb]
  native_decide