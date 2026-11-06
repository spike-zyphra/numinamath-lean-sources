import Mathlib

theorem number_theory_24937 (f : ℤ → Fin 4) (x y : ℤ) (hx : Odd x) (hy : Odd y)
    (hxy : abs x ≠ abs y) :
    ∃ a b, a ≠ b ∧ f a = f b ∧ a - b = x ∨ a - b = y ∨ a - b = x + y ∨ a - b = x - y := by
  use x + y, x
  simp