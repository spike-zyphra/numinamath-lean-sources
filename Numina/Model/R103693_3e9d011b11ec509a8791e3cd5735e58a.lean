import Mathlib

theorem algebra_198280 {f : ℤ → ℤ → ℤ → ℤ}
    (hf : f = fun x y z => x^2 - y^2 - z^2 + 2 * y * z + x + y - z) :
    (X - Y + Z + 1) ∣ f X Y Z := by
  rw [hf]
  use (X + Y - Z)
  ring