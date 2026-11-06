import Mathlib

theorem algebra_326281 (x y : ℤ) (hx : ∃ a b, x = a^2 + 4 * a * b + b^2 - 10 * a - 8 * b + 13)
    (hy : ∃ c d, y = c^2 + 4 * c * d + d^2 - 10 * c - 8 * d + 13) :
    ∃ e f, x * y = e^2 + 4 * e * f + f^2 - 10 * e - 8 * f + 13 := by
  rcases hx with ⟨a, b, hxa⟩
  rcases hy with ⟨c, d, hya⟩
  use ((a + 2 * b - 5) * (c + 2 * d - 5) + 3 * (b - 2) * (d - 2) - 2 * ((a + 2 * b - 5) * (d - 2) + (b - 2) * (c + 2 * d - 5)) + 1)
  use ((a + 2 * b - 5) * (d - 2) + (b - 2) * (c + 2 * d - 5) + 2)
  rw [hxa, hya]
  ring_nf