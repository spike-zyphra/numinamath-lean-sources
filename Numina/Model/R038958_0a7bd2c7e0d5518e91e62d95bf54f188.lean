import Mathlib

theorem number_theory_297671 {x y : ℤ} {k n : ℤ}(hx : ∃ a b, x = a^2 + k * a * b + n * b^2)
    (hy : ∃ c d, y = c^2 + k * c * d + n * d^2) :
    ∃ g h, x * y = g^2 + k * g * h + n * h^2 := by
  rcases hx with ⟨a, b, hxa⟩
  rcases hy with ⟨c, d, hya⟩
  use a * c - n * b * d
  use b * c + a * d + k * b * d
  rw [show x * y = (a^2 + k * a * b + n * b^2) * (c^2 + k * c * d + n * d^2) by
      rw [hxa, hya]]
  ring_nf