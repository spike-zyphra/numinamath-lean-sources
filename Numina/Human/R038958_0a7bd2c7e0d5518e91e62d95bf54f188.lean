import Mathlib

theorem number_theory_297671 {x y : ℤ} {k n : ℤ}(hx : ∃ a b, x = a^2 + k * a * b + n * b^2)
    (hy : ∃ c d, y = c^2 + k * c * d + n * d^2) :
    ∃ g h, x * y = g^2 + k * g * h + n * h^2 := by 
  obtain ⟨a, b, h⟩ := hx
  obtain ⟨c, d, h'⟩ := hy
  use (a * c + n * b* d + k * b * c)
  use (a* d - b * c)
  rw [h, h']
  ring_nf
