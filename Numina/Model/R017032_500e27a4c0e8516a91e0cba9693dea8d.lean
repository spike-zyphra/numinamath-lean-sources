import Mathlib

theorem algebra_1745 {x y : ℤ} (hx : ∃ a b c : ℤ, x = a^3 + b^3 + c^3 - 3*a*b*c)
    (hy : ∃ a b c : ℤ, y = a^3 + b^3 + c^3 - 3*a*b*c) :
    ∃ a b c : ℤ, x * y = a^3 + b^3 + c^3 - 3*a*b*c := by 
  rcases hx with ⟨a, b, c, hx⟩
  rcases hy with ⟨u, v, w, hy⟩ 
  use a * u + b * v + c * w
  use a * v + b * w + c * u
  use a * w + b * u + c * v
  simp [hx, hy]
  ring_nf