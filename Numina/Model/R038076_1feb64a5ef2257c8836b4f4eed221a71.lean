import Mathlib

theorem algebra_7876 {x y z : ℤ} (h1 : 2*x-3*y+z≡4 [ZMOD 13]) (h2 : 3*x+y-2*z≡1 [ZMOD 13])
    (h3 : x-2*y+3*z≡5 [ZMOD 13]) :
    ∃ a b c, x=13*a+12 ∧ y=13*b+2 ∧ z=13*c+12 := by
  have eq1 : (2 * x - 3 * y + z) % 13 = 4 % 13 := h1
  have eq2 : (3 * x + y - 2 * z) % 13 = 1 % 13 := h2
  have eq3 : (x - 2 * y + 3 * z) % 13 = 5 % 13 := h3
  use (x - 12) / 13
  use (y - 2) / 13
  use (z - 12) / 13
  constructor
  · -- Prove x=13*a+12
    omega
  constructor
  · -- Prove y=13*b+2
    omega
  · -- Prove z=13*c+12
    omega