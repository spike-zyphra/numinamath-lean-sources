import Mathlib

theorem algebra_139049 {b1 b2 g1 g2 : ℕ}
    (h1 : b1 = 2 * g1) (h2 : b1 = g2) (h3 : b2 = b1 - 2) (h4 : g2 = g1 + 6)
    (h5 : b2 = 2 * g2) (h6 : b1 = g2 + 1) :
    g1 = 14 ∧ g2 = 9 := by 
  omega