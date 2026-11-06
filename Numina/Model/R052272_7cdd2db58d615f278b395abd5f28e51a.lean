import Mathlib

theorem algebra_297377 {b g : ℕ} (hb : b > 0) (hg : g > 0)
    (h1 : b * 7 = g * 8) (h2 : b * 15 = g * 17 + 40) (h3 : b * 6 = g * 7 + 10) :
    b = 320 ∧ g = 280 := by
  omega