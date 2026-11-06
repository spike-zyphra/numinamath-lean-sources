import Mathlib

theorem algebra_235287 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h1 : (g + 10) * 55 / 100 = b * 50 / 100 + g * 10 / 100) :
    g * 10 / 100 < b * 50 / 100 := by
  omega