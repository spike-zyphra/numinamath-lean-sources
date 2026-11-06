import Mathlib

theorem algebra_176790 {g b : ℕ} (hb : b ≠ 0) (h : g = (10 / 9 : ℚ) * b) :
    (g * (2 / 5 : ℚ) + b * (1 / 3 : ℚ)) / (g + b) = 7 / 19 := by
  have h1 : (g : ℚ) = (10 / 9 : ℚ) * b := by exact_mod_cast h
  field_simp [h1]
  ring_nf