import Mathlib

theorem algebra_219912 {x : ℕ} (hx : x ≠ 0) (h1 : (1 / 3 : ℚ) * x + (1 / 5 : ℚ) * x + (1 / 6 : ℚ) * x + (1 / 4 : ℚ) * x + 6 = x) :
    x = 120 := by
  have h2 : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  field_simp at h1
  ring_nf at h1
  have h3 : (x : ℚ) = 120 := by
    linarith
  exact_mod_cast h3