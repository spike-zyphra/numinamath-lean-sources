import Mathlib

theorem algebra_176790 {g b : ℕ} (hb : b ≠ 0) (h : g = (10 / 9 : ℚ) * b) :
    (g * (2 / 5 : ℚ) + b * (1 / 3 : ℚ)) / (g + b) = 7 / 19 := by
  have h1 : (g : ℚ) = (10 / 9 : ℚ) * (b : ℚ) := by
    exact_mod_cast h
  have h2 : (g * (2 / 5 : ℚ) + b * (1 / 3 : ℚ)) = (7 / 9 : ℚ) * (b : ℚ) := by
    rw [show (g : ℚ) = (10 / 9 : ℚ) * (b : ℚ) by linarith [h1]]
    field_simp
    ring
  have h3 : ((g : ℚ) + (b : ℚ)) = (19 / 9 : ℚ) * (b : ℚ) := by
    rw [show (g : ℚ) = (10 / 9 : ℚ) * (b : ℚ) by linarith [h1]]
    field_simp
    ring
  rw [show (g * (2 / 5 : ℚ) + (b : ℚ) * (1 / 3 : ℚ)) = (7 / 9 : ℚ) * (b : ℚ) by linarith [h2]]
  rw [show ((g : ℚ) + (b : ℚ)) = (19 / 9 : ℚ) * (b : ℚ) by linarith [h3]]
  have h4 : (b : ℚ) ≠ 0 := by
    exact_mod_cast show (b : ℕ) ≠ 0 by exact_mod_cast hb
  field_simp [h4]
  <;> ring_nf