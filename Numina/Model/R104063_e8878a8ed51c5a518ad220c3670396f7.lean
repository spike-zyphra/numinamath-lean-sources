import Mathlib

theorem algebra_264363 {a p : ℕ} (ha : a ≠ 0) (hp : p ≠ 0)
    (h1 : a * (2 / 3 : ℚ) = p * (3 / 4 : ℚ)) :
    (a + p) * (12 / 17 : ℚ) = a * (2 / 3 : ℚ) + p * (3 / 4 : ℚ) := by
  have h2 : (a : ℚ) * (2 / 3 : ℚ) = (p : ℚ) * (3 / 4 : ℚ) := by exact_mod_cast h1
  have h3 : 8 * (a : ℚ) = 9 * (p : ℚ) := by 
    linarith
  have h4 : (a : ℚ) = (9 / 8 : ℚ) * (p : ℚ) := by
    linarith
  rw [h4]
  field_simp at *
  <;> nlinarith