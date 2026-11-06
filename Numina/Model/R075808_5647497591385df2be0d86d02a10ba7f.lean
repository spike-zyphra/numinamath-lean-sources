import Mathlib

theorem algebra_5161 {a b : ℕ} (ha : a = b + 11) (hb : b ≠ 0)
    (h : a - (1 / 3 : ℚ) * a = b - (1 / 4 : ℚ) * b + 5) :
    b = 28 := by 
  have eq1 : (a : ℚ) = (b : ℚ) + 11 := by exact_mod_cast ha
  rw [eq1] at h
  have eq2 : (b : ℚ) = 28 := by
    linarith
  exact_mod_cast eq2