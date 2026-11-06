import Mathlib

theorem algebra_93937 {a b : ℕ} (ha : a > 0) (hb : b > 0)
(h1 : (2 / 3 : ℚ) * a = (5 / 8 : ℚ) * b - 7) (h2 : (1 / 3 : ℚ) * a = (3 / 8 : ℚ) * b - 7) :
a = 42 := by

  have eq1 : (16 : ℚ) * (a : ℚ) = (15 : ℚ) * (b : ℚ) - 168 := by
    linarith

  have eq2 : (8 : ℚ) * (a : ℚ) = (9 : ℚ) * (b : ℚ) - 168 := by
    linarith

  have eq3 : (3 : ℚ) * (b : ℚ) = 168 := by
    have eq4 : (16 : ℚ) * (a : ℚ) = (15 : ℚ) * (b : ℚ) - 168 := eq1
    have eq5 : (16 : ℚ) * (a : ℚ) = (18 : ℚ) * (b : ℚ) - 336 := by
      linarith [eq2]
    linarith [eq4, eq5]

  have eq4 : (b : ℚ) = 56 := by
    linarith

  have eq5 : (a : ℚ) = 42 := by
    rw [eq4] at eq2
    linarith

  exact_mod_cast eq5