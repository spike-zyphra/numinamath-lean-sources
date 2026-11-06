import Mathlib

theorem algebra_109676 (d t : ℝ) (ht : t > 0) (h1 : d / 50 = t - 1) (h2 : d / 35 = t + 2) :
    d = 350 := by
  have eq1 : d = 50 * (t - 1) := by
    field_simp at h1
    linarith
  have eq2 : d = 35 * (t + 2) := by
    field_simp at h2
    linarith
  have ht_eq : t = 8 := by
    linarith [eq1, eq2]
  rw [ht_eq] at eq1
  linarith