import Mathlib

theorem algebra_12921 {g b : ℕ} (hg : g + b = 1200) (hb : g ≠ 0) (hgp : (2 / 3 : ℚ) * g + (1 / 2 : ℚ) * b = 730) :
    (2 / 3 : ℚ) * g = 520 := by
  have h1 : (g : ℚ) + (b : ℚ) = (1200 : ℚ) := by exact_mod_cast hg
  have h2 : (b : ℚ) = (1200 : ℚ) - (g : ℚ) := by
    linarith [h1]
  rw [h2] at hgp
  have h3 : (g : ℚ) = 780 := by
    linarith
  rw [h3]
  all_goals norm_num