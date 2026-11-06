import Mathlib

theorem algebra_122616 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h1 : (g + b) * (1 - 10 / 100 : ℝ) = b * (50 / 100 : ℝ) + g * (55 / 100 : ℝ)) :
    b * (55 / 100 : ℝ) < b * (50 / 100 : ℝ) := by
  have h2 : (b : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hb
  have h3 : (g : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hg
  norm_num at h1 ⊢
  nlinarith