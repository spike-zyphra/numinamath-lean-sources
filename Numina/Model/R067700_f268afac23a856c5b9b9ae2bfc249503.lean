import Mathlib

theorem algebra_144844 (x : ℕ) (hx : x ≠ 0) (h : (95 / 100 : ℝ) * 20 + x = (96 / 100 : ℝ) * (20 + x)) :
    x = 5 := by

  have eq1 : (x : ℝ) = 5 := by
    norm_num at h ⊢
    linarith

  have h2 : x = 5 := by
    exact_mod_cast eq1

  exact h2