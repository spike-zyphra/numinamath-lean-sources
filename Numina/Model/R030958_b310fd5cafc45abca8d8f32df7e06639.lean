import Mathlib

theorem algebra_921 {x y : ℕ} (hx : x ≥ 3) (hy : y ≥ 3) (h1 : (x - 3 : ℚ) / (y + 3) = 1 / 1) (h2 : (x + 3 : ℚ) / (y - 3) = 13 / 7): y = 17 := by
  have eq1 : (x - 3 : ℚ) = (y + 3 : ℚ) := by
    field_simp [(show (y + 3 : ℚ) ≠ 0 by
      by_contra h
      have : (y : ℚ) = -3 := by linarith
      have h' : (y : ℚ) ≥ (3 : ℚ) := by exact_mod_cast hy
      linarith
    )] at h1 ⊢
    linarith [h1]

  have eq2 : (7 : ℚ) * (x + 3 : ℚ) = (13 : ℚ) * (y - 3 : ℚ) := by
    field_simp [(show (y - 3 : ℚ) ≠ 0 by
      by_contra h
      have : (y : ℚ) = (3 : ℚ) := by linarith
      have h' : (y : ℚ) ≥ (3 : ℚ) := by exact_mod_cast hy
      -- Since y >= 3, y - 3 = 0 implies y = 3
      have : (y : ℚ) = 3 := by linarith
      rw [this] at h2
      norm_num at h2
      all_goals tauto
    )] at h2 ⊢
    linarith [h2]

  have eq1_nat' : (x : ℚ) = (y + 6 : ℚ) := by
    linarith [eq1]

  rw [show (x : ℚ) = (y + 6 : ℚ) by linarith [eq1_nat']] at eq2

  have eq3 : (y : ℚ) = 17 := by
    nlinarith

  exact_mod_cast eq3