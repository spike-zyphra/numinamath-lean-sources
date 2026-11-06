import Mathlib

theorem algebra_185605 (m : ℝ) (x y : ℤ) (hx : x < 0) (hy : y > 0)
    (h1 : -2 * x + 3 * y = 2 * m) (h2 : x - 5 * y = -11) :
    (m = 4 ∧ x = -1 ∧ y = 2) ∨ (m = 15 / 2 ∧ x = -6 ∧ y = 1) := by
  have eq1 : x = 5 * y - 11 := by
    omega
  have eq2 : y < 3 := by
    nlinarith [hx, eq1, hy]
  have eq3 : y = 1 ∨ y = 2 := by
    omega
  rcases eq3 with h | h
  · -- Assume y = 1
    have hy1 : y = 1 := h
    have hx1 : x = -6 := by
      rw [hy1] at eq1
      omega
    have hm1 : m = 15 / 2 := by
      rw [hx1, hy1] at h1
      norm_num at h1
      have h3 : (m : ℝ) = 15 / 2 := by linarith
      exact_mod_cast h3
    right
    constructor
    · exact_mod_cast hm1
    constructor
    · exact_mod_cast hx1
    · exact_mod_cast hy1
  · -- Assume y = 2
    have hy2 : y = 2 := h
    have hx2 : x = -1 := by
      rw [hy2] at eq1
      omega
    have hm2 : m = 4 := by
      rw [hx2, hy2] at h1
      norm_num at h1
      have h4 : (m : ℝ) = 4 := by linarith
      exact_mod_cast h4
    left
    constructor
    · exact_mod_cast hm2
    constructor
    · exact_mod_cast hx2
    · exact_mod_cast hy2