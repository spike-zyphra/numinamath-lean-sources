import Mathlib

theorem number_theory_104603 (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x - 13 : ℚ) / y = x / (y + 14)) :
    13 ∣ x ∧ 14 ∣ y := by
  have h1 : (x : ℚ) ≠ 0 := by
    exact_mod_cast hx
  have h2 : (y : ℚ) ≠ 0 := by
    exact_mod_cast hy
  have eq1 : (x - 13 : ℚ) / y = x / (y + 14) := h
  have eq2 : (x - 13 : ℚ) * (y + 14) = x * (y : ℚ) := by
    field_simp [h1, h2, show (y + 14 : ℚ) ≠ 0 by
      by_contra h3
      have : (y : ℚ) = -14 := by linarith
      have h4 : (y : ℚ) > 0 := by
        exact_mod_cast show (y : ℕ) > 0 by omega
      linarith
    ] at eq1 ⊢
    nlinarith
  have eq3 : (x : ℚ) * 14 = 13 * (y : ℚ) + 182 := by
    nlinarith
  have eq4 : (x : ℤ) * 14 = 13 * (y : ℤ) + 182 := by
    have h3 : (x : ℚ) * 14 = 13 * (y : ℚ) + 182 := eq3
    have h4 : (x : ℤ) * 14 = 13 * (y : ℤ) + 182 := by
      exact_mod_cast h3
    linarith
  constructor
  · -- Show that 13 divides x
    have h3 : (13 : ℤ) ∣ (x : ℤ) := by
      omega
    exact_mod_cast h3
  · -- Show that 14 divides y
    have h4 : (14 : ℤ) ∣ (y : ℤ) := by
      omega
    exact_mod_cast h4