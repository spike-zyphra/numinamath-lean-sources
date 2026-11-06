import Mathlib

theorem inequalities_312814 (r y w : ℕ) (h₀ : w ≤ (1 / 2 : ℚ) * y) (h₁ : w ≥ (1 / 3 : ℚ) * r)
    (h₂ : y + w ≤ 55) : r ≤ 54 := by
  have h3 : (w : ℚ) ≤ (1 / 2 : ℚ) * (y : ℚ) := by 
    exact_mod_cast h₀
  have h4 : 2 * (w : ℚ) ≤ (y : ℚ) := by
    linarith
  have h4_nat : 2 * w ≤ y := by
    exact_mod_cast h4
  have h5 : 3 * (w : ℚ) ≥ (r : ℚ) := by 
    linarith
  have h5_nat : 3 * w ≥ r := by
    exact_mod_cast h5
  omega