import Mathlib

theorem algebra_2934 (a : ℝ) (ha : a^2 + 2 * a - 3 = 1) : 2 * a^4 + 6 * a^3 - 3 * a^2 - 6 * a + 2019 = 2023 := by 
  have h1 : a^2 = -2 * a + 4 := by
    linarith
  have h2 : a^3 = 8 * a - 8 := by
    calc 
      a^3 = a * a^2 := by ring
      _ = a * (-2 * a + 4) := by rw [h1]
      _ = -2 * a^2 + 4 * a := by ring
      _ = -2 * (-2 * a + 4) + 4 * a := by rw [h1]
      _ = 8 * a - 8 := by ring
  have h3 : a^4 = -24 * a + 32 := by 
    calc 
      a^4 = a * a^3 := by ring
      _ = a * (8 * a - 8) := by rw [h2]
      _ = 8 * a^2 - 8 * a := by ring
      _ = 8 * (-2 * a + 4) - 8 * a := by rw [h1]
      _ = -24 * a + 32 := by ring
  have h4 : 2 * a^4 + 6 * a^3 - 3 * a^2 - 6 * a + 2019 = 2023 := by 
    rw [show a^4 = -24 * a + 32 by linarith [h3]]
    rw [show a^3 = 8 * a - 8 by linarith [h2]]
    rw [show a^2 = -2 * a + 4 by linarith [h1]]
    linarith
  exact h4