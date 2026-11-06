import Mathlib

theorem algebra_3760 {a : ℝ} (ha : a^2 + 2 * a - 3 = 1) :
    a^4 + 4 * a^3 - 2 * a^2 - 12 * a + 2027 = 2019 := by
  have h1 : a^2 + 2 * a - 4 = 0 := by linarith
  have h2 : a^2 = -2 * a + 4 := by
    linarith [h1]
  have h3 : a^3 = 8 * a - 8 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (-2 * a + 4) := by rw [h2]
      _ = -2 * a^2 + 4 * a := by ring
      _ = -2 * (-2 * a + 4) + 4 * a := by rw [h2]
      _ = 8 * a - 8 := by ring
  have h4 : a^4 = -24 * a + 32 := by
    calc
      a^4 = (a^2) ^ 2 := by ring
      _ = (-2 * a + 4) ^ 2 := by rw [h2]
      _ = 4 * a^2 - 16 * a + 16 := by ring
      _ = 4 * (-2 * a + 4) - 16 * a + 16 := by rw [h2]
      _ = -24 * a + 32 := by ring
  nlinarith [h4, h3, h2, sq_nonneg (a + 2), sq_nonneg (a - 2)]