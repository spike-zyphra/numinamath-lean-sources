import Mathlib

theorem algebra_230989 {a : ℝ} (ha : a^2 - a - 50 = 0) : a^4 - 101*a = 2550 := by 
  have h1 : a^2 = a + 50 := by
    linarith
  have h2 : a^3 = 51 * a + 50 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 50) := by rw [h1]
      _ = a^2 + 50*a := by ring
      _ = (a + 50) + 50*a := by rw [h1]
      _ = 51*a + 50 := by ring
  have h3 : a^4 = 101 * a + 2550 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (51 * a + 50) := by rw [h2]
      _ = 51 * a^2 + 50 * a := by ring
      _ = 51 * (a + 50) + 50 * a := by rw [h1]
      _ = 101*a + 2550 := by ring
  calc 
    a^4 - 101*a = (101*a + 2550) - 101*a := by rw [h3]
    _ = 2550 := by ring