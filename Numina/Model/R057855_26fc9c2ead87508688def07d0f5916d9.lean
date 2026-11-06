import Mathlib

theorem algebra_7968 {a : ℝ} (ha : a^2 - a - 3 = 0) : a^3 + 999*a^2 - 1003*a + 2009 = 5009 := by 
  have h1 : a^2 = a + 3 := by
    linarith
  have h2 : a^3 = 4 * a + 3 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 3) := by rw [h1]
      _ = a^2 + 3 * a := by ring
      _ = (a + 3) + 3 * a := by rw [h1]
      _ = 4 * a + 3 := by ring
  calc
    a^3 + 999 * a^2 - 1003 * a + 2009
        = (4 * a + 3) + 999 * (a + 3) - 1003 * a + 2009 := by 
          rw [h2, h1]
    _ = (4 * a + 3) + (999 * a + 2997) - 1003 * a + 2009 := by 
      ring
    _ = 5009 := by 
      linarith