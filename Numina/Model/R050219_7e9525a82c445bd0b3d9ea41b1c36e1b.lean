import Mathlib

theorem algebra_995 {m : ℝ} (hm : m^2 + m - 1 = 0) : m^3 + 2 * m^2 - 1997 = -1996 := by
  have h1 : m^2 = 1 - m := by linarith
  have h2 : m^3 = 2 * m - 1 := by
    calc
      m^3 = m * m^2 := by ring
      _   = m * (1 - m) := by rw [h1]
      _   = m - m^2 := by ring
      _   = m - (1 - m) := by rw [h1]
      _   = 2 * m - 1 := by ring
  rw [h2, h1]
  ring_nf