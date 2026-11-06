import Mathlib

theorem algebra_320487 {a : ℝ} (ha : a = Real.sqrt 17 - 1) :
    (a^5 + 2*a^4 - 17*a^3 - a^2 + 18*a - 17)^1993 = -1 := by
  have h1 : a + 1 = Real.sqrt 17 := by
    rw [ha]
    all_goals ring_nf
  have h2 : (a + 1) ^ 2 = 17 := by
    rw [h1]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h3 : a^2 + 2 * a - 16 = 0 := by
    nlinarith
  have h4 : a^2 = -2 * a + 16 := by
    linarith
  have h5 : a^3 = 20 * a - 32 := by
    calc
      a^3 = a * (a^2) := by ring
      _ = a * (-2 * a + 16) := by rw [show a^2 = -2 * a + 16 by linarith [h3]]
      _ = -2 * a^2 + 16 * a := by ring
      _ = -2 * (-2 * a + 16) + 16 * a := by rw [show a^2 = -2 * a + 16 by linarith [h3]]
      _ = 20 * a - 32 := by ring
  have h6 : a^4 = -72 * a + 320 := by
    calc
      a^4 = (a^2) ^ 2 := by ring
      _ = (-2 * a + 16) ^ 2 := by rw [show a^2 = -2 * a + 16 by linarith [h3]]
      _ = 4 * a^2 - 64 * a + 256 := by ring
      _ = 4 * (-2 * a + 16) - 64 * a + 256 := by rw [show a^2 = -2 * a + 16 by linarith [h3]]
      _ = -72 * a + 320 := by ring
  have h7 : a^5 = 464 * a - 1152 := by
    calc
      a^5 = a * (a^4) := by ring
      _ = a * (-72 * a + 320) := by rw [show a^4 = -72 * a + 320 by linarith [h6]]
      _ = -72 * a^2 + 320 * a := by ring
      _ = -72 * (-2 * a + 16) + 320 * a := by rw [show a^2 = -2 * a + 16 by linarith [h3]]
      _ = 464 * a - 1152 := by ring
  have h8 : a^5 + 2 * a^4 - 17 * a^3 - a^2 + 18 * a - 17 = -1 := by
    rw [show a^5 = 464 * a - 1152 by linarith [h7]]
    rw [show a^4 = -72 * a + 320 by linarith [h6]]
    rw [show a^3 = 20 * a - 32 by linarith [h5]]
    rw [show a^2 = -2 * a + 16 by linarith [h4]]
    nlinarith
  rw [h8]
  norm_num