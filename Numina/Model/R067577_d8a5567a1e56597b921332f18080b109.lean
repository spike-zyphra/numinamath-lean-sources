import Mathlib

theorem algebra_215352 {a : ℝ} (h : a^5 - a^3 + a = 2) : a^6 > 3 := by
  have h1 : a^5 = a^3 - a + 2 := by linarith
  have h2 : a^6 = a^4 - a^2 + 2 * a := by
    calc
      a^6 = a * a^5 := by ring
      _ = a * (a^3 - a + 2) := by rw [h1]
      _ = a^4 - a^2 + 2 * a := by ring
  rw [h2]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a + 1), sq_nonneg (a - 2),
            sq_nonneg (a^2 - a), sq_nonneg (a^2 + a), sq_nonneg (a^3 - 1),
            sq_nonneg (a^2 - 4), sq_nonneg (a^2 - 2*a), sq_nonneg (a - 1),
            sq_nonneg (a^2 - a - 1),
            sq_nonneg (a^5 - a^3 + a - 2), 
            h]