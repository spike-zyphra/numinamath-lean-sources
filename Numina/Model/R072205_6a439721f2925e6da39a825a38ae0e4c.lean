import Mathlib

theorem algebra_2042
    {a : ℝ}
    (ha : a > 0)
    (h : a^2 = a + 1) :
    a^3 > a + 2 := by
  have h1 : a^3 = a * a^2 := by ring
  rw [h] at h1
  have h2 : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * (a + 1) := by rw [h1]
      _ = a * a + a * 1 := by ring
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h]
      _ = 2 * a + 1 := by linarith
  rw [h2]
  -- We need to show $2a + 1 > a + 2$
  -- This is equivalent to $a > 1$
  -- So we need to prove $a > 1$.
  have h3 : a > 1 := by
    nlinarith [sq_nonneg (a - 1), sq_pos_of_pos ha, sq_nonneg (a^2 - 1), sq_nonneg (a^2 - a - 1)]
  linarith