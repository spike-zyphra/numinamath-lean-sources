import Mathlib

theorem algebra_253545 (x y : ℝ) (hx : x^3 = 20 + 14 * Real.sqrt 2) (hy : y^3 = 20 - 14 * Real.sqrt 2) :
    x + y = 4 := by
  have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [h1]
      _ = 4 := by norm_num

  have h3 : x * y = 2 := by
    have h4 : (x * y) ^ 3 = 8 := by
      calc
        (x * y) ^ 3 = x^3 * y^3 := by ring
        _ = (20 + 14 * Real.sqrt 2) * (20 - 14 * Real.sqrt 2) := by rw [hx, hy]
        _ = (20 : ℝ) ^ 2 - (14 * Real.sqrt 2) ^ 2 := by ring
        _ = 400 - (196 * (Real.sqrt 2 ^ 2)) := by
          ring_nf
        _ = 400 - (196 * 2) := by
          rw [h1]
          all_goals linarith
        _ = (8 : ℝ) := by norm_num

    have h5 : (x * y - 2) * ((x * y) ^ 2 + 2 * (x * y) + 4) = 0 := by
      ring_nf at h4 ⊢
      linarith

    cases' (mul_eq_zero.mp h5) with h6 h7
    · linarith
    · -- Show that second factor has no real solutions
      have h8 : (x * y) ^ 2 + 2 * (x * y) + 4 > 0 := by
        nlinarith [sq_nonneg (x * y + 1)]
      nlinarith

  have h4 : (x + y) ^ 3 = 40 + 6 * (x + y) := by
    have h5 : x^3 + y^3 = 40 := by
      linarith [hx, hy]
    have h6 : (x + y) ^ 3 = x^3 + y^3 + 3 * (x * y) * (x + y) := by
      ring
    rw [h6, h5, h3] at *
    all_goals linarith

  have h5 : (x + y - 4) * ((x + y) ^ 2 + 4 * (x + y) + 10) = 0 := by
    ring_nf at h4 ⊢
    linarith

  cases' (mul_eq_zero.mp h5) with h8 h9
  · linarith
  · -- Show that second factor has no real solutions
    have h10 : (x + y) ^ 2 + 4 * (x + y) + 10 > 0 := by
      nlinarith [sq_nonneg ((x + y) + 2)]
    nlinarith