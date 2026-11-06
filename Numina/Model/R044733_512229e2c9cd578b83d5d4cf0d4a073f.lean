import Mathlib

theorem inequalities_41313 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h1 : (Real.sqrt (x ^ 2 + 2 * y)) % 1 > 2 / 3) (h2 : (Real.sqrt (y ^ 2 + 2 * x)) % 1 > 2 / 3) :
    x = y := by
  norm_num at h1 h2
  all_goals
    have h3 : x ≤ y := by
      by_contra h
      push_neg at h
      all_goals
        nlinarith
    have h4 : y ≤ x := by
      by_contra h
      push_neg at h
      all_goals
        nlinarith
    linarith