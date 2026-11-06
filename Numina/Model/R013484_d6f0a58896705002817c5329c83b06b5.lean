import Mathlib

theorem algebra_194478 {x1 x2 : ℝ} (hx1 : x1^2 - x1 - 3 = 0) (hx2 : x2^2 - x2 - 3 = 0)
    (hne : x1 ≠ x2) : (x1^5 - 20) * (3 * x2^4 - 2 * x2 - 35) = -1063 := by
  have eq1 : x1^2 = x1 + 3 := by linarith
  have eq2 : x2^2 = x2 + 3 := by linarith
  have eq3 : x1^3 = 4 * x1 + 3 := by
    calc
      x1^3 = x1 * x1^2 := by ring
      _ = x1 * (x1 + 3) := by rw [eq1]
      _ = x1^2 + 3 * x1 := by ring
      _ = (x1 + 3) + 3 * x1 := by rw [eq1]
      _ = 4 * x1 + 3 := by ring
  have eq4 : x1^4 = 7 * x1 + 12 := by
    calc
      x1^4 = x1 * x1^3 := by ring
      _ = x1 * (4 * x1 + 3) := by rw [eq3]
      _ = 4 * x1^2 + 3 * x1 := by ring
      _ = 4 * (x1 + 3) + 3 * x1 := by rw [eq1]
      _ = 7 * x1 + 12 := by ring
  have eq5 : x1^5 = 19 * x1 + 21 := by
    calc
      x1^5 = x1 * x1^4 := by ring
      _ = x1 * (7 * x1 + 12) := by rw [eq4]
      _ = 7 * x1^2 + 12 * x1 := by ring
      _ = 7 * (x1 + 3) + 12 * x1 := by rw [eq1]
      _ = 19 * x1 + 21 := by ring
  have eq6 : x2^3 = 4 * x2 + 3 := by
    calc
      x2^3 = x2 * x2^2 := by ring
      _ = x2 * (x2 + 3) := by rw [eq2]
      _ = x2^2 + 3 * x2 := by ring
      _ = (x2 + 3) + 3 * x2 := by rw [eq2]
      _ = 4 * x2 + 3 := by ring
  have eq7 : x2^4 = 7 * x2 + 12 := by
    calc
      x2^4 = x2 * x2^3 := by ring
      _ = x2 * (4 * x2 + 3) := by rw [eq6]
      _ = 4 * x2^2 + 3 * x2 := by ring
      _ = 4 * (x2 + 3) + 3 * x2 := by rw [eq2]
      _ = 7 * x2 + 12 := by ring
  have h1 : x1 + x2 = 1 := by
    have h2 : x1^2 - x1 - 3 = 0 := hx1
    have h3 : x2^2 - x2 - 3 = 0 := hx2
    have h4 : x1^2 - x1 - 3 - (x2^2 - x2 - 3) = 0 := by
      linarith [hx1, hx2]
    have h5 : (x1 - x2) * (x1 + x2 - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- x1 - x2 = 0 then x1 = x2 contradicts
      exfalso
      apply hne
      linarith
    · -- x1 + x2 - 1 = 0, so sum is 1
      linarith
  have h2 : x1 * x2 = -3 := by
    nlinarith [hx1, hx2, sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
      intro h'
      apply hne
      linarith
    )]
  have eq8 : x1^5 - 20 = 19 * x1 + 1 := by
    nlinarith [eq5]
  have eq9 : 3 * x2^4 - 2 * x2 - 35 = 19 * x2 + 1 := by
    nlinarith [eq7]
  have eq10 : (x1^5 - 20) * (3 * x2^4 - 2 * x2 - 35) = (19 * x1 + 1) * (19 * x2 + 1) := by
    rw [eq8, eq9]
  have eq11 : (19 * x1 + 1) * (19 * x2 + 1) = 361 * (x1 * x2) + 19 * (x1 + x2) + 1 := by
    ring
  rw [eq10, eq11, h2, h1]
  all_goals norm_num