import Mathlib

theorem algebra_602745 (x y z : ℝ) (hx : x + y + z = 3) (hy : x^2 + y^2 + z^2 = 3) (hz : x^5 + y^5 + z^5 = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by

  have h_eq1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
    nlinarith

  have h_eq2 : (x - y) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hx_eq_y : x = y := by nlinarith

  have h_eq3 : (y - z) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hy_eq_z : y = z := by nlinarith

  -- From x + y + z = 3 and x = y = z, we can solve for x, y, z.

  have h_eq4 : x = z := by linarith [hx_eq_y, hy_eq_z]

  -- Now that x = y = z, substitute into x + y + z = 3 to get 3x = 3, so x = 1

  have hx1 : x = 1 := by
    have eq1 : x + y + z = 3 := hx
    rw [show y = x by linarith [hx_eq_y]] at eq1
    rw [show z = x by linarith [h_eq4]] at eq1
    linarith

  -- Derive y = 1 and z = 1 from x = 1 and previous equalities.

  have hy1 : y = 1 := by linarith [hx_eq_y, hx1]

  have hz1 : z = 1 := by linarith [hy_eq_z, hy1]

  -- Final solutions

  exact ⟨hx1, hy1, hz1⟩