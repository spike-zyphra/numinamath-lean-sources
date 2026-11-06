import Mathlib

theorem algebra_199520 (x y : ℝ) (hx : x = 2 * y) (hy : y ≠ 0)
    (h : x / (x + y) = 25 / 100) :
    y / (x + y) = 80 / 100 := by
  have h1 : x + y ≠ 0 := by
    by_contra h'
    have h2 : x + y = 0 := by linarith
    have h3 : y = 0 := by
      have eq1 : x = 2 * y := hx
      nlinarith [h2, eq1]
    contradiction
  -- Now that we have h1: x + y ≠ 0, we can manipulate h
  have h4 : 100 * x = 25 * (x + y) := by
    have h3' : x + y ≠ 0 := h1
    have h_eq : x / (x + y) = 25 / 100 := h
    field_simp [h3'] at h_eq
    linarith
  have h5 : y = 3 * x := by
    linarith
  -- Now from h5: y = 3 * x, and from hx: x = 2 * y
  -- Substitute y = 3 * x into hx
  have h6 : x = 0 := by
    rw [show y = 3 * x by linarith [h5]] at hx
    linarith
  have h7 : y = 0 := by
    linarith [h6, h5]
  -- Now from h7: y = 0. But from hy: y ≠ 0. Contradiction.
  have h8 : y ≠ 0 := hy
  contradiction