import Mathlib

theorem algebra_235783 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : (5 * x) + y = 2 * (x + y)) (h2 : x + (5 * y) = k * (x + y)) :
    k = 4 := by

  have eq1 : y = 3 * x := by
    omega

  rw [show y = 3 * x by omega] at h2

  have h3 : x + (5 * (3 * x)) = k * (x + 3 * x) := by
    linarith

  -- Simplify the equation
  -- Left side: x + 15x = 16x
  -- Right side: k * 4x
  have eq3 : k * (x + 3 * x) = 16 * x := by
    omega

  -- Rewrite as k * 4x = 16x
  have eq4 : k * (4 * x) = 16 * x := by
    ring_nf at eq3 ⊢
    omega

  have h4 : x > 0 := hx

  have h5 : k * (4 * x) = 4 * (4 * x) := by
    nlinarith

  -- Finally conclude k = 4 by cancelling 4 * x which is non-zero since x > 0
  have h6 : k = 4 := by
    nlinarith [show x > 0 by omega]

  exact h6