import Mathlib

theorem algebra_14352 {x : ℝ} (h : 4 / x ^ 2 = x / 16) (hx : x ≠ 0) : x = 4 := by
  have h1 : x ^ 3 = 64 := by
    field_simp [show x ≠ 0 by exact hx] at h
    nlinarith
  -- Now we need to solve x^3 = 64 over the reals. 
  -- This equation has a unique real solution x = 4.
  have h2 : x ^ 3 - 64 = 0 := by 
    linarith
  -- Factoring the equation
  have h3 : (x - 4) * (x ^ 2 + 4 * x + 16) = 0 := by
    ring_nf at h2 ⊢
    linarith
  -- Either x - 4 = 0 or x^2 + 4x + 16 = 0
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where x - 4 = 0, so x = 4
    linarith
  · -- Show that x^2 + 4x + 16 = 0 has no real solutions
    have h6 : x ^ 2 + 4 * x + 16 > 0 := by
      nlinarith [sq_nonneg (x + 2)]
    have h7 : x ^ 2 + 4 * x + 16 = 0 := by linarith
    linarith