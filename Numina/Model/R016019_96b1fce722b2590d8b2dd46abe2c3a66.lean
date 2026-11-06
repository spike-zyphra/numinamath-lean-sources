import Mathlib

theorem algebra_182575 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x = 6.8 * y) (h2 : y * 5 = x * 6.2) :
    x / y * 100 = 66.7 ∧ y / x * 100 = 73.1 := by
  -- Given h1 and h2
  -- x = 6.8 * y
  -- y * 5 = x * 6.2
  have h3 : x = 6.8 * y := h1
  rw [h3] at h2
  -- Substitute x in h2
  -- We get y * 5 = (6.8 * y) * 6.2
  -- y * 5 = 42.16 * y
  -- y * (5 - 42.16) = 0
  have h4 : (y * 5) = (6.8 * y) * 6.2 := by
    linarith
  -- Rewrite equate to
  -- y * 5 = y * (6.8 * 6.2)
  -- 5 * y = (42.16) * y
  -- y * (5 - 42.16) = 0
  -- y * (-37.16) = 0
  have h5 : y * (5 - 42.16) = 0 := by
    ring_nf at h4 ⊢
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- first case h6 : y = 0
    linarith -- contradicts hy
  · -- second case h7 : 5 - 42.16 = 0
    norm_num at h7