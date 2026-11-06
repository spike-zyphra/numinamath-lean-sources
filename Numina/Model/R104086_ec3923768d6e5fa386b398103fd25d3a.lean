import Mathlib

theorem algebra_194283 (v : ℝ) (h : v > 0) (h1 : 10 / (v + 7) + 20 / v = 1) :
    v = 28 := by
  have h2 : v + 7 ≠ 0 := by
    linarith
  have h3 : v ≠ 0 := by linarith
  field_simp [(show v + 7 ≠ 0 by assumption), (show v ≠ 0 by assumption)] at h1
  ring_nf at h1
  have h4 : v^2 - 23 * v - 140 = 0 := by
    nlinarith
  have h5 : (v - 28) * (v + 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where \( v - 28 = 0 \)
    linarith
  · -- Case where \( v + 5 = 0 \)
    have : v < 0 := by linarith
    linarith