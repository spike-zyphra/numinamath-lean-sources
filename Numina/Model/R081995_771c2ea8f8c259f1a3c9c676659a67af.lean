import Mathlib

theorem algebra_320584 {a b : ℝ} (ha : a^2 + 2 * a - 5 = 0) (hb : b^2 + 2 * b - 5 = 0)
    (hab : a ≠ b) : a * b^2 + a^2 * b = 10 := by
  have h1 : a^2 + 2 * a - 5 = 0 := ha
  have h2 : b^2 + 2 * b - 5 = 0 := hb
  have h3 : a^2 + 2 * a - 5 - (b^2 + 2 * b - 5) = 0 := by linarith
  have h4 : (a - b) * (a + b + 2) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $a - b = 0$
    exfalso
    exact hab (by linarith)
  · -- Case where $a + b + 2 = 0$
    have h7 : a + b = -2 := by linarith
    have h8 : a * b = -5 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hab)]
    have h9 : a * b^2 + a^2 * b = (a * b) * (a + b) := by
      ring
    rw [h9, h7, h8]
    norm_num