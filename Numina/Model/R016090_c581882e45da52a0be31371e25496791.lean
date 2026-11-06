import Mathlib

theorem algebra_213034 {a b c : ℝ} (h : (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3) :
    (a + b) ^ 2 * a * b + (b + c) ^ 2 * b * c + (c + a) ^ 2 * c * a +
    4 * a * b * c * (a + b + c) = 0 := by
  have h1 : 3 * (a + b) * (b + c) * (c + a) = 0 := by
    ring_nf at h ⊢
    linarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  cases' (mul_eq_zero.mp h2) with h4 h5
  · -- case a + b = 0
    have h6 : b = -a := by linarith
    rw [show b = -a by linarith]
    ring
  · -- case b + c = 0
    have h7 : c = -b := by linarith
    rw [show c = -b by linarith]
    ring
  · -- case c + a = 0
    have h8 : c = -a := by linarith
    rw [show c = -a by linarith]
    ring