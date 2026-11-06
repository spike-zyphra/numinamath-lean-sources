import Mathlib
open Real

theorem algebra_609891 (a b c n: ℝ)
  (h01: a > 0) (h02: b > 0) (h03: c > 0) (h04: n > 0)
  (h1: (a+b)/a = 3) (h2: (b+c)/b = 4) : ((c+a)/c = 7/6) := by
  have h1' : a ≠ 0 := by linarith
  have h2' : b ≠ 0 := by linarith
  have h3' : c ≠ 0 := by linarith
  have h1a : a + b = 3 * a := by
    field_simp [h1'] at h1
    linarith
  have h1b : b = 2 * a := by linarith [h1a]
  have h2a : b + c = 4 * b := by
    field_simp [h2'] at h2
    linarith
  have h2b : c = 3 * b := by linarith [h2a]
  rw [show b = 2 * a by linarith [h1b]] at h2b
  have h2c : c = 6 * a := by linarith [h2b]
  have h4 : (c + a) / c = 7 / 6 := by
    have h5 : c + a = 7 * a := by
      linarith [h2c]
    have h6 : c = 6 * a := by
      linarith [h2c]
    rw [show c + a = 7 * a by linarith [h5]]
    rw [show c = 6 * a by linarith [h6]]
    have ha : a ≠ 0 := by linarith
    field_simp [ha]
    <;> linarith
  linarith [h4]