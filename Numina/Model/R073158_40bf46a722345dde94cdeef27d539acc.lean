import Mathlib

theorem inequalities_660 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (x y : ℝ) (hx : x = (b^2 + 1) / a) (hy : y = (a^2 + 1) / b) :
    x > 2 ∨ y > 2 := by
  by_contra h
  push_neg at h
  have h1 : x ≤ 2 := by linarith [h.1]
  have h2 : y ≤ 2 := by linarith [h.2]
  have h3 : (b ^ 2 + 1) / a ≤ 2 := by
    linarith [show x ≤ 2 from h1, hx]
  have h4 : (a ^ 2 + 1) / b ≤ 2 := by
    linarith [show y ≤ 2 from h2, hy]
  have h5 : b ^ 2 + 1 ≤ 2 * a := by
    have h6 : 0 < a := ha
    have : (b ^ 2 + 1) ≤ 2 * a := by
      have h7 : (b ^ 2 + 1) / a ≤ 2 := h3
      have h8 : (b ^ 2 + 1) = (b ^ 2 + 1) / a * a := by
        field_simp [show a ≠ 0 by linarith]
      rw [h8] at *
      nlinarith
    linarith
  have h9 : a ^ 2 + 1 ≤ 2 * b := by
    have h10 : 0 < b := hb
    have : (a ^ 2 + 1) ≤ 2 * b := by
      have h11 : (a ^ 2 + 1) / b ≤ 2 := h4
      have h12 : (a ^ 2 + 1) = (a ^ 2 + 1) / b * b := by
        field_simp [show b ≠ 0 by linarith]
      rw [h12] at *
      nlinarith
    linarith
  have h13 : (a - 1) ^ 2 + (b - 1) ^ 2 ≤ 0 := by
    nlinarith
  have h14 : (a - 1) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h15 : (b - 1) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h16 : (a - 1) ^ 2 + (b - 1) ^ 2 = 0 := by
    nlinarith
  have ha1 : (a - 1) ^ 2 = 0 := by
    linarith [h14, h15, h16]
  have hb1 : (b - 1) ^ 2 = 0 := by
    linarith [h14, h15, h16]
  have ha2 : a - 1 = 0 := by
    rwa [sq_eq_zero_iff] at ha1
  have hb2 : b - 1 = 0 := by
    rwa [sq_eq_zero_iff] at hb1
  have h_eq : a = b := by
    linarith [show a = 1 from by linarith, show b = 1 from by linarith]
  contradiction