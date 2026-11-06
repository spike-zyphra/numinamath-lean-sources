import Mathlib

theorem algebra_212038 (x y z : ℝ) (h1 : x + y - z = -1) (h2 : x^2 - y^2 + z^2 = 1) (h3 : -x^3 + y^3 + z^3 = -1) :
    (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = -1 ∧ z = -1) := by
  have h4 : z = x + y + 1 := by
    linarith
  rw [h4] at h2
  have h5 : (x + y) * (x + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- case where `x + y = 0`
    have h8 : y = -x := by linarith
    have h9 : z = 1 := by
      nlinarith [h8, h4]
    have h10 : x = 1 := by
      rw [show y = -x by linarith [h8], show z = (1 : ℝ) by linarith [h9]] at h3
      have h11 : x^3 = 1 := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((-x : ℝ) ^ 2), sq_nonneg ((1 : ℝ) ^ 2)]
      have h12 : x = 1 := by
        have h13 : x^3 - 1 = 0 := by linarith
        have h14 : (x - 1) * (x^2 + x + 1) = 0 := by
          ring_nf at h13 ⊢
          linarith
        cases' (mul_eq_zero.mp h14) with h15 h16 
        · -- case where `x - 1 = 0`
          linarith
        · -- case where `x^2 + x + 1 = 0`
          nlinarith [sq_nonneg (x + 1 / 2)]
      linarith
    have h13 : y = -1 := by 
      rw [h10] at h8
      linarith
    have h14 : z = 1 := by
      linarith [h9]
    left
    constructor
    · -- x = 1
      linarith [h10]
    constructor
    · -- y = -1
      linarith [h13]
    · -- z = 1
      linarith [h14]
  · -- case where `x + 1 = 0`
    have h8 : x = -1 := by linarith
    have h9 : z = y := by
      nlinarith [h8, h4]
    have h10 : y = -1 := by
      rw [show x = -1 by linarith [h8], show z = y by linarith [h9]] at h3
      have h11 : y^3 = -1 := by
        nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y + 1), sq_nonneg ((y : ℝ) * y)]
      have h12 : y = -1 := by
        have h13 : y^3 + 1 = 0 := by linarith
        have h14 : (y + 1) * (y^2 - y + 1) = 0 := by 
          ring_nf at h13 ⊢
          linarith
        cases' (mul_eq_zero.mp h14) with h15 h16
        · -- case where `y + 1 = 0`
          linarith
        · -- case where `y^2 - y + 1 = 0`
          nlinarith [sq_nonneg (y - 1 / 2)]
      linarith
    have h11 : z = -1 := by
      nlinarith [h9, h10]
    right
    constructor
    · -- x = -1
      linarith [h8]
    constructor
    · -- y = -1
      linarith [h10]
    · -- z = -1
      linarith [h11]