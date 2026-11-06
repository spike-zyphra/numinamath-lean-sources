import Mathlib

theorem algebra_323723 {a b c x : ℝ} (ha : a + x ^ 2 = 1991) (hb : b + x ^ 2 = 1992)
    (hc : c + x ^ 2 = 1993) (habc : a * b * c = 24) :
    a / (b * c) + b / (a * c) + c / (a * b) - 1 / a - 1 / b - 1 / c = 1 / 8 := by
  have h1 : b = a + 1 := by
    nlinarith [ha, hb]
  have h2 : c = a + 2 := by
    nlinarith [ha, hc, h1]
  rw [h1, h2] at habc
  have h3 : a = 2 := by
    have h4 : a ^ 3 + 3 * a ^ 2 + 2 * a - 24 = 0 := by
      ring_nf at habc ⊢
      nlinarith
    have h5 : a ^ 3 + 3 * a ^ 2 + 2 * a - 24 = (a - 2) * (a ^ 2 + 5 * a + 12) := by
      ring
    rw [h5] at h4
    cases (mul_eq_zero.1 h4) with
    | inl h6 =>
      linarith
    | inr h7 =>
      have h8 : a ^ 2 + 5 * a + 12 = 0 := by 
        linarith 
      have h9 : a ^ 2 + 5 * a + 12 > 0 := by
        nlinarith [sq_nonneg (a + 5 / 2)]
      linarith 
  have h4 : b = 3 := by
    rw [h3] at h1
    linarith
  have h5 : c = 4 := by
    rw [h3] at h2
    linarith 
  rw [h3, h4, h5]
  norm_num 
  <;> nlinarith 
  <;> norm_num 
  <;> nlinarith