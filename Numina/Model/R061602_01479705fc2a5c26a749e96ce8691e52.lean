import Mathlib

theorem algebra_1821
    (a b c x y z : ℝ)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hz : z ≠ 0)
    (h₀ : a + b + c = 0)
    (h₁ : x + y + z = 0)
    (h₂ : a * x + b * y + c * z = 0) :
    a ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) + x ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) = 2 / 3 := by
  have h3 : c = -a - b := by linarith
  have h4 : z = -x - y := by linarith
  rw [h3, h4] at h₂
  have h5 : a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a^2 + a * b + b^2) := by
    rw [h3]
    ring
  have h6 : x ^ 2 + y ^ 2 + z ^ 2 = 2 * (x^2 + x * y + y^2) := by
    rw [h4]
    ring
  rw [h5, h6]
  have h7 : 2 * (a^2 + a * b + b^2) ≠ 0 := by
    by_contra h
    have : a^2 + a * b + b^2 = 0 := by nlinarith
    have h8 : a^2 + a * b + b^2 > 0 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
    linarith
  have h8' : 2 * (a^2 + a * b + b^2) ≠ 0 := by
    by_contra h
    have : a^2 + a * b + b^2 = 0 := by nlinarith
    have h8 : a^2 + a * b + b^2 > 0 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
    linarith
  have h9 : 2 * (x^2 + x * y + y^2) ≠ 0 := by
    by_contra h
    have : x^2 + x * y + y^2 = 0 := by nlinarith
    have h10 : x^2 + x * y + y^2 > 0 := by
      nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
    linarith
  have h9' : 2 * (x^2 + x * y + y^2) ≠ 0 := by
    by_contra h
    have : x^2 + x * y + y^2 = 0 := by nlinarith
    have h10 : x^2 + x * y + y^2 > 0 := by
      nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
    linarith
  field_simp [h8', h9']
  nlinarith [sq_nonneg (a * x - b * y), sq_nonneg (a * x - b * y), sq_nonneg (a - b), sq_nonneg (x - y), sq_nonneg (a * (x - y) - b * (x - y)), sq_nonneg (a * x + b * y - (-a - b) * (-x - y)), sq_nonneg (a + b + (-a - b)), sq_nonneg (x + y + (-x - y)), sq_nonneg (a - x), sq_nonneg (b - y)]