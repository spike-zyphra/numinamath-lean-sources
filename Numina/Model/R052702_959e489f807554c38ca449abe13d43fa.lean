import Mathlib

theorem algebra_159849 {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hroots1 : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0)
    (hroots2 : ∃ x y, x ≠ y ∧ x^2 + q * x + p = 0 ∧ y^2 + q * y + p = 0) :
    ∃ x y, x ≠ y ∧ x^2 + (p + q) * x + 2 * (p + q) = 0 ∧
    y^2 + (p + q) * y + 2 * (p + q) = 0 := by
  obtain ⟨x, y, hxy, hx1, hy1⟩ := hroots1
  have h1 : (x - y) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h
    apply hxy
    linarith
  have h_eq1 : p^2 - 4 * q > 0 := by
    have h2 : (x + y) ^ 2 - 4 * (x * y) > 0 := by nlinarith
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by intro h; apply hxy; nlinarith),
       sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y),
       sq_nonneg (x^2), sq_nonneg (y^2)]
  rcases hroots2 with ⟨u, v, huv, hu2, hv2⟩
  have h5 : (u - v) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h
    apply huv
    linarith
  have h_eq2 : q^2 - 4 * p > 0 := by
    have h6 : (u + v) ^ 2 - 4 * (u * v) > 0 := by nlinarith
    nlinarith [sq_pos_of_ne_zero (show u - v ≠ 0 by intro h; apply huv; nlinarith),
       sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg (u * v),
       sq_nonneg (u^2), sq_nonneg (v^2)]
  have h7 : (p + q) ^ 2 - 8 * (p + q) > 0 := by
    nlinarith [sq_nonneg (p - q), h_eq1, h_eq2, mul_pos hp hq]
  use (- (p + q) + Real.sqrt ((p + q) ^ 2 - 8 * (p + q))) / 2,
    (- (p + q) - Real.sqrt ((p + q) ^ 2 - 8 * (p + q))) / 2
  constructor
  · -- Show the two roots are distinct
    by_contra h_eq
    have h8 : Real.sqrt ((p + q) ^ 2 - 8 * (p + q)) = 0 := by
      nlinarith
    have h9 : (p + q) ^ 2 - 8 * (p + q) = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith)] at h8
      nlinarith
    linarith
  constructor
  · -- Show the first value is a solution
    nlinarith [Real.sqrt_nonneg ((p + q) ^ 2 - 8 * (p + q)), 
      Real.sq_sqrt (show ((p + q) ^ 2 - 8 * (p + q)) ≥ 0 by nlinarith)]
  · -- Show the second value is a solution
    nlinarith [Real.sqrt_nonneg ((p + q) ^ 2 - 8 * (p + q)), 
      Real.sq_sqrt (show ((p + q) ^ 2 - 8 * (p + q)) ≥ 0 by nlinarith)]