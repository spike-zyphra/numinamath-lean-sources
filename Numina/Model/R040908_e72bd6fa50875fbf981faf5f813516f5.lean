import Mathlib

open Real

theorem inequalities_143128 (c : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → x^2 + y^2 = 1 → x^6 + y^6 ≥ c * x * y) ↔
    c ≤ 1 / 2 := by
  constructor
  · -- Assume ∀ x, y > 0 with x² + y² =1, x⁶ + y⁶ ≥ c*x*y, prove c ≤1/2.
    intro h
    have h1 := h (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2)) (by positivity) (by positivity) (by
      have h1 : (Real.sqrt (1 / 2) : ℝ) ^ 2 + (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 := by
        have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
        nlinarith
      linarith
    )
    have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 = 1 / 4 := by
      calc
        (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 = 2 * ((Real.sqrt (1 / 2) : ℝ) ^ 6) := by ring
        _ = 2 * ((Real.sqrt (1 / 2) : ℝ) ^ 2) ^ 3 := by ring
        _ = 2 * (1 / 2) ^ 3 := by rw [h2]
        _ = 2 * (1 / 8) := by norm_num
        _ = 1 / 4 := by norm_num
    have h4 : (Real.sqrt (1 / 2) : ℝ) * (Real.sqrt (1 / 2) : ℝ) = 1 / 2 := by
      calc
        (Real.sqrt (1 / 2) : ℝ) * (Real.sqrt (1 / 2) : ℝ) = (Real.sqrt (1 / 2) : ℝ) ^ 2 := by ring
        _ = 1 / 2 := by rw [h2]
    nlinarith [h1, h3, h4]
  · -- Assume c ≤1/2, prove ∀x,y>0 with x²+y²=1, x⁶+y⁶ >=c*x*y.
    intro hc x y hx hy h
    have h1 : x^6 + y^6 = 1 - 3 * (x * y) ^ 2 := by
      calc
        x ^ 6 + y ^ 6 = (x^2) ^ 3 + (y^2) ^ 3 := by ring
        _ = (x^2 + y^2) ^ 3 - 3 * (x^2 * y^2) * (x^2 + y^2) := by ring
        _ = (1) ^ 3 - 3 * (x^2 * y^2) * (1) := by rw [h]
        _ = 1 - 3 * (x * y) ^ 2 := by
          ring_nf
    have h2 : x * y > 0 := mul_pos hx hy
    have h3 : x * y ≤ 1 / 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x ^ 2 + y ^ 2 - 1), sq_nonneg (x * y - 1 / 2)]
    have h4 : 3 * (x * y) ^ 2 + c * (x * y) - 1 ≤ 0 := by
      nlinarith [sq_nonneg (c - 1 / 2), sq_nonneg ((x * y) - 1 / 2), mul_nonneg (show (0 : ℝ) ≤ (1 / 2 - c) by nlinarith) (show (0 : ℝ) ≤ (1 / 2 - (x * y)) by nlinarith [h3]), sq_nonneg (x * y), h3, sq_nonneg (x * y - 1 / 2)]
    have h5 : x^6 + y^6 ≥ c * x * y := by
      nlinarith [h1, h4, h3, sq_nonneg (x * y), mul_pos hx hy, sq_nonneg (x * y - 1 / 2)]
    exact h5