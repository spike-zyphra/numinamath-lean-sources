import Mathlib
open Real
set_option maxHeartbeats 800000

theorem inequalities_235610 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) :
    √(x^3 + y) + √(y^3 + x) ≥ √(x^3 + x) + √(y^3 + y) := by
  have h1 : (√(x^3 + y) + √(y^3 + x)) ^2 ≥ (√(x^3 + x) + √(y^3 + y)) ^2 := by
    have h2 : (√(x^3 + y) + √(y^3 + x)) ^2 = (√(x^3 + y)) ^2 + (√(y^3 + x)) ^2 + 2 * (√(x^3 + y) * √(y^3 + x)) := by
      ring
    have h3 : (√(x^3 + x) + √(y^3 + y)) ^2 = (√(x^3 + x)) ^2 + (√(y^3 + y)) ^2 + 2 * (√(x^3 + x) * √(y^3 + y)) := by
      ring
    rw [h2, h3]
    have h4 : (√(x^3 + y)) ^2 = x^3 + y := by
      rw [Real.sq_sqrt]
      have h71 : x^3 + y ≥ 0 := by
        have h711 : x ^ 3 ≥ 0 := by
          have h100 : x ≥ 0 := by linarith [hx]
          positivity
        nlinarith [hy, h711]
      linarith
    have h5 : (√(y^3 + x)) ^2 = y^3 + x := by
      rw [Real.sq_sqrt]
      have h71 : y^3 + x ≥ 0 := by
        have h711 : y ^ 3 ≥ 0 := by
          have h100 : y ≥ 0 := by linarith [hy]
          positivity
        nlinarith [hx, h711]
      linarith
    have h6 : (√(x^3 + x)) ^2 = x^3 + x := by
      rw [Real.sq_sqrt]
      have h71 : x^3 + x ≥ 0 := by
        have h711 : x ^ 3 ≥ 0 := by
          have h100 : x ≥ 0 := by linarith [hx]
          positivity
        nlinarith [hx, h711]
      linarith
    have h7 : (√(y^3 + y)) ^2 = y^3 + y := by
      rw [Real.sq_sqrt]
      have h71 : y^3 + y ≥ 0 := by
        have h711 : y ^ 3 ≥ 0 := by
          have h100 : y ≥ 0 := by linarith [hy]
          positivity
        nlinarith [hy, h711]
      linarith
    have h8 : (√(x^3 + y) * √(y^3 + x)) ≥ (√(x^3 + x) * √(y^3 + y)) := by
      have h9 : (√(x^3 + y) * √(y^3 + x)) ^2 ≥ (√(x^3 + x) * √(y^3 + y)) ^2 := by
        have h10 : (√(x^3 + y) * √(y^3 + x)) ^2 = (x^3 + y) * (y^3 + x) := by
          calc
            (√(x^3 + y) * √(y^3 + x)) ^2 = (√(x^3 + y)) ^2 * (√(y^3 + x)) ^2 := by ring
            _ = (x^3 + y) * (y^3 + x) := by
              rw [h4, h5]
        have h11 : (√(x^3 + x) * √(y^3 + y)) ^2 = (x^3 + x) * (y^3 + y) := by
          calc
            (√(x^3 + x) * √(y^3 + y)) ^2 = (√(x^3 + x)) ^2 * (√(y^3 + y)) ^2 := by ring
            _ = (x^3 + x) * (y^3 + y) := by
              rw [h6, h7]
        rw [h10, h11]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), mul_nonneg hx hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - y * x)]
      have h12 : √(x^3 + y) * √(y^3 + x) ≥ 0 := by positivity
      have h13 : √(x^3 + x) * √(y^3 + y) ≥ 0 := by positivity
      nlinarith [h9, Real.sqrt_nonneg (x^3 + y), Real.sqrt_nonneg (y^3 + x), Real.sqrt_nonneg (x^3 + x), Real.sqrt_nonneg (y^3 + y)]
    nlinarith [h4, h5, h6, h7, h8]
  have h9 : √(x^3 + y) + √(y^3 + x) ≥ 0 := by positivity
  have h10 : √(x^3 + x) + √(y^3 + y) ≥ 0 := by positivity
  nlinarith [h1, Real.sqrt_nonneg (x^3 + y), Real.sqrt_nonneg (y^3 + x),
    Real.sqrt_nonneg (x^3 + x), Real.sqrt_nonneg (y^3 + y)]