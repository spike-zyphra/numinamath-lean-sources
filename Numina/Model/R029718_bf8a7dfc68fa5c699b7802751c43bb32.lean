import Mathlib

theorem inequalities_173302 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x) ≥ Real.sqrt x + Real.sqrt y := by
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have h3 : Real.sqrt (x ^ 2 / y) ≥ 0 := by positivity
  have h4 : Real.sqrt (y ^ 2 / x) ≥ 0 := by positivity
  have h5 : Real.sqrt x ≥ 0 := by positivity
  have h6 : Real.sqrt y ≥ 0 := by positivity

  have h7 : (Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x)) ^ 2 ≥ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h8 : (Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x)) ^ 2 =
        (Real.sqrt (x ^ 2 / y)) ^ 2 + (Real.sqrt (y ^ 2 / x)) ^ 2 + 2 * (Real.sqrt (x ^ 2 / y) * Real.sqrt (y ^ 2 / x)) := by
      ring
    have h9 : (Real.sqrt x + Real.sqrt y) ^ 2 = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by
      ring
    rw [h8, h9]
    have h10 : (Real.sqrt (x ^ 2 / y)) ^ 2 = x ^ 2 / y := by
      rw [Real.sq_sqrt]
      positivity
    have h11 : (Real.sqrt (y ^ 2 / x)) ^ 2 = y ^ 2 / x := by
      rw [Real.sq_sqrt]
      positivity
    have h12 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    have h13 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
    have h14 : Real.sqrt (x ^ 2 / y) * Real.sqrt (y ^ 2 / x) = Real.sqrt (x * y) := by
      have h15 : Real.sqrt (x ^ 2 / y) * Real.sqrt (y ^ 2 / x) = Real.sqrt ((x ^ 2 / y) * (y ^ 2 / x)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h15]
      have h16 : (x ^ 2 / y) * (y ^ 2 / x) = x * y := by
        field_simp
        <;> ring
      rw [h16]
    have h17 : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := by
      rw [← Real.sqrt_mul (by positivity)]
    rw [h10, h11, h12, h13, h14, h17]
    have h8 : x ^ 2 / y + y ^ 2 / x ≥ x + y := by
      have h9 : x ^ 2 / y + y ^ 2 / x - (x + y) ≥ 0 := by
        have h11 : x ^ 2 / y + y ^ 2 / x - (x + y) = (x ^ 3 + y ^ 3 - (x + y) * (x * y)) / (x * y) := by
          field_simp
          ring
        rw [h11]
        have h12 : x ^ 3 + y ^ 3 - (x + y) * (x * y) ≥ 0 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy]
        have h13 : x * y > 0 := mul_pos hx hy
        apply div_nonneg
        . linarith
        . positivity
      linarith
    nlinarith [Real.sqrt_nonneg (x * y), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (Real.sqrt (x ) - Real.sqrt (y )), Real.sqrt_nonneg (x ), Real.sqrt_nonneg (y ), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ x * y by positivity)]
  have h8 : Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x) ≥ Real.sqrt x + Real.sqrt y := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 / y), Real.sqrt_nonneg (y ^ 2 / x), Real.sqrt_nonneg x, Real.sqrt_nonneg y, h7, sq_nonneg (Real.sqrt (x ^ 2 / y) - Real.sqrt (y ^ 2 / x)), sq_nonneg (Real.sqrt x - Real.sqrt y), mul_pos hx hy]
  linarith