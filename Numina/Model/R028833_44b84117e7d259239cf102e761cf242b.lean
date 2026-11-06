import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic


lemma lemma_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 - x * y + y ^ 2 > 0 := by
  have h3 : x ^ 2 - x * y + y ^ 2 = (x - y / 2) ^ 2 + (3 / 4) * y ^ 2 := by
    ring
  have h4 : (x - y / 2) ^ 2 + (3 / 4) * y ^ 2 > 0 := by
    have h1 : 0 < y := hy
    have h2 : 0 < y ^ 2 := by nlinarith
    have h9 : (3 / 4) * y ^ 2 > 0 := by
      nlinarith [show 0 < y ^ 2 by nlinarith]
    have h8 : (x - y / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  linarith [h3, h4]


theorem inequalities_130194
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    Real.sqrt (x ^ 2 + y ^ 2 - x * y) +
    Real.sqrt (y ^ 2 + z ^ 2 - y * z) ≥
    Real.sqrt (z ^ 2 + x ^ 2 + z * x) := by
  have h1 : x ^ 2 + y ^ 2 - x * y > 0 := by
    have h2 : x ^ 2 + y ^ 2 - x * y = x^2 - x * y + y^2 := by ring
    rw [h2]
    apply lemma_1 x y hx hy
  have h2 : y ^ 2 + z ^ 2 - y * z > 0 := by
    have h3 : y ^ 2 + z ^ 2 - y * z = y^2 - y * z + z^2 := by ring
    rw [h3]
    apply lemma_1 y z hy hz
  have h3 : z ^ 2 + x ^ 2 + z * x > 0 := by
    nlinarith [mul_pos hx hz, sq_pos_of_pos hx, sq_pos_of_pos hz]
  have h4 : Real.sqrt (x ^ 2 + y ^ 2 - x * y) + Real.sqrt (y ^ 2 + z ^ 2 - y * z) ≥ Real.sqrt (z ^ 2 + x ^ 2 + z * x) := by
    have h5 : Real.sqrt (x ^ 2 + y ^ 2 - x * y) ≥ 0 := by positivity
    have h6 : Real.sqrt (y ^ 2 + z ^ 2 - y * z) ≥ 0 := by positivity
    have h7 : Real.sqrt (z ^ 2 + x ^ 2 + z * x) ≥ 0 := by positivity
    have h50 : (Real.sqrt (x ^ 2 + y ^ 2 - x * y) + Real.sqrt (y ^ 2 + z ^ 2 - y * z)) ^ 2 ≥ (Real.sqrt (z ^ 2 + x ^ 2 + z * x)) ^ 2 := by
      have h8 : (Real.sqrt (x ^ 2 + y ^ 2 - x * y) + Real.sqrt (y ^ 2 + z ^ 2 - y * z)) ^ 2 =
          (Real.sqrt (x ^ 2 + y ^ 2 - x * y)) ^ 2 + (Real.sqrt (y ^ 2 + z ^ 2 - y * z)) ^ 2 + 2 * (Real.sqrt (x ^ 2 + y ^ 2 - x * y) * Real.sqrt (y ^ 2 + z ^ 2 - y * z)) := by ring
      rw [h8]
      have h9 : (Real.sqrt (z ^ 2 + x ^ 2 + z * x)) ^ 2 = z ^ 2 + x ^ 2 + z * x := by
        rw [Real.sq_sqrt]
        nlinarith
      have h10 : (Real.sqrt (x ^ 2 + y ^ 2 - x * y)) ^ 2 = x ^ 2 + y ^ 2 - x * y := by
        rw [Real.sq_sqrt]
        nlinarith
      have h11 : (Real.sqrt (y ^ 2 + z ^ 2 - y * z)) ^ 2 = y ^ 2 + z ^ 2 - y * z := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + y ^ 2 - x * y) ^ 2 - Real.sqrt (y ^ 2 + z ^ 2 - y * z) ^ 2), sq_nonneg (Real.sqrt (x ^ 2 + y ^ 2 - x * y) - Real.sqrt (y ^ 2 + z ^ 2 - y * z)), sq_nonneg (x * y - x * z + y * z), sq_nonneg (Real.sqrt (x ^ 2 + y ^ 2 - x * y) * Real.sqrt (y ^ 2 + z ^ 2 - y * z) - (z ^ 2 + x ^ 2 + z * x - (x ^ 2 + y ^ 2 - x * y) - (y ^ 2 + z ^ 2 - y * z)) / 2), Real.sqrt_nonneg (x ^ 2 + y ^ 2 - x * y), Real.sqrt_nonneg (y ^ 2 + z ^ 2 - y * z), Real.sqrt_nonneg (z ^ 2 + x ^ 2 + z * x), sq_nonneg (Real.sqrt (x ^ 2 + y ^ 2 - x * y) ^ 2 + Real.sqrt (y ^ 2 + z ^ 2 - y * z) ^ 2 - (z ^ 2 + x ^ 2 + z * x)), Real.mul_self_sqrt (show 0 ≤ (x ^ 2 + y ^ 2 - x * y : ℝ) by nlinarith), Real.mul_self_sqrt (show 0 ≤ (y ^ 2 + z ^ 2 - y * z : ℝ) by nlinarith), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + y ^ 2 - x * y)) (Real.sqrt_nonneg (y ^ 2 + z ^ 2 - y * z)), sq_nonneg (x * y - x * z + y * z)]
    nlinarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2 - x * y), Real.sqrt_nonneg (y ^ 2 + z ^ 2 - y * z), Real.sqrt_nonneg (z ^ 2 + x ^ 2 + z * x), h50]
  exact h4