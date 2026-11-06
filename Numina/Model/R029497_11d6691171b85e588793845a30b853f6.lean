import Mathlib

open Real

theorem algebra_21454 :
    IsLeast {((sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2)) / (x + y + z)) |
      (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) (z : ℝ) (hz : 0 < z)} (sqrt 2) := by
  constructor
  · -- Show sqrt 2 is in the set
    use 1, by norm_num, 1, by norm_num, 1, by norm_num
    have h1 : sqrt (1 ^ 2 + (1 : ℝ) ^ 2) = Real.sqrt 2 := by
      norm_num
    rw [h1]
    field_simp
    <;> ring_nf <;> norm_num
  · -- Show sqrt 2 is minimal
    intro r hr
    rcases hr with ⟨x, hx, y, hy, z, hz, hr⟩
    have h4 : sqrt (x ^ 2 + y ^ 2) ≥ (x + y) / Real.sqrt 2 := by
      have h7 : Real.sqrt (x ^ 2 + y ^ 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
      have h8 : Real.sqrt 2 > 0 := by positivity
      have h9 : (x + y) / Real.sqrt 2 ≥ 0 := by
        apply div_nonneg
        linarith [show 0 < x from hx, show 0 < y from hy]
        positivity
      have h10 : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 ≥ ((x + y) / Real.sqrt 2) ^ 2 := by
        have h7 : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 by positivity)
        have h8 : ((x + y) / Real.sqrt 2) ^ 2 = (x + y) ^ 2 / (Real.sqrt 2) ^ 2 := by
          field_simp
        have h9 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        rw [h7, h8, h9]
        have h8 : (x^2 + y^2 : ℝ) ≥ ((x + y) ^ 2 / (2 : ℝ)) := by
          have h9 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by ring
          rw [h9]
          have h13 : x ^ 2 + y ^ 2 ≥ 2 * (x * y) := by
            nlinarith [sq_nonneg (x - y)]
          nlinarith [sq_nonneg (x - y)]
        linarith
      nlinarith [h7, h9, Real.sqrt_nonneg 2]
    have h5 : sqrt (x ^ 2 + z ^ 2) ≥ (x + z) / Real.sqrt 2 := by
      have h7 : Real.sqrt (x ^ 2 + z ^ 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + z ^ 2)
      have h8 : Real.sqrt 2 > 0 := by positivity
      have h9 : (x + z) / Real.sqrt 2 ≥ 0 := by
        apply div_nonneg
        linarith [show 0 < x from hx, show 0 < z from hz]
        positivity
      have h10 : (Real.sqrt (x ^ 2 + z ^ 2)) ^ 2 ≥ ((x + z) / Real.sqrt 2) ^ 2 := by
        have h7 : (Real.sqrt (x ^ 2 + z ^ 2)) ^ 2 = x ^ 2 + z ^ 2 := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + z ^ 2 by positivity)
        have h8 : ((x + z) / Real.sqrt 2) ^ 2 = (x + z) ^ 2 / (Real.sqrt 2) ^ 2 := by
          field_simp
        have h9 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        rw [h7, h8, h9]
        have h8 : (x^2 + z^2 : ℝ) ≥ ((x + z) ^ 2 / (2 : ℝ)) := by
          have h9 : (x + z) ^ 2 = x^2 + z^2 + 2 * (x * z) := by ring
          rw [h9]
          have h13 : x ^ 2 + z ^ 2 ≥ 2 * (x * z) := by
            nlinarith [sq_nonneg (x - z)]
          nlinarith [sq_nonneg (x - z)]
        linarith
      nlinarith [h7, h9, Real.sqrt_nonneg 2]
    have h6 : sqrt (y ^ 2 + z ^ 2) ≥ (y + z) / Real.sqrt 2 := by
      have h7 : Real.sqrt (y ^ 2 + z ^ 2) ≥ 0 := Real.sqrt_nonneg (y ^ 2 + z ^ 2)
      have h8 : Real.sqrt 2 > 0 := by positivity
      have h9 : (y + z) / Real.sqrt 2 ≥ 0 := by
        apply div_nonneg
        linarith [show 0 < y from hy, show 0 < z from hz]
        positivity
      have h10 : (Real.sqrt (y ^ 2 + z ^ 2))  ^ 2 ≥ ((y + z) / Real.sqrt 2) ^ 2 := by
        have h7 : (Real.sqrt (y ^ 2 + z ^ 2)) ^ 2 = y ^ 2 + z ^ 2 := Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + z ^ 2 by positivity)
        have h8 : ((y + z) / Real.sqrt 2) ^ 2 = (y + z) ^ 2 / (Real.sqrt 2) ^ 2 := by
          field_simp
        have h9 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        rw [h7, h8, h9]
        have h8 : (y^2 + z^2 : ℝ) ≥ ((y + z) ^ 2 / (2 : ℝ)) := by
          have h9 : (y + z) ^ 2 = y^2 + z^2 + 2 * (y * z) := by ring
          rw [h9]
          have h13 : y ^ 2 + z ^ 2 ≥ 2 * (y * z) := by
            nlinarith [sq_nonneg (y - z)]
          nlinarith [sq_nonneg (y - z)]
        linarith
      nlinarith [h7, h9, Real.sqrt_nonneg 2]
    have h7 : sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2) ≥ Real.sqrt 2 * (x + y + z) := by
      have h8 : sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2) ≥ ((x + y) / Real.sqrt 2 + (x + z) / Real.sqrt 2 + (y + z) / Real.sqrt 2) := by 
        linarith [h4, h5, h6]
      have h9 : ((x + y) / Real.sqrt 2 + (x + z) / Real.sqrt 2 + (y + z) / Real.sqrt 2) = Real.sqrt 2 * (x + y + z) := by 
        field_simp
        <;> ring_nf <;> norm_num
      linarith [h8, h9]
    have h8 : ((sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2)) / (x + y + z)) ≥ Real.sqrt 2 := by
      have h5 : (x + y + z) > 0 := by
        linarith [show 0 < x from hx, show 0 < y from hy, show 0 < z from hz]
      have h3 : sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2) ≥ Real.sqrt 2 * (x + y + z) := h7
      have h6 : ((sqrt (x ^ 2 + y ^ 2) + sqrt (x ^ 2 + z ^ 2) + sqrt (y ^ 2 + z ^ 2)) / (x + y + z)) ≥ Real.sqrt 2 := by
        apply (le_div_iff₀ (by positivity)).mpr 
        linarith 
      linarith
    linarith [h8, hr]