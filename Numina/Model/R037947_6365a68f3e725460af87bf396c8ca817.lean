import Mathlib

open Real

theorem inequalities_153367 :
    IsGreatest {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ t = (4 * x * z + y * z) / (x ^ 2 + y ^ 2 + z ^ 2)} (Real.sqrt 17 / 2) := by 
  constructor
  · -- Show √17 / 2 is in the set.
    use 4, 1, Real.sqrt 17
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show z > 0
      have h1 : Real.sqrt 17 > 0 := by
        positivity
      linarith
    · -- Show t = (4 * x * z + y * z) / (x ^ 2 + y ^ 2 + z ^ 2)
      have h2 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
      field_simp [h2]
      <;> nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
  · -- Show that √17 / 2 is the greatest element in the set
    intro t h
    rcases h with ⟨x, y, z, hx, hy, hz, ht⟩
    have h1 : (4 * x * z + y * z) ≤ (Real.sqrt 17 / 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
      have h3 : 0 ≤ (Real.sqrt 17) := by positivity
      have h4 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
      have h5 : (4 * x * z + y * z) ^ 2 ≤ (17 / 4) * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (x - 4 * y), sq_nonneg (z - Real.sqrt 17 * y), sq_nonneg (2 * x - 2 * y - (z * 4 / (Real.sqrt 17))), sq_nonneg (4 * x + y - 2 * z), sq_nonneg (y * 4 - x), sq_nonneg (z ^ 2 - 17 * y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - z ^ 2), Real.sqrt_nonneg 17, sq_nonneg (y - x / 4), sq_nonneg (z - Real.sqrt 17 * y / 1), sq_nonneg (4 * x - y), Real.sqrt_nonneg 17, sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (4 * x * x - y * y), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      have h7 : (4 * x * z + y * z) ≤ (Real.sqrt 17 / 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
        have h8 : (Real.sqrt 17 / 2) ≥ 0 := by positivity
        have h9 : (Real.sqrt 17 / 2) * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), h4, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      linarith
    have h2 : t ≤ Real.sqrt 17 / 2 := by
      rw [ht]
      apply (div_le_iff₀ (by positivity)).mpr 
      linarith [h1]
    linarith [h2]