import Mathlib

theorem number_theory_611197 :
    IsGreatest {k : ℝ | 0 < k ∧ ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 3 = k ^ 2 * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) + k * (x / y + y / x)} ((√7 - 1) / 2) := by
  constructor
  · -- Show that (sqrt(7) - 1)/2 is in the set
    constructor
    · -- Show it's positive
      nlinarith [Real.sqrt_pos.mpr (show 7 > 0 by norm_num : (7 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num : (7 : ℝ) ≥ 0), Real.sqrt_nonneg 7]
    · -- Find specific x,y that satisfy the equation
      use 1, 1
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Verify the equation
        nlinarith [Real.sqrt_pos.mpr (show (7: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (7 : ℝ) ≥ 0), sq_nonneg (√7 ^ 2 - 7: ℝ), sq_nonneg ( (√7 - 1) / 2 ), Real.sqrt_pos.mpr (by norm_num : (7 : ℝ) > 0)]
  · -- Show it's greatest
    intro k hk
    rcases hk with ⟨hk_pos, x, y, hx_pos, hy_pos, he⟩
    have h1 : x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 ≥ 2 := by
      have h2 : x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 - 2 ≥ 0 := by
        have h3 : x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 - 2 = (x^2 - y^2) ^ 2 / (x^2 * y^2) := by
          field_simp
          ring
        rw [h3]
        have h2_pos : (x ^ 2 - y ^ 2) ^ 2 ≥ 0 := by nlinarith
        have h4_pos : x^2 * y^2 > 0 := by
          positivity
        positivity
      linarith
    have h2 : x / y + y / x ≥ 2 := by
      have h2 : x / y + y / x - 2 ≥ 0 := by
        have h3 : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by
          field_simp
          ring
        rw [h3]
        have h2_pos : (x - y) ^ 2 ≥ 0 := by nlinarith
        have h4_pos : x * y > 0 := by
          positivity
        positivity
      linarith
    nlinarith [sq_nonneg (k + 1), sq_nonneg (k - (Real.sqrt 7 - 1) / 2), Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num : (7 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (7 : ℝ) ≥ 0), Real.sqrt_nonneg 7, sq_nonneg (k * (x ^ 2 / y ^ 2 - 1) ), sq_nonneg (k * (x / y - 1) ) ]