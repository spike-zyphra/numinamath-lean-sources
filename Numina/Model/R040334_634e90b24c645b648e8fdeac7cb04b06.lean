import Mathlib

open Real Set

theorem algebra_12173 : IsGreatest {z : ℝ | ∃ x y, z = (2 * x + sqrt 2 * y) / (2 * x ^ 4 + 4 * y ^ 4 + 9)} (1 / 4) := by
  constructor
  · -- Show 1/4 is in the set
    use 1, Real.sqrt 2 / 2
    have h1 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
    have h2 : sqrt 2 ^ 4 = (sqrt 2 ^ 2) ^ 2 := by ring
    rw [h1] at h2
    have h3 : sqrt 2 ^ 4 = 4 := by
      rw [h2]
      norm_num
    have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = 1 / 4 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = (Real.sqrt 2 ^ 4) / (2 ^ 4) := by
          field_simp
        _ = 4 / 16 := by
          rw [h3]
          all_goals norm_num
        _ = 1 / 4 := by norm_num
    norm_num [h4, h3]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show 1/4 is the greatest
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h3 : (2 * x + sqrt 2 * y) / (2 * x ^ 4 + 4 * y ^ 4 + 9) ≤ (1 / 4 : ℝ) := by
      have h4 : 0 < (2 * x ^ 4 + 4 * y ^ 4 + 9 : ℝ) := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x), sq_nonneg (y), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      apply (div_le_div_iff (by linarith) (by linarith)).mpr
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - Real.sqrt 2 / 2), sq_nonneg (x + 1), sq_nonneg (y + Real.sqrt 2 / 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg (x - Real.sqrt 2 * y), sq_nonneg (x ^ 2 - (Real.sqrt 2 / 2) ^ 2), sq_nonneg (y ^ 2 - (1 / 2) ^ 2), sq_nonneg (x * (x - 1)), sq_nonneg (y * (y - Real.sqrt 2 / 2)), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x ^ 2 * y ^ 2 - 1 / 4)]
    have h4 : z ≤ (1 / 4 : ℝ) := by
      linarith [hz, h3]
    linarith