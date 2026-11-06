import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_309313 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ t = (x * y + y * z) / (x ^ 2 + y ^ 2 + z ^ 2)} (Real.sqrt 2 / 2) := by
  constructor
  · -- First, show that sqrt(2)/2 is in the set.
    use 1, Real.sqrt 2, 1
    constructor
    · -- Show that not all of 1, sqrt 2, 1 are zero
      left
      norm_num
    · -- Show that sqrt 2 / 2 = (1 * sqrt 2 + sqrt 2 * 1) / (1 ^ 2 + (sqrt 2) ^ 2 + 1 ^ 2)
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      have h2 : (1 * Real.sqrt 2 + Real.sqrt 2 * 1 : ℝ) / (1 ^ 2 + Real.sqrt 2 ^ 2 + 1 ^ 2) = Real.sqrt 2 / 2 := by
        rw [h1]
        ring_nf
      linarith [h2]
  · -- Now, show that sqrt 2 / 2 is the greatest element in the set
    intro t ht
    rcases ht with ⟨x, y, z, hne, heq⟩
    have h1 : x ^ 2 + y ^ 2 + z ^ 2 > 0 := by
      by_contra h
      push_neg at h
      have h2 : x ^ 2 ≥ 0 := sq_nonneg x
      have h3 : y ^ 2 ≥ 0 := sq_nonneg y
      have h4 : z ^ 2 ≥ 0 := sq_nonneg z
      have h5 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by linarith [h2, h3, h4, h]
      have hx : x = 0 := by nlinarith
      have hy : y = 0 := by nlinarith
      have hz : z = 0 := by nlinarith
      rcases hne with (h11 | h12 | h13)
      · -- x ≠ 0
        tauto
      · -- y ≠ 0
        tauto
      · -- z ≠ 0
        tauto
    have h2 : (x * y + y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ Real.sqrt 2 / 2 := by
      have h3 : 2 * (x * y + y * z) ≤ Real.sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
        have h4 : Real.sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * (x * y + y * z) := by
          nlinarith [sq_nonneg (x - z), sq_nonneg (x - Real.sqrt 2 / 2 * y), sq_nonneg (z - Real.sqrt 2 / 2 * y), sq_nonneg (y ^ 2), sq_nonneg ((x + z) - Real.sqrt 2 * y), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), sq_nonneg (y - (x + z) * Real.sqrt 2 / 2), sq_nonneg (y ^ 2 - (x ^ 2 + z ^ 2)), sq_nonneg ((x + z) ^ 2 - (y ^ 2)), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
        linarith
      have h4 : 2 * (x * y + y * z) ≤ Real.sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
        linarith
      have h5 : (x * y + y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ Real.sqrt 2 / 2 := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    linarith [heq, h2]