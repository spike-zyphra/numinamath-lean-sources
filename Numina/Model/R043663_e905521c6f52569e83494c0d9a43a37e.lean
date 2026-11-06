import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311794 (x y z : ℝ) (h : ¬(x=0 ∧ y=0 ∧ z=0)) :
    (x * y + 2 * y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ sqrt 5 / 2 := by

  have h1 : x ^ 2 + y ^ 2 + z ^ 2 > 0 := by
    by_contra h1
    push_neg at h1
    have h2 : x ^ 2 ≥ 0 := sq_nonneg x
    have h3 : y ^ 2 ≥ 0 := sq_nonneg y
    have h4 : z ^ 2 ≥ 0 := sq_nonneg z
    have h5 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by linarith [h1, h2, h3, h4]
    have h6 : x = 0 := by nlinarith
    have h7 : y = 0 := by nlinarith
    have h8 : z = 0 := by nlinarith
    have h9 : x = 0 ∧ y = 0 ∧ z = 0 := ⟨h6, h7, h8⟩
    contradiction
  have h2 : (x * y + 2 * y * z) ≤ Real.sqrt 5 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [ sq_nonneg (y ^ 2), sq_nonneg (x - z * 2 / 1), sq_nonneg (z + 2 * x),
        sq_nonneg (y - Real.sqrt 5 * x), sq_nonneg (y - Real.sqrt 5 * z / 2), sq_nonneg (x - z),
        sq_nonneg (y ^ 2 - (Real.sqrt 5 / 2) * y * (x + 2 * z)), sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2),
        Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        sq_nonneg (Real.sqrt 5 * x - y), sq_nonneg (Real.sqrt 5 * z - 2 * y) ]
  apply (div_le_iff₀ (by linarith)).mpr
  linarith