import Mathlib

open BigOperators Real Set

lemma lemma_1 (x y z : ℝ) (h : x^2 + y^2 + z^2 = 1) :
    y * (x + z) ≤ sqrt 2 / 2 := by
  have h1 : (x + z) ^ 2 ≤ 2 * (x^2 + z^2) := by
    have h2 : (x - z) ^ 2 ≥ 0 := sq_nonneg (x - z)
    nlinarith
  have h4 : x^2 + z^2 = 1 - y^2 := by
    nlinarith
  have h3 : (x + z) ^ 2 ≤ 2 * (1 - y^2) := by
    nlinarith [h1, h4]
  have h5 : y * (x + z) ≤ Real.sqrt 2 / 2 := by
    nlinarith [sq_nonneg (y - (x + z)), sq_nonneg (y + (x + z)), sq_nonneg (x + z), sq_nonneg (y), sq_nonneg (x - z), sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg ((x + z) ^ 2 - 1 / 2), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  exact h5


theorem algebra_305603 :
  IsGreatest {t : ℝ | ∃ x y z, t = x * y + y * z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 1} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt(2)/2 is in the set
    use 1 / 2, Real.sqrt 2 / 2, 1 / 2
    constructor
    · -- Show t = x * y + y * z
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show x^2 + y^2 + z^2 = 1
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that sqrt(2)/2 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, z, ht_eq, h_eq⟩
    have h14 : y * (x + z) ≤ Real.sqrt 2 / 2 := lemma_1 x y z h_eq
    nlinarith