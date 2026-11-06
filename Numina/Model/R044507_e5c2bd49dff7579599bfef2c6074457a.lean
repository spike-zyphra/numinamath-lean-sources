import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_115057 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hxy : x * y ≤ 1) (hxy' : x * z ≤ 1) (hxy'' : y * z ≤ 1) :
  IsGreatest {m | 0 < m ∧ ∀ x y : ℝ, 0 < x → 0 < y → x * y ≤ 1 →
    ((1 + x ^ 2) * (1 + y ^ 2)) / (2 + x ^ 2 + y ^ 2) ≥ m * (1 + x * y)} (1 / 2) ∧
  ((1 + x ^ 2) * (1 + y ^ 2)) / (2 + x ^ 2 + y ^ 2) +
  ((1 + x ^ 2) * (1 + z ^ 2)) / (2 + x ^ 2 + z ^ 2) +
  ((1 + y ^ 2) * (1 + z ^ 2)) / (2 + y ^ 2 + z ^ 2) ≥
  (3 + x * y + x * z + y * z) / 2 := by
  constructor
  · -- Show that 1/2 is the greatest element in the set
    constructor
    · -- Show that 1/2 is in the set
      constructor
      · -- Show that 0 < (1/2 : ℝ)
        norm_num
      · -- Show that the inequality holds for 1/2
        intro x y hx hy hxy
        have h1 : ((1 + x^2) * (1 + y^2)) / (2 + x^2 + y^2) ≥ (1 / 2) * (1 + x * y) := by
          have h2 : 2 + x^2 + y^2 > 0 := by
            nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
          have h3 : 2 * ((1 + x ^ 2) * (1 + y ^ 2)) ≥ (1 + x * y) * (2 + x ^ 2 + y ^ 2) := by
            have h4 : x * y ≤ 1 := hxy
            nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - y), mul_pos hx hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), mul_pos hx hy, mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ x * y by nlinarith)]
          have h5 : ((1 + x^2) * (1 + y^2)) / (2 + x^2 + y^2) ≥ (1 / 2) * (1 + x * y) := by
            apply (le_div_iff₀ (by positivity)).mpr
            linarith
          exact h5
        exact h1
    · -- Show that 1/2 is greatest
      intro m hm
      rcases hm with ⟨hm_pos, hm_ineq⟩
      have h2 := hm_ineq 1 1 (by norm_num) (by norm_num) (by norm_num)
      norm_num at h2
      linarith
  · -- Show the inequality in part b)
    have h1 : ((1 + x ^ 2) * (1 + y ^ 2)) / (2 + x ^ 2 + y ^ 2) ≥ (1 + x * y) / 2 := by
      have h2 : 0 < (2 + x^2 + y^2 : ℝ) := by
        nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
      apply (le_div_iff₀ h2).mpr 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), mul_pos hx hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ x * y by nlinarith)]
    have h2 : ((1 + x ^ 2) * (1 + z ^ 2)) / (2 + x ^ 2 + z ^ 2) ≥ (1 + x * z) / 2 := by
      have h3 : 0 < (2 + x^2 + z ^ 2 : ℝ) := by
        nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hz]
      apply (le_div_iff₀ h3).mpr 
      nlinarith [sq_nonneg (x - z), sq_nonneg (x * z - 1), mul_pos hx hz, sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (x * z), mul_nonneg (show 0 ≤ x * z by nlinarith) (show 0 ≤ x * z by nlinarith)]
    have h3 : ((1 + y ^ 2) * (1 + z ^ 2)) / (2 + y ^ 2 + z ^ 2) ≥ (1 + y * z) / 2 := by
      have h4 : 0 < (2 + y^2 + z^2 : ℝ) := by
        nlinarith [sq_pos_of_pos hy, sq_pos_of_pos hz]
      apply (le_div_iff₀ h4).mpr 
      nlinarith [sq_nonneg (y - z), sq_nonneg (y * z - 1), mul_pos hy hz, sq_nonneg (y^2 - z^2), sq_nonneg (y * z), mul_nonneg (show 0 ≤ y * z by nlinarith) (show 0 ≤ y * z by nlinarith)]
    linarith [h1, h2, h3]