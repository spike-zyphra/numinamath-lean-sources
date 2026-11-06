import Mathlib

lemma two_le_one_add_ab (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) ≥ 2 / (1 + x * y) := by
  have h1 : 1 + x ^ 2 ≥ 2 := by nlinarith [sq_nonneg (x - 1)]
  have h2 : 1 + y ^ 2 ≥ 2 := by nlinarith [sq_nonneg (y - 1)]
  have h3 : 1 + x * y ≥ 2 := by nlinarith [show x * y ≥ 1 by nlinarith, sq_nonneg (x * y - 1)]
  have h4 : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) - 2 / (1 + x * y) ≥ 0 := by
    have h5 : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) - 2 / (1 + x * y) =
          ( (1 + x * y) * ( (1 + y ^ 2) + (1 + x ^ 2) ) - 2 * (1 + x ^ 2) * (1 + y ^ 2) ) / ( (1 + x ^ 2) * (1 + y ^ 2) * (1 + x * y) ) := by
      have h6 : (1 + x ^ 2) * (1 + y ^ 2) * (1 + x * y) ≠ 0 := by positivity
      field_simp [h6]
      ring
    rw [h5]
    have h7 : (1 + x * y) * ( (1 + y ^ 2) + (1 + x ^ 2) ) - 2 * (1 + x ^ 2) * (1 + y ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
    have h8 : (1 + x ^ 2) * (1 + y ^ 2) * (1 + x * y) > 0 := by positivity
    apply div_nonneg
    linarith
    all_goals linarith
  linarith

theorem inequalities_30936 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) ≥
    1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) := by
        have h1 : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≥ 2 / (1 + a * b) := by
            apply two_le_one_add_ab
            all_goals linarith
        have h2 : 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) ≥ 2 / (1 + b * c) := by
            apply two_le_one_add_ab
            all_goals linarith
        have h3 : 1 / (1 + c ^ 2) + 1 / (1 + a ^ 2) ≥ 2 / (1 + c * a) := by
            apply two_le_one_add_ab
            all_goals linarith
        have h4 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2)) + (1 / (1 + b ^ 2) + 1 / (1 + c ^ 2)) + (1 / (1 + c ^ 2) + 1 / (1 + a ^ 2)) ≥ (2 / (1 + a * b) + 2 / (1 + b * c) + 2 / (1 + c * a)) := by
            linarith [h1, h2, h3]
        have h5 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2)) + (1 / (1 + b ^ 2) + 1 / (1 + c ^ 2)) + (1 / (1 + c ^ 2) + 1 / (1 + a ^ 2)) = 2 * (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2)) := by ring
        have h6 : 2 / (1 + a * b) + 2 / (1 + b * c) + 2 / (1 + c * a) = 2 * (1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a)) := by ring
        have h7 : 2 * (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2)) ≥ 2 * (1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a)) := by
            linarith [h4, h5, h6]
        nlinarith [h7, mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb), mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc), mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]