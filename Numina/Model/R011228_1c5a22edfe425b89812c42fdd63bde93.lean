import Mathlib

open Real


theorem inequalities_100122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 3 + b * c) + 1 / (b ^ 3 + c * a) + 1 / (c ^ 3 + a * b) ≤
      ((a * b + b * c + c * a) ^ 2) / 6 := by
  have h1 : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z → x * y * z = 1 → 2 * x ≤ x ^ 3 + y * z := by
    intro x y z hx hy hz habc
    have h2 : x * y * z = 1 := by linarith
    have h3 : 0 < y * z := mul_pos hy hz
    have eq1 : y * z = 1 / x := by
      field_simp [(show 0 < x by linarith)]
      all_goals 
        nlinarith [h2]

    have h5 : x ^ 3 + y * z - 2 * x ≥ 0 := by
      rw [show y * z = 1 / x by linarith [eq1]]
      have hx2 : x > 0 := by linarith
      have h5a : x ^ 3 + (1 / x) - 2 * x ≥ 0 := by
        have hx_eq : x ^ 3 + (1 / x) - 2 * x = (x ^ 4 - 2 * x ^ 2 + 1) / x := by
          field_simp [hx2]
          ring
        rw [hx_eq]
        apply div_nonneg
        · -- Numerator is non-negative 
          nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 - x), sq_nonneg (x), sq_nonneg (x ^ 2 - 1)]
        · -- Denominator is non-negative
          linarith 
      linarith 
    linarith 
  have h2 : 1 / (a ^ 3 + b * c) ≤ 1 / (2 * a) := by
    have h3 : 2 * a ≤ a ^ 3 + b * c := h1 ha hb hc habc
    apply one_div_le_one_div_of_le 
    all_goals linarith 
  have h4 : 2 * b ≤ b ^ 3 + c * a := by 
    refine h1 hb hc ha ?_ 
    convert habc using 1 
    ring 
  have h3 : 1 / (b ^ 3 + c * a) ≤ 1 / (2 * b) := by
    apply one_div_le_one_div_of_le 
    all_goals 
      nlinarith [show 0 < b from hb,show 0 < a from ha, show 0 < c from hc, h4]
  have h6 : 2 * c ≤ c ^ 3 + a * b := by 
    refine h1 hc ha hb ?_ 
    convert habc using 1 
    ring 
  have h4' : 1 / (c ^ 3 + a * b) ≤ 1 / (2 * c) := by 
    apply one_div_le_one_div_of_le 
    all_goals 
      nlinarith [show 0 < c from hc, show 0 < a from ha, show 0 < b from hb, h6]
  have h5 : 1 / (a ^ 3 + b * c) + 1 / (b ^ 3 + c * a) + 1 / (c ^ 3 + a * b) ≤ 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) := by 
    linarith [h2, h3, h4']
  have h6 : 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) = (a * b + b * c + c * a) / (2 * (a * b * c)) := by 
    field_simp 
    ring 
  rw [h6] at h5 
  rw [habc] at h5 
  have h7 : a * b + b * c + c * a ≥ 3 := by 
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b * c - 1), habc]
  have h8 : (a * b + b * c + c * a) / 2 ≤ ((a * b + b * c + c * a) ^ 2) / 6 := by 
    nlinarith [show 0 < a * b + b * c + c * a by positivity, sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  linarith [h5, h8]