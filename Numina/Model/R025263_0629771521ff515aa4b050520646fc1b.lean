import Mathlib

theorem inequalities_196799 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / (a^2 + b^2) + (b + c) / (b^2 + c^2) + (c + a) / (c^2 + a^2) ≤
    1 / a + 1 / b + 1 / c := by
  have h8 : (a + b) / (a ^ 2 + b ^ 2) ≤ (1 /a + 1 / b) / 2 := by
    have h9 : 0 < a ^ 2 + b ^ 2 := by nlinarith
    have h10 : 0 < a * b := by nlinarith
    have h11 : (a + b) / (a ^ 2 + b ^ 2) ≤ (1 /a + 1 / b) / 2 := by
      have h13 : (a + b) / (a ^ 2 + b ^ 2) - ( (1 / a + 1 /b) / 2 ) ≤ 0 := by
        have h14 : (a + b) / (a ^ 2 + b ^ 2) - ( (1 / a + 1 /b) / 2 ) = - ( (a - b) ^2 * (a + b) ) / ( 2 * a * b * (a ^ 2 + b ^ 2) ) := by
          field_simp
          ring
        rw [ h14 ]
        have h15 : - ( (a - b) ^2 * (a + b) ) / ( 2 * a * b * (a ^ 2 + b ^ 2) ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show numerator is ≤ 0
            have h16 : ( a - b ) ^ 2 ≥ 0 := by nlinarith
            have h17 : (a + b) > 0 := by nlinarith
            have h18 : ( a - b ) ^2 * ( a + b ) ≥ 0 := mul_nonneg h16 (show 0 ≤ a + b by linarith)
            linarith
          · -- Show denominator is ≥ 0
            positivity
        linarith
      linarith
    linarith
  have h8b : (b + c) / (b ^ 2 + c ^ 2) ≤ (1 /b + 1 / c) / 2 := by
    have h9 : 0 < b ^ 2 + c ^ 2 := by nlinarith
    have h10 : 0 < b * c := by nlinarith
    have h11 : (b + c) / (b ^ 2 + c ^ 2) ≤ (1 /b + 1 / c) / 2 := by
      have h13 : (b + c) / (b ^ 2 + c ^ 2) - ( (1 / b + 1 /c) / 2 ) ≤ 0 := by
        have h14 : (b + c) / (b ^ 2 + c ^ 2) - ( (1 / b + 1 /c) / 2 ) = - ( (b - c) ^2 * (b + c) ) / ( 2 * b * c * (b ^ 2 + c ^ 2) ) := by
          field_simp
          ring
        rw [ h14 ]
        have h15 : - ( (b - c) ^2 * (b + c) ) / ( 2 * b * c * (b ^ 2 + c ^ 2) ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show numerator is ≤ 0
            have h16 : ( b - c ) ^ 2 ≥ 0 := by nlinarith
            have h17 : (b + c) > 0 := by nlinarith
            have h18 : ( b - c ) ^2 * ( b + c ) ≥ 0 := mul_nonneg h16 (show 0 ≤ b + c by linarith)
            linarith
          · -- Show denominator is ≥ 0
            positivity
        linarith
      linarith
    linarith
  have h8c : (c + a) / (c ^ 2 + a ^ 2) ≤ (1 /c + 1 / a) / 2 := by
    have h9 : 0 < c ^ 2 + a ^ 2 := by nlinarith
    have h10 : 0 < c * a := by nlinarith
    have h11 : (c + a) / (c ^ 2 + a ^ 2) ≤ (1 /c + 1 / a) / 2 := by
      have h13 : (c + a) / (c ^ 2 + a ^ 2) - ( (1 / c + 1 /a) / 2 ) ≤ 0 := by
        have h14 : (c + a) / (c ^ 2 + a ^ 2) - ( (1 / c + 1 /a) / 2 ) = - ( (c - a) ^2 * (c + a) ) / ( 2 * c * a * (c ^ 2 + a ^ 2) ) := by
          field_simp
          ring
        rw [ h14 ]
        have h15 : - ( (c - a) ^2 * (c + a) ) / ( 2 * c * a * (c ^ 2 + a ^ 2) ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show numerator is ≤ 0
            have h16 : ( c - a ) ^ 2 ≥ 0 := by nlinarith
            have h17 : (c + a) > 0 := by nlinarith
            have h18 : ( c - a ) ^2 * ( c + a ) ≥ 0 := mul_nonneg h16 (show 0 ≤ c + a by linarith)
            linarith
          · -- Show denominator is ≥ 0
            positivity
        linarith
      linarith
    linarith
  have h9 : (a + b) / (a^2 + b^2) + (b + c) / (b^2 + c^2) + (c + a) / (c^2 + a^2) ≤ (1 / a + 1 / b) / 2 + (1 / b + 1 / c) / 2 + (1 / c + 1 / a) / 2 := by
    linarith [ h8, h8b, h8c ]
  have h91 : (1 / a + 1 / b) / 2 + (1 / b + 1 / c) / 2 + (1 / c + 1 / a) / 2 = 1 / a + 1 / b + 1 / c := by
    ring
  linarith [h9, h91]