import Mathlib

open Real Set

theorem algebra_11987 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2 + b^2 + 1 / (a + b)^2 ≥ sqrt 2 ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a^2 + b^2 + 1 / (a + b)^2 = sqrt 2 := by
  have h1 : a^2 + b^2 + 1 / (a + b)^2 ≥ Real.sqrt 2 := by 
    have h2 : a^2 + b^2 ≥ ( (a + b) ^ 2 ) / 2 := by 
      linarith [sq_nonneg (a - b)]
    have h3 : a^2 + b^2 + 1 / (a + b)^2 ≥ ( (a + b) ^ 2 ) / 2 + 1 / (a + b) ^ 2 := by 
      linarith [h2]
    have h4 : ( (a + b) ^ 2 ) / 2 + 1 / (a + b) ^ 2 ≥ Real.sqrt 2 := by
      have h5 : 0 < (a + b) ^ 2 := by 
        nlinarith [show 0 < a by linarith, show 0 < b by linarith]
      have h6 : ( (a + b) ^ 2 ) / 2 + 1 / (a + b) ^ 2 - Real.sqrt 2 ≥ 0 := by
        have h7 : ( (a + b) ^ 2 ) / 2 + 1 / (a + b) ^ 2 - Real.sqrt 2 = 
            ( ( (a + b) ^ 4 - 2 * Real.sqrt 2 * (a + b) ^ 2 + 2 ) ) / ( 2 * (a + b) ^ 2 ) := by 
          field_simp
          <;> 
          nlinarith [ Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num) , Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num) ]
        rw [ h7 ]
        have h8 : ( (a + b) ^ 4 - 2 * Real.sqrt 2 * (a + b) ^ 2 + 2 ) ≥ 0 := by 
          nlinarith [ sq_nonneg ( (a + b) ^ 2 - Real.sqrt 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num) ]
        apply div_nonneg 
        linarith 
        nlinarith [ show 0 < (a + b) ^ 2 by nlinarith ]
      linarith 
    linarith [h3, h4]
  have h2 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a^2 + b^2 + 1 / (a + b)^2 = Real.sqrt 2 := by
    use Real.sqrt (Real.sqrt 2) / 2, Real.sqrt (Real.sqrt 2) / 2
    constructor 
    · -- Show $a > 0$
      nlinarith [ Real.sqrt_nonneg (Real.sqrt 2), Real.sqrt_pos.mpr (show 0 < Real.sqrt 2 by positivity) ]
    constructor 
    · -- Show $b > 0$
      nlinarith [ Real.sqrt_nonneg (Real.sqrt 2), Real.sqrt_pos.mpr (show 0 < Real.sqrt 2 by positivity) ]
    · -- Show that the expression equals sqrt 2
      have h8 : (Real.sqrt (Real.sqrt 2) / 2 + Real.sqrt (Real.sqrt 2) / 2) ^ 2 = Real.sqrt 2 := by 
        have h9 : Real.sqrt (Real.sqrt 2) ^ 2 = Real.sqrt 2 := by
          rw [Real.sq_sqrt]
          positivity 
        nlinarith
      have h10 : (Real.sqrt (Real.sqrt 2) / 2) ^ 2 + (Real.sqrt (Real.sqrt 2) / 2) ^ 2 = Real.sqrt 2 / 2 := by 
        have h9 : Real.sqrt (Real.sqrt 2) ^ 2 = Real.sqrt 2 := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith 
      have h9 : 1 / ( (Real.sqrt (Real.sqrt 2) / 2 + Real.sqrt (Real.sqrt 2) / 2 ) ^ 2 ) = Real.sqrt 2 / 2 := by 
        rw [h8]
        field_simp
        <;> 
        nlinarith [ Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num) ]
      nlinarith [ h10, h9, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num) ]
  constructor 
  · linarith [ h1 ]
  · exact h2