import Mathlib

theorem inequalities_601419 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / 4 ≤ (a ^ 2 + 2 * b * c) / (b + c) ^ 2 + (b ^ 2 + 2 * a * c) / (c + a) ^ 2 +
    (c ^ 2 + 2 * a * b) / (a + b) ^ 2 ∧
    2 ≤ (a ^ 2 + b * c) / (b ^ 2 + b * c + c ^ 2) + (b ^ 2 + a * c) / (c ^ 2 + c * a + a ^ 2) +
    (c ^ 2 + a * b) / (a ^ 2 + a * b + b ^ 2) := by
  constructor
  · -- Prove the first inequality
    have hb' : 0 < b := hb
    have hc' : 0 < c := hc
    have ha' : 0 < a := ha
    have h1 : 0 < (b + c) ^ 2 := by positivity
    have h2 : 0 < (c + a) ^ 2 := by positivity
    have h3 : 0 < (a + b) ^ 2 := by positivity
    have h4 : (a ^ 2 + 2 * b * c) / (b + c) ^ 2 + (b ^ 2 + 2 * a * c) / (c + a) ^ 2 + (c ^ 2 + 2 * a * b) / (a + b) ^ 2 - 9 / 4 ≥ 0 := by
      have h5 : (a ^ 2 + 2 * b * c) / (b + c) ^ 2 + (b ^ 2 + 2 * a * c) / (c + a) ^ 2 + (c ^ 2 + 2 * a * b) / (a + b) ^ 2 - 9 / 4 =
          ( (a ^ 2 + 2 * b * c) * (c + a) ^ 2 * (a + b) ^ 2 + (b ^ 2 + 2 * a * c) * (b + c) ^ 2 * (a + b) ^ 2 + (c ^ 2 + 2 * a * b) * (b + c) ^ 2 * (c + a) ^ 2 - (9 / 4) * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 ) / ( (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 ) := by
        field_simp
        ring
      rw [h5] at *
      have h6 : (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 > 0 := by positivity
      suffices (a ^ 2 + 2 * b * c) * (c + a) ^ 2 * (a + b) ^ 2 + (b ^ 2 + 2 * a * c) * (b + c) ^ 2 * (a + b) ^ 2 + (c ^ 2 + 2 * a * b) * (b + c) ^ 2 * (c + a) ^ 2 - (9 / 4) * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 ≥ 0 by
        have : ( (a ^ 2 + 2 * b * c) * (c + a) ^ 2 * (a + b) ^ 2 + (b ^ 2 + 2 * a * c) * (b + c) ^ 2 * (a + b) ^ 2 + (c ^ 2 + 2 * a * b) * (b + c) ^ 2 * (c + a) ^ 2 - (9 / 4) * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 ) / ( (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2 ) ≥ 0 := by 
          apply div_nonneg
          linarith
          positivity
        linarith
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
    linarith
  · -- Prove the second inequality
    have hb' : 0 < b := hb
    have hc' : 0 < c := hc
    have ha' : 0 < a := ha
    have h1 : 0 < b ^ 2 + b * c + c ^ 2 := by positivity
    have h2 : 0 < c ^ 2 + c * a + a ^ 2 := by positivity
    have h3 : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
    have h4 : (a ^ 2 + b * c) / (b ^ 2 + b * c + c ^ 2) + (b ^ 2 + a * c) / (c ^ 2 + c * a + a ^ 2) + (c ^ 2 + a * b) / (a ^ 2 + a * b + b ^ 2) - 2 ≥ 0 := by
      have h5 : (a ^ 2 + b * c) / (b ^ 2 + b * c + c ^ 2) + (b ^ 2 + a * c) / (c ^ 2 + c * a + a ^ 2) + (c ^ 2 + a * b) / (a ^ 2 + a * b + b ^ 2) - 2 =
          ( (a ^ 2 + b * c) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) + (b ^ 2 + a * c) * (b ^ 2 + b * c + c ^ 2) * (a ^ 2 + a * b + b ^ 2) + (c ^ 2 + a * b) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) - 2 * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) ) / ( (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) ) := by 
        field_simp
        ring
      rw [h5] at *
      have h6 : (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) > 0 := by positivity
      suffices (a ^ 2 + b * c) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) + (b ^ 2 + a * c) * (b ^ 2 + b * c + c ^ 2) * (a ^ 2 + a * b + b ^ 2) + (c ^ 2 + a * b) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) - 2 * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) ≥ 0 by
        have : ( (a ^ 2 + b * c) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) + (b ^ 2 + a * c) * (b ^ 2 + b * c + c ^ 2) * (a ^ 2 + a * b + b ^ 2) + (c ^ 2 + a * b) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) - 2 * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) ) / ( (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a ^ 2 + a * b + b ^ 2) ) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
    linarith