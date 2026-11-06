import Mathlib

open Real

theorem inequalities_25832 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * a ^ 2 + b ^ 2 = 9 * c ^ 2) :
    sqrt 3 ≤ 2 * c / a + c / b := by
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : (2 * c / a + c / b) ^ 2 ≥ 3 := by
    have h4 : (2 * c / a + c / b) ^ 2 =
      4 * c ^ 2 / a ^ 2 + 4 * c ^ 2 / (a * b) + c ^ 2 / b ^ 2 := by
      field_simp
      <;> ring
    have h5 : 4 * c ^ 2 / a ^ 2 + 4 * c ^ 2 / (a * b) + c ^ 2 / b ^ 2 =
      (4 * c ^ 2 * b ^ 2 + 4 * c ^ 2 * a * b + c ^ 2 * a ^ 2) / (a ^ 2 * b ^ 2) := by
      field_simp
      <;> ring
    have h6 : (4 * c ^ 2 * b ^ 2 + 4 * c ^ 2 * a * b + c ^ 2 * a ^ 2) / (a ^ 2 * b ^ 2) ≥ 3 := by
      have h7 : 4 * c ^ 2 * b ^ 2 + 4 * c ^ 2 * a * b + c ^ 2 * a ^ 2 ≥ 3 * (a ^ 2 * b ^ 2) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (2 * a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - c * 3), sq_nonneg (2 * a * c - b * c), sq_nonneg (a ^ 2 + b ^ 2 - 3 * c ^ 2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < b ^ 2 by nlinarith)]
      have h8 : (a ^ 2 * b ^ 2) > 0 := by
        positivity
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    linarith [h4, h5, h6]
  have h3 : (sqrt 3) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h5 : (2 * c / a + c / b) ≥ Real.sqrt 3 := by
    have h7 : (2 * c / a + c / b) ^ 2 ≥ (Real.sqrt 3) ^ 2 := by
      nlinarith [h2, h3]
    have h8 : 0 ≤ (Real.sqrt 3) := by
      positivity
    have h9 : 0 ≤ (2 * c / a + c / b) := by
      have ha' : 0 < a := ha
      have hc' : 0 < c := hc
      have hb' : 0 < b := hb
      positivity
    nlinarith [h7, h8, h9, Real.sqrt_nonneg 3]
  linarith [h5]