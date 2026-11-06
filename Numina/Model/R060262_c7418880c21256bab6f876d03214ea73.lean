import Mathlib

open Real Set

theorem algebra_20865 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / b + 5 * b / a ≥ 2 * sqrt 5 := by 
  have h1 : a / b + 5 * b / a = (a ^ 2 + 5 * b ^ 2) / (a * b) := by
    field_simp [hb.ne.symm, ha.ne.symm]
    <;> ring
  have h2 : 0 < a * b := mul_pos ha hb
  have h4 : (a ^ 2 + 5 * b ^ 2) / (a * b) ≥ 2 * sqrt 5 := by
    have h5 : a ^ 2 + 5 * b ^ 2 ≥ 2 * sqrt 5 * (a * b) := by
      nlinarith [sq_nonneg (a - Real.sqrt 5 * b), 
                  Real.sqrt_nonneg 5, 
                  Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
                  mul_pos ha hb]
    have h6 : 0 < a * b := mul_pos ha hb
    apply (le_div_iff₀ (by linarith)).mpr
    linarith [h5]
  linarith [h1, h4]