import Mathlib

theorem inequalities_224814 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    Real.sqrt 3 ≤ a * b / c + b * c / a + c * a / b := by 
  -- positivity of terms
  have h1 : 0 < a * b / c := by positivity
  have h2 : 0 < b * c / a := by positivity
  have h3 : 0 < c * a / b := by positivity
  -- needed for application of squaring to preserve inequality
  have h5 : (a * b / c + b * c / a + c * a / b) ≥ 0 := by positivity
  -- needed to ensure zero on the square root side.
  have h7 : Real.sqrt 3 ≥ 0 := by positivity
  -- Now the main proof strategy is to apply the relation x \ge a : x^2 \ge a^2 if x and a are non-negative.
  -- First prove that the squaring holds.
  have h4 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 := by
    have h5 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 * (a^2 + b^2 + c^2) := by
      have h6 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 * ( (a * b / c) * (b * c / a) + (b * c / a) * (c * a / b) + (c * a / b) * (a * b / c) ) := by
        nlinarith [sq_nonneg (a * b / c - (b * c / a)), sq_nonneg (a * b / c - (c * a / b)), sq_nonneg (b * c / a - (c * a / b)), 
                  sq_nonneg ((a * b / c) + (b * c / a) + (c * a / b)), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                 ]
      have h7 : (a * b / c) * (b * c / a) = b^2 := by 
        field_simp
        <;> ring
      have h8 : (b * c / a) * (c * a / b) = c^2 := by 
        field_simp
        <;> ring
      have h9 : (c * a / b) * (a * b / c) = a^2 := by 
        field_simp
        <;> ring
      rw [h7, h8, h9] at h6
      linarith
    have h6' : a^2 + b^2 + c^2 = 1 := h
    have h7 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 * (a^2 + b^2 + c^2) := h5
    rw [h6'] at h7
    linarith
  -- Now establish the sqrt from squaring. 
  have h8 : (Real.sqrt 3) ^ 2 ≤ (a * b / c + b * c / a + c * a / b) ^ 2 := by
    have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    nlinarith [h4, h9]
  -- Now with positivity, take squared root. 
  -- Since $S = a*b/c + ...$ and sqrt 3 are both non-negative, we have from S^2 >= sqrt 3 ^ 2 that S >= sqrt 3.
  have h10 : Real.sqrt 3 ≥ 0 := by positivity
  have h11 : a * b / c + b * c / a + c * a / b ≥ 0 := by positivity
  nlinarith [Real.sqrt_nonneg 3, sq_nonneg (a * b / c + b * c / a + c * a / b - Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]