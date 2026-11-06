import Mathlib

theorem inequalities_599506 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    Real.sqrt 3 ≤ a * b / c + b * c / a + c * a / b := by
  have h1 : 0 < a * b / c := by positivity
  have h2 : 0 < b * c / a := by positivity
  have h3 : 0 < c * a / b := by positivity

  have h4 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 := by
    have h41 : (a * b / c + b * c / a + c * a / b) ^ 2 =
        (a * b / c) ^ 2 + (b * c / a) ^ 2 + (c * a / b) ^ 2 + 2 * ( (a * b / c) * (b * c / a) + (a * b / c) * (c * a / b) + (b * c / a) * (c * a / b) ) := by ring
    rw [h41]
    have h42 : (a * b / c) * (b * c / a) = b^2 := by
      field_simp
      <;> ring
    have h43 : (a * b / c) * (c * a / b) = a^2 := by
      field_simp
      <;> ring
    have h44 : (b * c / a) * (c * a / b) = c^2 := by
      field_simp
      <;> ring
    rw [h42, h43, h44]
    nlinarith [sq_nonneg ( (a * b / c) - (b * c / a) ), sq_nonneg ( (b * c / a) - (c * a / b) ), sq_nonneg ( (c * a / b) - (a * b / c) ), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2) ]
  
  have h5 : (a * b / c + b * c / a + c * a / b) ≥ Real.sqrt 3 := by
    have h6 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
    have h7 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ (3 : ℝ) := h4
    have h8 : Real.sqrt 3 ≥ 0 := by positivity
    have h9 : (a * b / c + b * c / a + c * a / b) ≥ 0 := by positivity
    nlinarith [h6, Real.sqrt_nonneg 3, sq_nonneg ( (a * b / c + b * c / a + c * a / b ) - Real.sqrt 3 ), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
  
  linarith [h5]