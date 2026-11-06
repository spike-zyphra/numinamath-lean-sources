import Mathlib

theorem inequalities_49171 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (a ^ 3 + a ^ 2) / (1 + b * c) + (b ^ 3 + b ^ 2) / (1 + c * a) +
        (c ^ 3 + c ^ 2) / (1 + a * b) := by
  
  have h1 : 1 + b * c = (a + 1) / a := by
    field_simp
    nlinarith [habc]

  have h2 : 1 + c * a = (b + 1) / b := by
    field_simp
    nlinarith [habc]

  have h3 : 1 + a * b = (c + 1) / c := by
    field_simp
    nlinarith [habc]

  have h4 : (a ^ 3 + a ^ 2) / (1 + b * c) = a ^ 3 := by 
    rw [h1]
    field_simp
    <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

  have h5 : (b ^ 3 + b ^ 2) / (1 + c * a) = b ^ 3 := by 
    rw [h2]
    field_simp
    <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

  have h6 : (c ^ 3 + c ^ 2) / (1 + a * b) = c ^ 3 := by 
    rw [h3]
    field_simp
    <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have h12 : (a ^ 3 + a ^ 2) / (1 + b * c) + (b ^ 3 + b ^ 2) / (1 + c * a) + (c ^ 3 + c ^ 2) / (1 + a * b) = a ^ 3 + b ^ 3 + c ^ 3 := by
    rw [h4, h5, h6]
  
  have h7 : a ^ 3 + b ^ 3 + c ^ 3 ≥ 3 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 3), sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith [h12, h7]