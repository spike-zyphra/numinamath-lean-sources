import Mathlib

theorem inequalities_76925 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
    a + b + c ≥ 3 / (a + b + c) + 2 / (a * b * c) := by

  have h1 : a * b * c * (a + b + c) ≥ a * b + a * c + b * c := by 
    have h2 : 0 < a * b * c := by
      positivity
    have h3 : a + b + c ≥ 1 / a + 1 / b + 1 / c := h
    have h4 : (a + b + c) * (a * b * c) ≥ (1 / a + 1 / b + 1 / c) * (a * b * c) := by
      apply mul_le_mul_of_nonneg_right
      linarith
      positivity
    have h5 : (1 / a + 1 / b + 1 / c) * (a * b * c) = a * b + a * c + b * c := by 
      field_simp
      <;> ring 
    have h6 : (a + b + c) * (a * b * c) = a * b * c * (a + b + c) := by 
      ring 
    nlinarith [h4, h5, h6, h2]

  have h2 : 0 < a * b * c := by 
    positivity 
  have h3 : 0 < a + b + c := by
    positivity

  have h5 : a * b * c * (a + b + c) * (a + b + c) - (3 * (a * b * c) + 2 * (a + b + c)) ≥ 0 := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        h1, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h7 : a + b + c - (3 / (a + b + c) + 2 / (a * b * c)) ≥ 0 := by 
    have h8 : 0 < (a + b + c) * (a * b * c) := by
      positivity
    have h8' : a + b + c - (3 / (a + b + c) + 2 / (a * b * c)) = 
        (a * b * c * (a + b + c) * (a + b + c) - (3 * (a * b * c) + 2 * (a + b + c))) / ((a + b + c) * (a * b * c)) := by 
      field_simp 
      <;> ring 
    rw [h8']
    apply div_nonneg 
    linarith [h5]
    positivity

  have h6 : a + b + c - 3 / (a + b + c) - 2 / (a * b * c) ≥ 0 := by
    have h11 : a + b + c - 3 / (a + b + c) - 2 / (a * b * c) = (a + b + c - (3 / (a + b + c) + 2 / (a * b * c))) := by
      ring 
    linarith [h11, h7]

  linarith [h6]