import Mathlib

theorem inequalities_80299 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = a * b * c) :
    (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) +
    (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) +
    (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h3 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ (a + b) / (2 * a * b) := by
    have h4 : 0 < a * b * (a ^ 3 + b ^ 3) := by
      positivity
    have h5 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) - (a + b) / (2 * a * b) ≥ 0 := by
      have pos1 : 0 < a * b * (a ^ 3 + b ^ 3) := by
        positivity
      have pos2 : 0 < 2 * a * b := by
        positivity
      have h6 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) - (a + b) / (2 * a * b) =
          (2 * (a ^ 4 + b ^ 4) - (a + b) * (a ^ 3 + b ^ 3)) / (2 * a * b * (a ^ 3 + b ^ 3)) := by
        field_simp
        ring
      rw [h6]
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b), sq_nonneg (a ^ 2 + b ^ 2), 
        sq_nonneg (a * b - b * a), mul_pos ha hb, mul_pos ha (show 0 < a ^ 2 by positivity), mul_pos hb (show 0 < b ^ 2 by positivity)]
      positivity
    linarith
  have h4 : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ (b + c) / (2 * b * c) := by
    have h5 : 0 < b * c * (b ^ 3 + c ^ 3) := by
      positivity
    have h6 : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) - (b + c) / (2 * b * c) ≥ 0 := by
      have pos1 : 0 < b * c * (b ^ 3 + c ^ 3) := by
        positivity
      have pos2 : 0 < 2 * b * c := by
        positivity
      have h7 : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) - (b + c) / (2 * b * c) =
          (2 * (b ^ 4 + c ^ 4) - (b + c) * (b ^ 3 + c ^ 3)) / (2 * b * c * (b ^ 3 + c ^ 3)) := by
        field_simp
        ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (b - c), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b + c), sq_nonneg (b ^ 2 + c ^ 2), 
          sq_nonneg (b * c - c * b), mul_pos hb hc, mul_pos hb (show 0 < b ^ 2 by positivity), mul_pos hc (show 0 < c ^ 2 by positivity)]
      positivity
    linarith
  have h5 : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ (c + a) / (2 * c * a) := by
    have h6 : 0 < c * a * (c ^ 3 + a ^ 3) := by
      positivity
    have h7 : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) - (c + a) / (2 * c * a) ≥ 0 := by
      have pos1 : 0 < c * a * (c ^ 3 + a ^ 3) := by
        positivity
      have pos2 : 0 < 2 * c * a := by
        positivity
      have h8 : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) - (c + a) / (2 * c * a) =
          (2 * (c ^ 4 + a ^ 4) - (c + a) * (c ^ 3 + a ^ 3)) / (2 * c * a * (c ^ 3 + a ^ 3)) := by
        field_simp
        ring
      rw [h8]
      apply div_nonneg
      nlinarith [sq_nonneg (c - a), sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c + a), sq_nonneg (c ^ 2 + a ^ 2), 
          sq_nonneg (c * a - a * c), mul_pos hc ha, mul_pos hc (show 0 < c ^ 2 by positivity), mul_pos ha (show 0 < a ^ 2 by positivity)]
      positivity
    linarith
  have h6 : (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) = (a * b + b * c + c * a) / (a * b * c) := by
    field_simp
    ring
  have h7 : (a * b + b * c + c * a) / (a * b * c) = 1 := by
    have h8 : a * b + b * c + c * a = a * b * c := h
    rw [h8]
    field_simp
  have h8 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) + (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) + (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) := by
    linarith [h3, h4, h5]
  have h9 : (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) = 1 := by
    linarith [h6, h7]
  linarith [h8, h9]