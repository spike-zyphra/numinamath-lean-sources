import Mathlib

theorem inequalities_28212 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by 
  have h₁ : 0 < a * b := mul_pos ha hb
  have h₂ : 0 < b * c := mul_pos hb hc
  have h₃ : 0 < c * a := mul_pos hc ha
  have h₄ : 0 < a * b + b * c + c * a := by linarith
  have h₅ : 0 < a + b + c := by linarith
  have h6 : 1 * (a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a) ≥ 0 := by
    nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
  have h7 : (1 + 3 / (a * b + b * c + c * a) ) - (6 / (a + b + c)) ≥ 0 := by
    have h8 : (1 + 3 / (a * b + b * c + c * a) ) - (6 / (a + b + c)) =
        ( (1 * (a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a) ) / ( (a * b + b * c + c * a) * (a + b + c) ) ) := by 
      field_simp
      ring
    rw [h8]
    have h8_pos : (a * b + b * c + c * a) * (a + b + c) > 0 := by positivity
    have h9_pos : 1 * (a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a) ≥ 0 := by linarith [h6]
    apply div_nonneg
    · linarith
    · positivity 
  linarith 
  <;> try { tauto } <;> try { nlinarith } 
  <;> try { tauto } <;> try { nlinarith } 
  <;> try { nlinarith } 
  <;> try { tauto } <;> try { nlinarith } 
  <;> try { tauto } <;> try { nlinarith }