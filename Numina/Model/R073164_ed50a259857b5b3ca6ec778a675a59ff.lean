import Mathlib

theorem inequalities_132909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    3 * (a * b + b * c + c * a) - 2 ≤ (a^5 + b^5) / (a * b * (a + b)) +
    (b^5 + c^5) / (b * c * (b + c)) + (c^5 + a^5) / (c * a * (c + a)) := by
  have pos1 : 0 < a * b * (a + b) := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    nlinarith
  have pos2 : 0 < b * c * (b + c) := by
    apply mul_pos
    apply mul_pos
    exact hb
    exact hc
    nlinarith
  have pos3 : 0 < c * a * (c + a) := by
    apply mul_pos
    apply mul_pos
    exact hc
    exact ha
    nlinarith
  have h1 : (a^5 + b^5) / (a * b * (a + b)) = (a^4 + b^4) / (a * b) - (a^2 + b^2) + a * b := by 
    field_simp [pos1]
    ring
  have h2 : (b^5 + c^5) / (b * c * (b + c)) = (b^4 + c^4) / (b * c) - (b^2 + c^2) + b * c := by 
    field_simp [pos2]
    ring
  have h3 : (c^5 + a^5) / (c * a * (c + a)) = (c^4 + a^4) / (c * a) - (c^2 + a^2) + c * a := by 
    field_simp [pos3]
    ring
  rw [h1, h2, h3]
  suffices (a^4 + b^4) / (a * b) + (b^4 + c^4) / (b * c) + (c^4 + a^4) / (c * a) ≥ 2 * (a * b + b * c + c * a) by 
    nlinarith
  have h4 : (a^4 + b^4) / (a * b) ≥ 2 * (a * b) := by 
    apply (le_div_iff₀ (mul_pos ha hb)).mpr 
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b)]
  have h5 : (b^4 + c^4) / (b * c) ≥ 2 * (b * c) := by 
    apply (le_div_iff₀ (mul_pos hb hc)).mpr 
    nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (b - c)]
  have h6 : (c^4 + a^4) / (c * a) ≥ 2 * (c * a) := by 
    apply (le_div_iff₀ (mul_pos hc ha)).mpr 
    nlinarith [sq_nonneg (c^2 - a^2), sq_nonneg (c - a)]
  linarith [h4, h5, h6]