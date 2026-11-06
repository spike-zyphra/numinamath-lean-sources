import Mathlib

theorem inequalities_38308 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b ≥ a * b) (h2 : b + c ≥ b * c) (h3 : c + a ≥ c * a) :
    a + b + c ≥ 3 / 4 * a * b * c := by
  have h1' : 1 / a + 1 / b ≥ 1 := by
    have h1_pos1 : 0 < a * b := mul_pos ha hb
    have h1_pos2 : 0 < a := by linarith
    have h1_pos3 : 0 < b := by linarith
    have h1': a + b ≥ a * b := h1
    have h1' : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp
      <;> ring
    rw [h1'] 
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have h2' : 1 / b + 1 / c ≥ 1 := by
    have h2_pos1 : 0 < b * c := mul_pos hb hc
    have h2_pos2 : 0 < b := by linarith
    have h2_pos3 : 0 < c := by linarith
    have h2': b + c ≥ b * c := h2
    have h2' : 1 / b + 1 / c = (b + c) / (b * c) := by
      field_simp
      <;> ring
    rw [h2']
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have h3' : 1 / c + 1 / a ≥ 1 := by
    have h3_pos1 : 0 < c * a := mul_pos hc ha
    have h3_pos2 : 0 < c := by linarith
    have h3_pos3 : 0 < a := by linarith
    have h3': c + a ≥ c * a := h3
    have h3' : 1 / c + 1 / a = (c + a) / (c * a) := by
      field_simp
      <;> ring
    rw [h3']
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  nlinarith [show 0 < a from ha, show 0 < b from hb, show 0 < c from hc, h1, h2, h3, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c from hc)]