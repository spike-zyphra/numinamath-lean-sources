import Mathlib

theorem inequalities_173928 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    a^2 / b + b^2 / c + c^2 / d + d^2 / a > a + b + c + d := by 
  have h1 : a^2 / b + b - 2 * a > 0 := by 
    have hne : a ≠ b := hdist.1
    have h2 : a^2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp
      ring
    rw [h2]
    have hb : 0 < b := hb
    have h3 : 0 < (a - b) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      intro h0
      apply hne
      linarith
    apply div_pos
    exact h3
    linarith
  have h2 : b^2 / c + c - 2 * b > 0 := by 
    have hne : b ≠ c := by
      tauto
    have h3 : b^2 / c + c - 2 * b = (b - c) ^ 2 / c := by 
      field_simp
      ring
    rw [h3]
    have hc : 0 < c := hc
    have h4 : 0 < (b - c) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      intro h0
      apply hne
      linarith
    apply div_pos
    exact h4
    linarith
  have h3 : c^2 / d + d - 2 * c > 0 := by 
    have hne : c ≠ d := by
      tauto
    have h4 : c^2 / d + d - 2 * c = (c - d) ^ 2 / d := by 
      field_simp
      ring
    rw [h4]
    have hd : 0 < d := hd
    have h5 : 0 < (c - d) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      intro h0
      apply hne
      linarith
    apply div_pos
    exact h5
    linarith
  have h4 : d^2 / a + a - 2 * d > 0 := by 
    have hne : d ≠ a := by 
      tauto
    have h5 : d^2 / a + a - 2 * d = (d - a) ^ 2 / a := by 
      field_simp
      ring
    rw [h5]
    have ha : 0 < a := ha
    have h6 : 0 < (d - a) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      intro h0
      apply hne
      linarith
    apply div_pos
    exact h6
    linarith
  linarith [h1, h2, h3, h4]