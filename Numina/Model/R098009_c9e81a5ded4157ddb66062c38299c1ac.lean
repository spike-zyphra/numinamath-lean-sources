import Mathlib

theorem inequalities_145662 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a / b < c / d) :
    a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d := by
  have h1 : a / b < (a + c) / (b + d) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    have h3 : a * d < c * b := by
      have h2 : a / b < c / d := h
      have h4 : a / b - c / d < 0 := sub_neg_of_lt h2
      have h5 : a * d - c * b < 0 := by
        have h5 : (a / b - c / d) = (a * d - c * b) / (b * d) := by
          field_simp
          <;> ring
        rw [h5] at h4
        have h6 : (b * d) > 0 := mul_pos hb hd
        apply div_neg_iff.mp at h4
        cases h4 with
        | inl h7 =>
          have h71 : a * d - c * b < 0 := by linarith
          exact h71
        | inr h8 =>
          linarith
      linarith
    suffices a * d < b * c by
      nlinarith
    linarith

  have h4 : (a + c) / (b + d) < c / d := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    have h3 : a * d < c * b := by
      have h2 : a / b < c / d := h
      have h4 : a / b - c / d < 0 := sub_neg_of_lt h2
      have h5 : a * d - c * b < 0 := by
        have h5 : (a / b - c / d) = (a * d - c * b) / (b * d) := by
          field_simp
          <;> ring
        rw [h5] at h4
        have h6 : (b * d) > 0 := mul_pos hb hd
        apply div_neg_iff.mp at h4
        cases h4 with
        | inl h7 =>
          have h71 : a * d - c * b < 0 := by linarith
          exact h71
        | inr h8 =>
          linarith
      linarith
    suffices a * d < b * c by
      nlinarith
    linarith
  constructor
  · exact h1
  · exact h4