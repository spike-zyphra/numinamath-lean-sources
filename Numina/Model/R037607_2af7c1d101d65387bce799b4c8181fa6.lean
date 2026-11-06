import Mathlib

theorem inequalities_150002 (a b c d : ℝ) (h₀ : a > b) (h₁ : b > c) (h₂ : c > d) :
    c < (c * d - a * b) / (c - a + d - b) ∧ (c * d - a * b) / (c - a + d - b) < b := by

  have h3 : c - a + d - b < 0 := by 
    nlinarith
  have h4 : c < (c * d - a * b) / (c - a + d - b) := by
    apply (lt_div_iff_of_neg' (by linarith)).mpr
    have h5 : c * (c - a + d - b) > c * d - a * b := by 
      nlinarith [h₀, h₁, h₂, mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), 
                  mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)]
    linarith
  have h4' : (c * d - a * b) / (c - a + d - b) < b := by
    apply (div_lt_iff_of_neg' (by linarith)).mpr
    have h7 : c * d - a * b > b * (c - a + d - b) := by
      nlinarith [h₀, h₁, h₂, mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), 
                  mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)]
    linarith
  constructor
  · exact h4
  · exact h4'