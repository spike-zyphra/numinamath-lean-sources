import Mathlib

theorem inequalities_59987 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (h : a + b + c = 2) :
    a / (1 - a) * b / (1 - b) * c / (1 - c) ≥ 8 := by 
  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2
  have h11 : 0 < b := hb.1
  have h12 : b < 1 := hb.2
  have h13 : 0 < c := hc.1
  have h14 : c < 1 := hc.2

  have h3 : 0 < 1 - a := by linarith
  have h4 : 0 < 1 - b := by linarith
  have h5 : 0 < 1 - c := by linarith
  
  have h6 : a / (1 - a) * b / (1 - b) * c / (1 - c) - 8 ≥ 0 := by
    have h3' : 0 < (1 - a) * (1 - b) * (1 - c) := by positivity
    have h7 : a / (1 - a) * b / (1 - b) * c / (1 - c) - 8 = (a * b * c - 8 * (1 - a) * (1 - b) * (1 - c)) / ((1 - a) * (1 - b) * (1 - c)) := by
      field_simp
      <;> ring
    rw [h7]
    have h10 : a * b * c - 8 * (1 - a) * (1 - b) * (1 - c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h11), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h12), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h13), 
        mul_pos (sub_pos.mpr h11) (sub_pos.mpr h12), 
        mul_pos (sub_pos.mpr h11) (sub_pos.mpr h13), 
        mul_pos (sub_pos.mpr h12) (sub_pos.mpr h13), 
        h
      ]
      all_goals nlinarith
    apply div_nonneg 
    linarith 
    all_goals positivity
  
  linarith
  all_goals nlinarith