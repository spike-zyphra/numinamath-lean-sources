import Mathlib

theorem algebra_240844 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a > b) (h' : a^2 + b^2 = 6 * a * b) :
    (a + b) / (a - b) = Real.sqrt 2 := by

  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have h3 : a - b ≠ 0 := by linarith

  have h4 : (a + b) / (a - b) > 0 := by 
    apply div_pos
    · linarith
    · linarith

  have h5 : ((a + b) / (a - b)) ^ 2 = 2 := by
    have h6 : (a - b) ≠ 0 := by linarith
    field_simp at *
    nlinarith

  have h6 : (a + b) / (a - b) = Real.sqrt 2 := by
    have hsq : ((a + b) / (a - b)) ^ 2 = 2 := h5
    have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h8 : ((a + b) / (a - b)) ^ 2 = (Real.sqrt 2) ^ 2 := by 
      linarith
    have h9 : 0 < (a + b) / (a - b) := h4
    have h10 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h11 : (a + b) / (a - b) = Real.sqrt 2 := by
      nlinarith [sq_nonneg ((a + b) / (a - b) - Real.sqrt 2), Real.sqrt_nonneg 2]
    exact h11

  exact h6