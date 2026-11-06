import Mathlib

theorem algebra_10255
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a + b + c = 9)
    (h2 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 10 / 9) :
    a / (b + c) + b / (c + a) + c / (a + b) = 7 := by

  have h3 : a + b + c = 9 := h1
  have h4 : a + b ≠ 0 := by nlinarith
  have h5 : b + c ≠ 0 := by nlinarith
  have h6 : c + a ≠ 0 := by nlinarith

  have eq1 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) * (a + b + c) = 10 := by
    have h7 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) * (a + b + c) = (10 / 9) * (a + b + c) := by
      rw [h2]
    have h8 : (10 / 9) * (a + b + c) = 10 := by 
      rw [show a + b + c = 9 by linarith [h1]]
      all_goals norm_num
    linarith [h7, h8]

  -- Express left-hand side of eq1 in desired form.
  have eq2 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) * (a + b + c) = (a / (b + c) + b / (c + a) + c / (a + b) ) + 3 := by
    have eq3 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) * (a + b + c) = ( (a + b + c) / (a + b) ) + ( (a + b + c) / (b + c) ) + ( (a + b + c) / (c + a) ) := by 
      field_simp [h4, h5, h6]
      <;> ring
    rw [eq3]
    have eq4 : (a + b + c) / (a + b) = (c / (a + b)) + 1 := by 
      field_simp [show a + b ≠ 0 by nlinarith]
      <;> nlinarith
    have eq5 : (a + b + c) / (b + c) = (a / (b + c)) + 1 := by 
      field_simp [show b + c ≠ 0 by nlinarith]
      <;> nlinarith
    have eq6 : (a + b + c) / (c + a) = (b / (c + a)) + 1 := by 
      field_simp [show c + a ≠ 0 by nlinarith]
      <;> nlinarith
    rw [eq4, eq5, eq6]
    ring

  linarith [eq1, eq2]