import Mathlib

theorem algebra_325739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 9) (h2 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 10 / 9) :
    a / (b + c) + b / (c + a) + c / (a + b) = 7 := by

  have h3 : 0 < a + b := by linarith
  have h4 : 0 < b + c := by linarith
  have h5 : 0 < c + a := by linarith

  have eq1 : a + b + c = 9 := h1
  have eq2 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 10 / 9 := h2

  have h7 : (a + b + c) * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) = 10 := by
    have h71 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 10 / 9 := h2
    have h72 : a + b + c = 9 := h1
    rw [h71, h72]
    norm_num

  have eq4 : (a + b + c) * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) =
      (a + b + c) / (a + b) + (a + b + c) / (b + c) + (a + b + c) / (c + a) := by 
    ring

  have eq5 : (a + b + c) / (a + b) + (a + b + c) / (b + c) + (a + b + c) / (c + a) = 3 + (a / (b + c) + b / (c + a) + c / (a + b)) := by
    have h9 : (a + b + c) / (a + b) = 1 + c / (a + b) := by 
      field_simp
      <;> nlinarith
    have h10 : (a + b + c) / (b + c) = 1 + a / (b + c) := by 
      field_simp
      <;> nlinarith
    have h11 : (a + b + c) / (c + a) = 1 + b / (c + a) := by 
      field_simp
      <;> nlinarith
    rw [h9, h10, h11]
    ring

  rw [eq4] at h7
  linarith [h7, eq5]