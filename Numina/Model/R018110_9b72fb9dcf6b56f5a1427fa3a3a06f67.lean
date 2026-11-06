import Mathlib

theorem algebra_322760 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a + b + c = 0) :
    a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) = -3 := by
  have h1 : a + b + c = 0 := h
  have eq1 : a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) =
    (a + c) / b + (b + c) / a + (a + b) / c := by 
    field_simp [hb, ha, hc]
    ring
  rw [eq1]
  have h2 : a + c = -b := by
    linarith 
  have h3 : b + c = -a := by 
    linarith 
  have h4 : a + b = -c := by 
    linarith 
  rw [show a + c = -b by linarith] 
  rw [show b + c = -a by linarith]
  rw [show a + b = -c by linarith]
  have eq3 : (-b : ℝ) / b = -1 := by 
    have hb' : b ≠ 0 := hb
    field_simp [hb']
  have eq4 : (-a : ℝ) / a = -1 := by 
    have ha' : a ≠ 0 := ha
    field_simp [ha']
  have eq5 : (-c : ℝ) / c = -1 := by 
    have hc' : c ≠ 0 := hc
    field_simp [hc']
  rw [eq3]
  rw [eq4]
  rw [eq5]
  norm_num