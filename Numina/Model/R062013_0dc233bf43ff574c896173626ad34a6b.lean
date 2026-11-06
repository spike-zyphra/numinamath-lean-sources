import Mathlib

theorem algebra_1173 {x : ℝ} (hx : x = 1.6) :
    (1 - y) * x = 1 ↔ y = 0.375 := by
  rw [hx]
  constructor
  · -- Assume (1 - y) * 1.6 = 1, prove y = 0.375
    intro h
    have eq1 : (1 - y) * (1.6 : ℝ) = 1 := by 
      linarith
    have eq2 : (1 - y : ℝ) = 1 / 1.6 := by
      field_simp at eq1 ⊢
      linarith
    have eq3 : (y : ℝ) = 1 - (1 / 1.6 ) := by
      linarith [eq2]
    rw [eq3]
    norm_num
  · -- Assume y = 0.375, prove (1 - y) * 1.6 = 1
    intro h
    rw [h]
    norm_num