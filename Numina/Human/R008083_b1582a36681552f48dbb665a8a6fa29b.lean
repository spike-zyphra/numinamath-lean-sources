import Mathlib

theorem algebra_199707 {a b : ℝ} {x y : ℝ} (ha : a = 5 / 10) (hb : b = 3 / 10)
    (hxy : x / a + y / b = 90)
    (h' : x + y = 35) :
    x = 20 ∧ y = 15 := by 
  rw [ha, hb] at *
  field_simp at *
  constructor <;> linarith
