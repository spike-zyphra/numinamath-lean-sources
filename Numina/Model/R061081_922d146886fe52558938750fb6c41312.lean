import Mathlib

theorem algebra_270015 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (1 / 18) + x * 81 = y * 49) (h2 : x * 49 + y * 81 = (2 / 9) * (1 / 18)) :
    (1 - (2 / 9) * (1 / 18)) / (x + y) = 231 := by
  have h3 : y > 0 := hy
  have h4 : x > 0 := hx
  have eq1 : (1 - (2 / 9) * (1 / 18) : ℝ) = (80 / 81 : ℝ) := by
    norm_num
  have final_eq : (1 - (2 / 9) * (1 / 18)) / (x + y) = 231 := by 
    have h5 : (x + y) ≠ 0 := by linarith
    field_simp at h1 h2 ⊢
    nlinarith
  exact final_eq