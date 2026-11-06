import Mathlib

theorem algebra_185007 (x : ℝ) (hx : x ≠ 0) (h1 : (1 - 1 / 2) * (1 - 1 / 3) * (1 - 1 / 4) * (1 - 1 / 5) * (1 - 1 / 6) * (1 - 1 / 7) * x = y) :
    y / x = 1 / 7 := by
  have h2 : y = (1 / 7) * x := by
    have h3 : (1 - 1 / 2 : ℝ) * (1 - 1 / 3) * (1 - 1 / 4) * (1 - 1 / 5) * (1 - 1 / 6) * (1 - 1 / 7) = (1 / 7 : ℝ) := by norm_num
    have h4 : (1 - 1 / 2 : ℝ) * (1 - 1 / 3) * (1 - 1 / 4) * (1 - 1 / 5) * (1 - 1 / 6) * (1 - 1 / 7) * x = (1 / 7 : ℝ) * x := by 
      rw [h3]
      <;> ring
    linarith [h1, h4]
  have eq3 : y / x = 1 / 7 := by 
    have eq2 : y = (1 / 7 : ℝ) * x := h2
    rw [eq2]
    have h3 : x ≠ 0 := hx
    field_simp [h3]
    <;> ring
  exact eq3