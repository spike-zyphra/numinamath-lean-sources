import Mathlib

theorem algebra_202838 (x : ℝ) (hx : x ≠ 0) (h : 1 / 4 + 4 * (1 / 2013 + 1 / x) = 7 / 4) :
    1872 + 48 * (2013 * x / (x + 2013)) = 2000 := by
  have eq1 : x + 2013 ≠ 0 := by
    intro h1
    have hx1 : x = -2013 := by linarith
    rw [hx1] at h
    norm_num at h <;> linarith

  -- Solving the given equation
  have h1 : 4 * (1 / 2013 + 1 / x) = 3 / 2 := by
    linarith
  
  have h2 : 1 / 2013 + 1 / x = 3 / 8 := by
    linarith
  
  have h3 : x = 8 * 2013 / 6031 := by
    field_simp [hx] at h2
    linarith

  rw [h3]
  norm_num
  <;> linarith