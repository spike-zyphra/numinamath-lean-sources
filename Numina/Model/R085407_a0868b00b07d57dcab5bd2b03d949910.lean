import Mathlib

theorem algebra_145989 {x y : ℝ} (h : x / (x + y) = 101) : (y - x) / y = 2.01 := by

  have h1 : x + y ≠ 0 := by 
    by_contra h2
    have h3 : x / (x + y) = 0 := by 
      rw [h2]
      norm_num
    linarith

  have eq1 : x = 101 * (x + y) := by 
    field_simp [h1] at h 
    linarith

  have eq2 : 101 * y = -100 * x := by 
    linarith [eq1]

  have h4 : y ≠ 0 := by 
    by_contra h5
    rw [h5] at eq2
    have hx : x = 0 := by 
      linarith
    have h6 : x + y = 0 := by 
      rw [hx, h5]
      norm_num
    contradiction

  have eq3 : y - x = (201 / 100) * y := by
    have eq7 : x = (-101 / 100) * y := by 
      linarith [eq2]
    calc
      y - x = y - ((-101 / 100) * y) := by rw [eq7]
      _ = y - (- (101 / 100) * y) := by ring
      _ = y + (101 / 100) * y := by ring
      _ = (1 + (101 / 100)) * y := by ring
      _ = (201 / 100) * y := by norm_num

  calc
    (y - x) / y = ((201 / 100) * y) / y := by rw [eq3]
    _ = (201 / 100) * (y / y) := by ring
    _ = (201 / 100) * 1 := by 
      rw [div_self]
      exact h4
    _ = (201 / 100) := by ring
    _ = 2.01 := by norm_num