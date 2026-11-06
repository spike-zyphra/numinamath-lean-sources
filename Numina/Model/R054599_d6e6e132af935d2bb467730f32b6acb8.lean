import Mathlib

theorem algebra_598672 (x y : ℝ) :
    x^2 + (y - 1)^2 + (x - y)^2 = 1 / 3 ↔ x = 1 / 3 ∧ y = 2 / 3 := by 
  constructor
  · -- Forward direction: If the equation holds, then (x, y) = (1/3, 2/3)
    intro h
    have h1 : x^2 + (y - 1)^2 + (x - y)^2 - 1 / 3 = 0 := by linarith 
    have h2 : (x - 1 / 3)^2 + (y - 2 / 3)^2 = 0 := by 
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3),
        sq_nonneg (x - y / 2), sq_nonneg (y - 2 / 3)]
    have hx1 : (x - 1 / 3) ^ 2 = 0 := by 
      linarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3)]
    have hy1 : (y - 2 / 3) ^ 2 = 0 := by 
      linarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3)]
    have hx2 : x = 1 / 3 := by 
      nlinarith
    have hy2 : y = 2 / 3 := by 
      nlinarith
    exact ⟨hx2, hy2⟩
  · -- Backward direction: If (x, y) = (1/3, 2/3), then the equation holds
    rintro ⟨rfl, rfl⟩
    norm_num