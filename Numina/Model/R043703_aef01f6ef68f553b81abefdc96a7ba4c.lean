import Mathlib

theorem algebra_173 (x : ℂ) (hx : x^2 + x + 1 = 0) (hx2 : x ≠ 0) : (x^3 + 1/x^3)^3 = 8 := by
  have h1 : x^3 = 1 := by
    have eq1 : x^2 = -x - 1 := by
      have h1 : x^2 + x + 1 = 0 := hx
      calc
        x^2 = x^2 + x + 1 - x - 1 := by ring
        _ = 0 - x - 1 := by rw [h1]
        _ = -x - 1 := by ring
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-x - 1) := by rw [eq1]
      _ = -x^2 - x := by ring
      _ = -(-x - 1) - x := by rw [eq1]
      _ = x + 1 - x := by ring
      _ = 1 := by ring
  have h2 : 1 / x^3 = 1 := by
    rw [h1]
    field_simp [show x ≠ 0 by exact hx2]
  have h3 : x^3 + 1 / x^3 = 2 := by
    rw [h2, h1]
    all_goals norm_num
  rw [h3]
  all_goals norm_num