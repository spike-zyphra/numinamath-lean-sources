import Mathlib

theorem algebra_7184 {a : ℚ} (ha : a ≠ 0) (h : a + 3 / a = 5) :
    ((a + 2) ^ 2 - 1) / (a ^ 3 * (5 * a - 22)) = -1 := by
  have h1 : a ^ 2 + 3 = 5 * a := by
    field_simp [ha] at h
    linarith
  have h2 : a ^ 3 = 22 * a - 15 := by
    have ha2 : a ^ 2 = 5 * a - 3 := by linarith [h1]
    calc
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (5 * a - 3) := by rw [ha2]
      _ = 5 * a ^ 2 - 3 * a := by ring
      _ = 5 * (5 * a - 3) - 3 * a := by rw [ha2]
      _ = 25 * a - 15 - 3 * a := by ring
      _ = 22 * a - 15 := by ring
  have num_eq : (a + 2) ^ 2 - 1 = 9 * a := by
    have ha2 : a ^ 2 = 5 * a - 3 := by linarith [h1]
    calc
      (a + 2) ^ 2 - 1 = a ^ 2 + 4 * a + 4 - 1 := by ring
      _ = a ^ 2 + 4 * a + 3 := by ring
      _ = (5 * a - 3) + 4 * a + 3 := by rw [ha2]
      _ = 9 * a := by ring
  have denom_eq : a ^ 3 * (5 * a - 22) = -9 * a := by
    have ha2 : a ^ 2 = 5 * a - 3 := by linarith [h1]
    have h2' : a ^ 3 = 22 * a - 15 := by
      calc
        a ^ 3 = a * a ^ 2 := by ring
        _ = a * (5 * a - 3) := by rw [ha2]
        _ = 5 * a ^ 2 - 3 * a := by ring
        _ = 5 * (5 * a - 3) - 3 * a := by rw [ha2]
        _ = 25 * a - 15 - 3 * a := by ring
        _ = 22 * a - 15 := by ring
    calc 
      a ^ 3 * (5 * a - 22) = (22 * a - 15) * (5 * a - 22) := by rw [h2']
      _ = 110 * a ^ 2 - 559 * a + 330 := by ring
      _ = 110 * (5 * a - 3) - 559 * a + 330 := by 
        rw [show a ^ 2 = 5 * a - 3 by linarith [h1]]
      _ = -9 * a := by ring
  rw [num_eq, denom_eq]
  field_simp [ha]
  <;> linarith