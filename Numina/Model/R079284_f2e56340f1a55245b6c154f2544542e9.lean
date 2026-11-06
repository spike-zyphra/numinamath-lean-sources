import Mathlib

theorem algebra_2218 {x : ℝ} (hx : x ^ 2 + 2 * x = 3) :
    x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 - 13 * x + 15 = 18 := by
  have eq1 : x ^ 2 = 3 - 2 * x := by linarith
  have eq2 : x ^ 3 = 7 * x - 6 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (3 - 2 * x) := by rw [eq1]
      _ = 3 * x - 2 * x ^ 2 := by ring
      _ = 3 * x - 2 * (3 - 2 * x) := by rw [eq1]
      _ = 7 * x - 6 := by ring
  have eq3 : x ^ 4 = 21 - 20 * x := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (3 - 2 * x) ^ 2 := by rw [eq1]
      _ = 9 - 12 * x + 4 * x ^ 2 := by ring
      _ = 9 - 12 * x + 4 * (3 - 2 * x) := by rw [eq1]
      _ = 21 - 20 * x := by ring
  have eq4 : x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 - 13 * x + 15 = (21 - 20 * x) + 7 * (7 * x - 6) + 8 * (3 - 2 * x) - 13 * x + 15 := by
    rw [show x ^ 4 = 21 - 20 * x by linarith [eq3]]
    rw [show x ^ 3 = 7 * x - 6 by linarith [eq2]]
    rw [show x ^ 2 = 3 - 2 * x by linarith [eq1]]
    <;> ring
  rw [eq4]
  linarith