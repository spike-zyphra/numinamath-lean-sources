import Mathlib

theorem algebra_95916
  {f : ℝ → ℝ}
  (h : ∀ x > 0, f x + 2 * f (2002 / x) = 3 * x) :
  f 2 = 2000 := by

  have h1: f 2 + 2 * f 1001 = 6 := by
    calc
      f 2 + 2 * f 1001 = f 2 + 2 * f (2002 / 2) := by ring
      _ = 3 * 2 := by rw [h 2 (by positivity)]
      _ = 6 := by ring

  have h2: f 1001 + 2 * f 2 = 3003 := by
    calc
      f 1001 + 2 * f 2 = f 1001 + 2 * f (2002 / 1001) := by ring
      _ = 3 * 1001 := by rw [h 1001 (by positivity)]
      _ = 3003 := by ring

  have h3 : f 1001 = 3003 - 2 * f 2 := by linarith

  calc
    f 2 = f 2 + 2 * f 1001 - 2 * f 1001 := by ring
    _ = 6 - 2 * f 1001 := by rw [h1]
    _ = 6 - 2 * (3003 - 2 * f 2) := by rw [h3]
    _ = 6 - 6006 + 4 * f 2 := by ring

  linarith