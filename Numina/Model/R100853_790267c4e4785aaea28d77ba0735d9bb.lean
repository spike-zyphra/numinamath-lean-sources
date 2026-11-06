import Mathlib

theorem algebra_4716 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a * 75 = b * 150) : a * 45 = b * 90 := by
  have h2 : a = 2 * b := by
    omega
  calc 
    a * 45 = (2 * b) * 45 := by rw [h2]
    _ = 90 * b := by ring
    _ = b * 90 := by ring