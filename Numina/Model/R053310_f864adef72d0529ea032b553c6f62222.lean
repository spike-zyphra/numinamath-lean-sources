import Mathlib

theorem algebra_237231 (a b : ℕ) (ha : a = 51) (hb : b = 78) :
    ∃ x, a + x = 2 * (b - x) := by
  use 35
  calc 
    a + 35 = 51 + 35 := by rw [ha]
    _ = 86 := by norm_num
    _ = 2 * (78 - 35) := by norm_num
    _ = 2 * (b - 35) := by rw [hb]