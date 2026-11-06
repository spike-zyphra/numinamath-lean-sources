import Mathlib

theorem algebra_14363 {a b : ℕ} (ha : a + b = 30) (hb : a * 2^5 + b * 3^5= 3281) :
    a * 2 ^ 5 = 608 := by
  have h1 : b = 30 - a := by 
    omega
  rw [h1] at hb
  have h2 : a = 19 := by
    omega
  calc
    a * 2 ^ 5 = 19 * 32 := by
      rw [h2]
      all_goals norm_num
    _ = 608 := by
      norm_num