import Mathlib

theorem algebra_86749 {x y a b : ℝ} (ha : x + y = a) (hb : x * y = b) :
    x ^ 6 + y ^ 6 = a ^ 6 - 6 * a ^ 4 * b + 9 * a ^ 2 * b ^ 2 - 2 * b ^ 3 := by
  have h1 : x ^ 2 + y ^ 2 = a ^ 2 - 2 * b := by 
    have h2 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      ring
    rw [h2, ha, hb]
    all_goals ring

  have h4 : x ^ 6 + y ^ 6 = (x ^ 2 + y ^ 2) ^ 3 - 3 * (x * y) ^ 2 * (x ^ 2 + y ^ 2) := by
    ring
  rw [h4]
  rw [h1, hb]
  all_goals ring