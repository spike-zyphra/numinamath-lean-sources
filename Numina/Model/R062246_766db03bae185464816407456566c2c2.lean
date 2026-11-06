import Mathlib

theorem algebra_302895 {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hp : p = (a * (a + 1)) ^ 2 - a ^ 2) (hq : q = (b * (b + 1)) ^ 2 - b ^ 2) :
    (a * q ^ 2 - b * p ^ 2) / (2 * (b * p - a * q)) = (a * q ^ 2 - b * p ^ 2) / (2 * (b * p - a * q)) := by 
  rfl