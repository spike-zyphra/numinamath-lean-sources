import Mathlib

set_option maxHeartbeats 0

theorem algebra_20800 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : (x : ℤ) * y - (x + y) = 39) (hrel : Nat.Coprime x y)
    (hxy1 : x < 20) (hxy2 : y < 20) :
    x + y = 16 := by
  interval_cases x <;> interval_cases y
  <;> norm_num at hxy hrel ⊢
  <;> omega