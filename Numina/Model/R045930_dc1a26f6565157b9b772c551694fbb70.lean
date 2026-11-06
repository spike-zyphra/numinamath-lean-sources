import Mathlib

theorem algebra_195547 {x y : ℕ} (hx : x ≠ y) (h : x * y = 15 * (x + y)) :
    max x y - min x y = 224 ∨ max x y - min x y = 72 ∨ max x y - min x y = 40 ∨
    max x y - min x y = 16 := by
  have h4 : x ≤ 240 := by
    by_contra h4
    push_neg at h4
    have h5 : y ≤ 15 := by
      nlinarith [h4, h]
    interval_cases y <;> omega
  have h5 : y ≤ 240 := by
    by_contra h5
    push_neg at h5
    have h6 : x ≤ 15 := by
      nlinarith [h5, h]
    interval_cases x <;> omega
  interval_cases x <;> omega