import Mathlib

theorem algebra_234694 {x y z : ℝ} (h1 : 3 * x * y - 5 * y * z - x * z = 3 * y)
    (h2 : x * y + y * z = -y) (h3 : -5 * x * y + 4 * y * z + x * z = -4 * y) :
    (x = 2 ∧ y = -1 / 3 ∧ z = -3) ∨ (x = x ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = z) := by
  by_cases hy : y = 0
  · -- if y = 0
    have h4 : x * z = 0 := by
      nlinarith [h1, h3]
    cases' (mul_eq_zero.mp h4) with hx hz
    · -- x = 0
      right
      right
      constructor
      · linarith
      constructor
      · linarith
      · -- z = z
        linarith
    · -- z = 0
      right
      left
      constructor
      · -- x = x
        linarith
      constructor
      · linarith
      · -- z = 0
        linarith
  · -- if y ≠ 0
    have h4 : x + z = -1 := by
      apply (mul_left_inj' hy).mp
      linarith
    have h5 : 2 * x + z = 1 := by 
      apply (mul_left_inj' hy).mp
      nlinarith [h1, h3]
    have hx1 : x = 2 := by
      nlinarith
    have hz1 : z = -3 := by 
      linarith [h4, hx1]
    have hy1 : y = -1 / 3 := by
      rw [hx1, hz1] at h1
      linarith
    left
    constructor
    · -- x = 2
      linarith [hx1]
    constructor
    · -- y = -1 / 3
      linarith [hy1]
    · -- z = -3
      linarith [hz1]