import Mathlib

theorem algebra_240556 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 5 * x + 7 * y = 11 * z + 20 * w) (h2 : 8 * x + 4 * y = 20 * z + 8 * w)
    (hz : z > 0) (hw : w > 0) :
    x > 0 ∧ y > 0 ∧ z > 0 ∧ w > 0 ∧
    (5 * x + 7 * y = 11 * z + 20 * w ∧ 8 * x + 4 * y = 20 * z + 8 * w) ↔
    (x > 0 ∧ y > 0 ∧ z > 0 ∧ w > 0 ∧ 5 * x + 7 * y = 11 * z + 20 * w ∧ 8 * x + 4 * y = 20 * z + 8 * w) := by
  constructor
  · -- Assume the left side, prove the right side
    rintro ⟨hx1, hy1, hz1, hw1, ⟨h1', h2'⟩⟩
    tauto
  · -- Assume the right side, prove the left side
    rintro ⟨hx1, hy1, hz1, hw1, h1', h2'⟩
    tauto