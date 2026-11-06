import Mathlib

theorem algebra_9387 :
    IsLeast {a | 0 < a ∧ (∀ x y : ℝ, x > 0 → y > 0 → 9 * x + y = x * y → a * x + y ≥ 25)} 4 := by
  constructor
  · -- Show that 4 is in the set.
    constructor
    · norm_num
    · intro x y hx hy h
      nlinarith [sq_nonneg (x - 2.5), sq_nonneg (y - 15), sq_nonneg (x * 3 - y / 2), sq_nonneg (y - 3 * x * 2), mul_pos hx hy, mul_pos (show 0 < x by linarith) (show 0 < y by linarith)]
  · -- Show that 4 is the least element in the set.
    intro a h
    rcases h with ⟨ha_pos, h⟩
    have h4 := h 2.5 15 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h4 
    nlinarith