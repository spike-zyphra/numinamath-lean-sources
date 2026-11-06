import Mathlib

theorem algebra_13543 : IsGreatest {y : ℝ | ∃ x, y = -x ^ 2 - 16 * x - 64} 0 := by
  constructor
  · -- Show 0 is in the set
    use -8
    norm_num
  · -- Show no greater element exists
    intro y
    rintro ⟨x, hx⟩
    have h : -x ^ 2 - 16 * x - 64 ≤ 0 := by
      nlinarith [sq_nonneg (x + 8)]
    linarith [hx, h]