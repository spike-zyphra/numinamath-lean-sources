import Mathlib

theorem algebra_14244 : IsGreatest {s : ℝ | ∃ l w : ℝ, 0 < l ∧ 0 < w ∧ l + 2 * w = 360 ∧ s = l * w} 16200 := by
  constructor
  · use 180, 90
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · intro s hs
    rcases hs with ⟨l, w, hl, hw, h1, hs⟩
    nlinarith [sq_nonneg (l - 180), sq_nonneg (w - 90), sq_nonneg (w), sq_nonneg (l), mul_nonneg (show 0 ≤ l by linarith) (show 0 ≤ w by linarith)]