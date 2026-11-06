import Mathlib

theorem inequalities_195379 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (huv : u < 1) (hvw : v < 1) (hwx : w < 1) :
    ∃ x, x ≤ 1 / 4 ∧ (x = u * (1 - v) ∨ x = v * (1 - w) ∨ x = w * (1 - u)) := by
  by_cases h₁ : u * (1 - v) ≤ 1 / 4
  · -- Assume that u * (1 - v) ≤ 1/4. Thus x can be u * (1 - v).
    use u * (1 - v)
    constructor
    · linarith
    · left
      rfl
  · -- Assume that u * (1 - v) > 1/4.
    by_cases h₂ : v * (1 - w) ≤ 1 / 4
    · -- Assume that v * (1 - w) ≤ 1/4. Thus x can be v * (1 - w).
      use v * (1 - w)
      constructor
      · linarith
      · right
        left
        rfl
    · -- Assume that u * (1 - v) > 1/4 and v * (1 - w) > 1/4. Thus we have to show that w * (1 - u) ≤ 1/4.
      use w * (1 - u)
      constructor
      · -- Show that w * (1 - u) ≤ 1/4.
        nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg (v - 1 / 2), sq_nonneg (w - 1 / 2),
          mul_pos hu hv, mul_pos hv hw, mul_pos hw hu, 
          mul_pos (sub_pos.mpr huv) (sub_pos.mpr hvw), 
          mul_pos (sub_pos.mpr hvw) (sub_pos.mpr hwx), 
          mul_pos (sub_pos.mpr hwx) (sub_pos.mpr huv)]
      · -- Show that x is either u * (1 - v), v * (1 - w), or w * (1 - u).
        right
        right
        rfl