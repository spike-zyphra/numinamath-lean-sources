import Mathlib

theorem algebra_751 : IsGreatest {z : ℝ | ∃x, ∃y, 0 < x ∧ 0 < y ∧ 2 * x + 3 * y = 8 ∧ z = 2 * x * y + y ^ 2} 8 := by
  constructor
  · -- Show that 8 is achievable, using x = 1 and y = 2
    use 1, 2
    constructor
    · norm_num -- 0 < 1
    constructor
    · norm_num -- 0 < 2
    constructor
    · norm_num -- 2 * 1 + 3 * 2 = 8
    all_goals norm_num -- z = 2 * 1 * 2 + 2 ^ 2
  · -- Show that any value in the set is at most 8
    intro z hz
    rcases hz with ⟨x, y, hx_pos, hy_pos, h_eq, hz_eq⟩
    have h1 : 2 * x + 3 * y = 8 := h_eq
    have h2 : x = (8 - 3 * y) / 2 := by 
      linarith [h1]
    have h3 : 2 * x * y + y ^ 2 = 8 * y - 2 * y ^ 2 := by
      rw [h2]
      nlinarith 
    have h4 : 8 * y - 2 * y ^ 2 ≤ 8 := by 
      nlinarith [sq_nonneg (y - 2)]
    have h5 : 2 * x * y + y ^ 2 ≤ 8 := by 
      linarith [h3, h4]
    linarith [hz_eq, h5] -- z = 2 * x * y + y ^ 2, so z ≤ 8