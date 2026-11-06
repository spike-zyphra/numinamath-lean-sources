import Mathlib

open Real

theorem algebra_14630 : IsGreatest {k : ℝ | ∃ x y : ℝ, (x > 0 ∧ y > 0) ∧ k = (x + y) ^ 2 / (x ^ 2 + y ^ 2)} 2 := by
  constructor
  · -- Show that 2 is in the set
    use 1, 1
    constructor
    · constructor
      · norm_num
      · norm_num
    · norm_num
  · -- Show that 2 is an upper bound
    intro k hk
    rcases hk with ⟨x, y, ⟨hx, hy⟩, rfl⟩
    have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (x - y)]
    have h2 : x ^ 2 + y ^ 2 > 0 := by
      nlinarith [hx, hy, sq_pos_of_pos hx, sq_pos_of_pos hy]
    
    have h3 : (x + y) ^ 2 / (x ^ 2 + y ^ 2) ≤ (2 * (x ^ 2 + y ^ 2)) / (x ^ 2 + y ^ 2) := by
      apply (div_le_div_right h2).mpr
      linarith [h1]

    have h4 : (2 * (x ^ 2 + y ^ 2)) / (x ^ 2 + y ^ 2) = (2 : ℝ) := by
      have h5 : x ^ 2 + y ^ 2 ≠ 0 := by nlinarith [hx, hy, sq_pos_of_pos hx, sq_pos_of_pos hy]
      field_simp [h5]
      <;> nlinarith

    linarith [h3, h4]