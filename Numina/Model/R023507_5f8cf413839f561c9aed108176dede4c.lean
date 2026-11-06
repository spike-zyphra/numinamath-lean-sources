import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_102847 :
  IsLeast {f | ∃ x y : ℝ, f = (x - y)^2 + (x + 1 / y + 1)^2} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set
    use (-1 / 2 : ℝ)
    use (-1 : ℝ)
    norm_num
  · -- Show that 1/2 is the minimum value
    intro f hf
    rcases hf with ⟨x, y, rfl⟩
    have h1 : (x - y) ^ 2 + (x + 1 / y + 1) ^ 2 ≥ 1 / 2 := by
      by_cases hy : y = 0
      · -- When y = 0, 1/y = 0 in Lean's real numbers
        rw [hy]
        norm_num
        <;> nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x + 1), sq_nonneg ((x : ℝ)), sq_nonneg ((x + 1 / 2) : ℝ)]
      · -- When y ≠ 0, we can proceed with the standard analysis
        have h1 : 1 / y = 1 / y := rfl
        have h2 : (x + 1 / y + 1) ^ 2 =
          ((x * y + 1 + y) / y) ^ 2 := by
            field_simp [hy]
            all_goals linarith
        rw [h2]
        have h4 : (x - y) ^ 2 + ((x * y + 1 + y) / y) ^ 2 - 1 / 2 ≥ 0 := by
          have h12 : (x - y) ^ 2 + ((x * y + 1 + y) / y) ^ 2 - 1 / 2 =
            ((x - y)^2 * y^2 + (x * y + 1 + y)^2 - (1/2) * y^2) / (y^2) := by
            field_simp
            <;> ring_nf <;> field_simp
            all_goals nlinarith
          rw [h12]
          have h13 : (y ^ 2) > 0 := by
            exact sq_pos_of_ne_zero (show y ≠ 0 by exact hy)
          have h99 : (x - y) ^ 2 * y ^ 2 + (x * y + 1 + y) ^ 2 - (1 / 2) * y ^ 2 ≥ 0 := by
            nlinarith [sq_nonneg ((x * y + y + 1) + y * (x - y)), sq_nonneg ((x * y + y + 1) - y * (x - y)), sq_nonneg ((x * y + 1 + y) * y * 2), sq_nonneg ((x * y + 1 + y) ^ 2 * 4), sq_nonneg ((x * y + 1 + y) + y), sq_nonneg ((x * y + 1 + y) ^ 2), sq_nonneg ((x * y + 1 + y) * (x - y)), sq_nonneg ((x * y + 1 + y) * y * 2), sq_nonneg ((x * y + 1 + y) + (x * y)), sq_nonneg (x * y + 1 + y - (x * y)), sq_nonneg (x - y - (x * y)), sq_nonneg (x * y), sq_nonneg (x * y + y * 1), sq_nonneg (y * 2 + 2), sq_nonneg (x * y * 0), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - (-1/2)), sq_nonneg (y - (-1)), sq_nonneg ((x + 1 / 2) * (y + 1)), sq_nonneg ((x * (y + 1) )), sq_nonneg (((y * (y * 2 + 1)) : ℝ)), sq_nonneg (((y * (y * 2 + 1) ) * (x + 1 / 2) ) : ℝ)]
          apply div_nonneg
          linarith
          all_goals positivity
        linarith
        all_goals nlinarith
    linarith [h1]
    all_goals nlinarith