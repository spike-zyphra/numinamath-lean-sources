import Mathlib

theorem algebra_20578 :
  IsLeast {t : ℝ | ∃ x y, t = x ^ 2 + y ^ 2 + 2 * x - 4 * y + 8} 3 := by
  constructor
  · -- Let's show that (3) belongs to the set, by choosing appropriate x and y
    use -1
    use 2
    norm_num
  · -- Now, let's show that any element in the set is greater than 3
    intro t
    rintro ⟨x, y, rfl⟩
    have h1 : (x + 1) ^ 2 + (y - 2) ^ 2 ≥ 0 := by
      apply add_nonneg
      · apply sq_nonneg
      · apply sq_nonneg
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2)]