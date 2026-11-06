import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_180508 :
  IsGreatest {V | ∃ x : ℝ, (0 < x) ∧ (x < 10) ∧ (V = x * (20 - 2 * x)^2)} ((40 / 3) ^ 3 / 4) := by
  constructor
  · -- Show that ((40 / 3) ^ 3 / 4) is in the set
    use 10 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that ((40 / 3) ^ 3 / 4) is greatest in the set
    intro V
    rintro ⟨x, ⟨hx1, hx2, hV⟩⟩
    have h1 : x * (20 - 2 * x) ^ 2 ≤ (40 / 3) ^ 3 / 4 := by
      nlinarith [sq_nonneg (x - 10 / 3), sq_nonneg (x - 10), sq_nonneg (x - 0), sq_nonneg ((20 - 2 * x) - 40 / 3), sq_nonneg (x * (x - 10 / 3)), sq_nonneg ((20 - 2 * x) * (x - 10 / 3)), sq_nonneg ((x - 10 / 3) * (x - 10)), mul_pos hx1 (sub_pos.mpr hx2)]
    linarith [h1, hV]