import Mathlib

theorem algebra_301235 (x y : ℤ) :
    x > 0 ∧ y > 0 ∧ 3 * x ^ 2 - 8 * x * y + 7 * y ^ 2 - 4 * x + 2 * y = 109 ↔
    (x, y) = (2, 5) ∨ (x, y) = (14, 9) := by
  constructor
  · -- Forward: if (x,y) is positive integer solution, then it is either (2,5),(14,9)
    rintro ⟨hx, hy, heq⟩
    have h1 : x ≤ 30 := by
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 5 : ℤ), sq_nonneg (x - 14 : ℤ), sq_nonneg (y - 9 : ℤ), sq_nonneg (3 * x - 4 * y), sq_nonneg (x - y)]
    have h2 : y ≤ 30 := by
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 5 : ℤ), sq_nonneg (x - 14 : ℤ), sq_nonneg (y - 9 : ℤ), sq_nonneg (3 * x - 4 * y), sq_nonneg (x - y)]
    interval_cases x <;> interval_cases y
    <;> norm_num at heq
    <;> norm_num [Prod.ext_iff] at *
    <;> all_goals omega
  · -- Backward implication. If (x,y) is (2,5),(14,9) then it is solution.
    rintro (h | h)
    · -- Case (2,5)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (14,9)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num