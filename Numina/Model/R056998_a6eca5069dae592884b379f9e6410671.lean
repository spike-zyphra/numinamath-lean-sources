import Mathlib

theorem calculus_35916 :
    IsGreatest {x | ∃ a b : ℝ, x = 8 * a ^ 2 + 9 * a * b + 18 * b ^ 2 + 2 * a + 3 * b ∧ 4 * a ^ 2 + 9 * b ^ 2 = 8} 26 := by
  constructor
  · -- Show 26 is achievable with a=1, b=2/3
    use 1, 2 / 3
    norm_num
    <;> nlinarith
  · -- Show x <= 26 for all x in the set
    rintro x ⟨a, b, hx, h⟩
    have h1 : 8 * a ^ 2 + 9 * a * b + 18 * b ^ 2 + 2 * a + 3 * b ≤ 26 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2 / 3), sq_nonneg (4 * (a - 1) + 9 * (b - 2 / 3)), sq_nonneg (a + 1 / 3), sq_nonneg (b + 2 / 3), sq_nonneg (a * b - 2 / 3), sq_nonneg ((a - 1) / 2), sq_nonneg ((b - 2 / 3) / 2), sq_nonneg (a - 1), sq_nonneg (b - 2/3), sq_nonneg (4 * a * b)]
    linarith [hx, h1]