import Mathlib

theorem algebra_21283 : IsLeast {x : ℝ | ∃ y : ℝ, x ^ 2 + y ^ 2 = 14 * x + 48 * y} (-18) := by
  constructor
  · -- Show -18 is indeed achievable, i.e., there exists y such that (-18, y) satisfies the equation
    use 24
    norm_num
  · -- Show that for any x in the set, x ≥ -18
    intro x
    rintro ⟨y, hy⟩
    have h : (x - 7) ^ 2 + (y - 24) ^ 2 = 625 := by
      nlinarith
    nlinarith [sq_nonneg (y - 24), sq_nonneg (x - 7)]