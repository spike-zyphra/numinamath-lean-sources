import Mathlib

theorem algebra_4729 (a b c : ℝ) (ha : a^2 - b * c - 1 = 0) (hb : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    ∃! x : ℤ, a = x := by
  have h1 : a^2 - b * c = 1 := by linarith
  have h2 : (a - 3)^2 + b^2 + c^2 = 4 := by
    nlinarith
  have h3 : a ≥ 1 := by
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b + c), sq_nonneg (a - 1), sq_nonneg (c - b)]
  have h4 : a ≤ 5 := by
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b + c), sq_nonneg (a - 5), sq_nonneg (c - b)]
  have h5 : a = (1 : ℝ) := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 0), sq_nonneg (c - 0), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (a - 3)]
  use 1
  constructor
  · -- Show that 1 is indeed an integer value of a
    have h5' : a = (1 : ℝ) := by
      linarith
    norm_num at h5' ⊢
    all_goals linarith
  · -- Show that it is unique
    intro x h
    have h8 : a = (x : ℝ) := by
      norm_num at h ⊢
      linarith
    have h9 : (x : ℝ) = 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 0), sq_nonneg (c - 0), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (a - 3), sq_nonneg (x : ℝ)]
    have h10 : x = 1 := by
      exact_mod_cast h9
    linarith