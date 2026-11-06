import Mathlib

theorem algebra_6739 : IsLeast {y | ∃ x : ℝ, y = 2018 / (-3 * x ^ 2 + 18 * x - 33)} (-1009 / 3) := by
  constructor
  · -- We need to show that -1009/3 is in the set
    use 3
    norm_num
  · -- We need to show that -1009/3 is the minimum
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : -3 * x ^ 2 + 18 * x - 33 ≤ -6 := by
      nlinarith [sq_nonneg (x - 3)]
    have h2 : -3 * x ^ 2 + 18 * x - 33 < 0 := by
      nlinarith [sq_nonneg (x - 3)]
    have h3 : 2018 / (-3 * x ^ 2 + 18 * x - 33) ≥ -1009 / 3 := by
      apply (le_div_iff_of_neg' (by nlinarith [sq_nonneg (x - 3)] )).mpr
      nlinarith [sq_nonneg (x - 3)]
    linarith