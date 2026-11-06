import Mathlib

theorem algebra_154321 {a : ℝ} (ha : a ^ 4 = 2) :
    ∃! t : ℝ, ∃! y : ℝ, |t| - y = -1 - 2 * t ^ 4 ∧ t ^ 2 + y ^ 2 = 1 ∧ y = 1 + |t| + 2 * t ^ 4 ∧ y ^ 2 = 1 - t ^ 2 := by 
  use 0
  constructor
  · -- Show that t = 0 is the unique value.
    use 1
    constructor
    · -- Show that y = 1 is the unique solution when t = 0
      constructor
      · norm_num [abs_zero]
      constructor
      · norm_num [abs_zero]
      constructor
      · norm_num [abs_zero]
      · norm_num [abs_zero]
    · -- Show that y = 1 is the unique solution when t = 0 
      intro y hy
      rcases hy with ⟨h1, h2, h3, h4⟩
      norm_num [abs_zero] at h1 h2 h3 h4
      have h5 : y = 1 := by linarith
      exact h5
  · -- Show that t = 0 is unique.
    intro t ht
    rcases ht with ⟨y, ⟨h1, h2, h3, h4⟩, hy⟩
    -- From equation 3: $y = 1 + |t| + 2t^4$, we have y >= 1
    have h5 : y ≥ 1 := by
      have h6 : |t| ≥ 0 := abs_nonneg t
      have h7 : 2 * t^4 ≥ 0 := by 
        nlinarith [sq_nonneg t, sq_nonneg (t^2)]
      nlinarith [h3, h6, h7]
    -- From |t| - y = -1 - 2*t^4 and t^2 + y^2 = 1 to show y^2 <=1.
    have h6 : y^2 ≤ 1 := by
      nlinarith [sq_nonneg t, h4]
    -- Then y =1.
    have h7 : y = 1 := by
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg t, sq_nonneg (t^2)]
    -- Then t^2 = 0.
    have ht2 : t^2 = 0 := by
      nlinarith [h7, h4]
    -- Then t = 0.
    have ht0 : t = 0 := by
      nlinarith
    exact ht0