import Mathlib
open Real Set

theorem algebra_8969 :
    IsLeast {x | ∃ t : ℝ, x = t^4 + 3*t^3 + 5*t^2 + 5*t + 2019} 2017 := by
  constructor
  · -- First, we show 2017 is in the set.
    use -1
    norm_num
  · -- Then, we prove 2017 is the least element of the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : t^4 + 3 * t^3 + 5 * t^2 + 5 * t + 2019 - 2017 ≥ 0 := by
      nlinarith [sq_nonneg (t + 1), sq_nonneg (t^2 + t + 1), sq_nonneg (t + 1/2), sq_nonneg (t - (-2)/2), sq_nonneg (t^2 - (-1)/2), sq_nonneg (t^3 + 1/2), sq_nonneg (t^2 + t), sq_nonneg (t * (t + 1)), sq_nonneg ((t + 1)^2), sq_nonneg ((t + 3)/2), sq_nonneg ((t - 1)/2), sq_nonneg ((t + 1)/2)]
    linarith [ht, h1]