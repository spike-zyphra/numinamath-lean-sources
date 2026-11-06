import Mathlib

theorem algebra_11473 : IsLeast { l * w | (l : ℤ) (w : ℤ) (_ : l > 0) (_ : w > 0) (h : 2 * (l + w) = 100) } 49 := by
  constructor
  · -- Show 49 is in the set
    use 1, 49
    all_goals norm_num
  · -- Show no smaller element is in the set
    intro k hk
    rcases hk with ⟨l, w, hl, hw, h, hk⟩
    have h1 : l + w = 50 := by
      linarith
    have h2 : w = 50 - l := by
      omega
    rw [show w = 50 - l by omega] at hk
    have h3 : l ≥ 1 := by
      omega
    have h4 : l ≤ 49 := by
      nlinarith
    nlinarith [sq_nonneg (l - 1 : ℤ), sq_nonneg (l - 49 : ℤ), sq_nonneg (l * (50 - l) - 49 : ℤ)]