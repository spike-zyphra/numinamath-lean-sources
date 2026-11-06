import Mathlib

theorem algebra_10417 :
    IsLeast {t : ℝ | t > 0 ∧ -4.9 * t ^ 2 + 23.8 * t = 28} 2 := by
  constructor
  · -- Show that 2 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that without t in the set, 2 <= t
    intro t ht
    rcases ht with ⟨ht_pos, ht_eq⟩
    norm_num at ht_eq ⊢
    nlinarith [sq_nonneg (t - 2), sq_nonneg (t - 20 / 7)]