import Mathlib

open Real Set

theorem algebra_2568 : IsLeast {t | ∃ a b c d : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ 4 ∧ a + b + c + d = 4 ∧ d ≤ 2 * a ∧ t = a * b * c * d} (64 / 81) := by
  constructor
  · -- Show that 64/81 is indeed achievable
    use 2 / 3, 2 / 3, 4 / 3, 4 / 3
    norm_num
  · -- Show that 64/81 is the least element in the set
    intro t ht
    rcases ht with ⟨a, b, c, d, h0, hab, hbc, hcd, hd4, hsum, hd2a, ht⟩
    nlinarith [sq_nonneg (a - 2 / 3), sq_nonneg (b - 2 / 3), sq_nonneg (c - 4 / 3), sq_nonneg (d - 4 / 3),
              mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc),
              mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hcd),
              mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd),
              mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h0),
              mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr h0),
              mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr h0),
              mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr hab)]