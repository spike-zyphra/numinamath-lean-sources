import Mathlib

theorem algebra_5380 : ∃ t : ℝ, t ∈ Set.Ioo 6 7 ∧ (6 * t + 11 * (t - 6)) % 11 = 0 := by
  use 72 / 11
  constructor
  · -- Show that 72/11 ∈ (6, 7)
    exact ⟨by norm_num, by norm_num⟩
  · -- Calculate the expression and verify modulo 11 equals 0
    norm_num [Int.floor_eq_iff]
    <;> try { norm_num }
    <;> try { linarith }
    <;> try { norm_num }