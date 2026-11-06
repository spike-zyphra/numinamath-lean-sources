import Mathlib

open Real

theorem algebra_283661 :
    {θ : ℝ | (fun x => sin (x + θ) + √3 * cos (x - θ)).Even} = {k * π - π / 6 | k : ℤ} := by
  ext θ
  calc (fun x => sin (x + θ) + √3 * cos (x - θ)).Even
    _ ↔ sin (θ + π / 6) = 0 := ?_
    _ ↔ ∃ k : ℤ, k * π - π / 6 = θ := by simp [sin_eq_zero_iff, sub_eq_iff_eq_add]
  simp [Function.Even, sin_add, sin_sub, cos_add, cos_sub]
  conv_lhs =>
    intro x
    rw [← sub_eq_zero]
    ring_nf
  constructor
  . intro h
    specialize h (π / 2)
    simp at h
    linear_combination -h / 4
  . intro h x
    linear_combination -4 * sin x * h
