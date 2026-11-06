import Mathlib

open Real

theorem algebra_19368 {h : ℝ → ℝ} (hh : h = fun x => sqrt ((x^3 + 72) / 2) + 1) : h 6 = 13 := by
  rw [hh]
  have h1 : sqrt (( (6 : ℝ) ^ 3 + 72 ) / 2 ) = 12 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  simp [h1]
  <;> norm_num