import Mathlib

open Complex

theorem algebra_270790 (z : ℂ) : ((z + 5) ^ 2).re / ((z + 5) ^ 2).im = -3 / 4 ↔
    (z.re + 2 * z.im + 5) * (z.re - z.im / 2 + 5) = 0 ∧ (z.re + 5) * z.im ≠ 0 := by
  ring_nf; simp; rw [pow_two, mul_re, mul_im]
  by_cases h : z.re * z.im + z.im * 5 = 0
  · have : z.im * 10 + (z.re * z.im + z.im * z.re) = 0 := by linarith only [h]
    simp [this]; norm_num; intro; exact h
  rw [← div_eq_mul_inv, div_eq_div_iff, ← sub_eq_zero]; ring_nf
  constructor
  · intro h'; constructor; linarith only [h']
    exact h
  rintro ⟨h'⟩; linarith only [h']
  revert h; contrapose!; intro; linarith
  norm_num