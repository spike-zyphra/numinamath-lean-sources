import Mathlib

theorem number_theory_14737 (nthDigitAfterPt : ℕ → ℚ → ℕ) (nthDigitAfterPt_def : ∀ n : ℕ, ∀ x : ℚ,
    nthDigitAfterPt n x = if 0 ≤ x then ⌊10 ^ n * x⌋₊ % 10 else ⌊10 ^ n * (-x)⌋₊) :
    nthDigitAfterPt 100 (3 / 26) = 3 := by
  rw [nthDigitAfterPt_def 100 (3 / 26)]
  norm_num
  <;> native_decide