import Mathlib

theorem algebra_14012 (k l b : ℂ) (hk : k = 780 + 1040 * .I) (hl : l = 0)
    (hb : b = 2600 * .I) :
    Complex.abs (k - l) = 1300 := by
  rw [hk, hl]
  simp [Complex.abs, Complex.normSq]
  ring_nf
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num