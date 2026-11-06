import Mathlib

/- One of the roots of
\[ax^3 + 3x^2 + bx - 65 = 0,\]is $-2 - 3i,$ where $a$ and $b$ are real numbers.  Find the real root of this cubic polynomial. -/
theorem algebra_13144 {a b : ℝ} (ha : a ≠ 0) (h : a * (-2 - 3 * Complex.I)^3 + 3 * (-2 - 3 * Complex.I)^2 + b * (-2 - 3 * Complex.I) - 65 = 0) :
    ∃ x : ℝ, a * x^3 + 3 * x^2 + b * x - 65 = 0 ∧ x = 5 / 2 := by
  use 5 / 2
  simp [Complex.ext_iff, pow_two, pow_three] at h
  norm_num at h
  exact ⟨by linarith, rfl⟩