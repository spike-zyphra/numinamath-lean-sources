import Mathlib

open Real Set

theorem algebra_9034 (f : ℝ → ℝ) (hf : f = λ x => 2 * sin x + sin (2 * x)) :
    IsLeast (range f) (-3 * √3 / 2) := by
  simp [hf, sin_two_mul, range, IsLeast, lowerBounds]
  constructor
  . use -(π / 3)
    simp [hf]
    ring
  . intro x
    suffices H : (sin x * (1 + cos x)) ^ 2 ≤ (3 * √3 / 4) ^ 2 by
      linarith [abs_le_of_sq_le_sq' H (by positivity)]
    conv_rhs =>
      ring_nf
      norm_num
    rw [show (sin x * (1 + cos x))  ^ 2 = sin x ^ 2 * (1 + cos x) ^ 2 by ring, sin_sq]
    nlinarith [sq_nonneg (2 * cos x - 1), sq_nonneg (2 * cos x + 3)]
