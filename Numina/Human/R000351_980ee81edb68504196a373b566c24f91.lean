import Mathlib

open Real Function

/-The maximum value of the function $f(x)=\sin \left(x- \frac{\pi}{3}\right)\cos x$ in the interval $\left[\frac{\pi}{6}, \frac{\pi}{3}\right]$ is \_\_\_\_\_\_.-/
theorem algebra_9079_1 (x : ℝ): x ≤ Real.pi / 3 ∧ Real.pi / 6 ≤ x →
(sin (x - Real.pi/3)) * (cos x) ≤ 0 := by
-- Prove that $cos x$ is nonnegative and $sin (x - Real.pi/3)$ is nonpositive
  rintro ⟨hx1, hx2⟩
  rw [mul_nonpos_iff]; right; constructor
  apply Real.sin_nonpos_of_nonnpos_of_neg_pi_le; linarith; linarith
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le; linarith; linarith

/-check that the maximum is reached by $x=π/3$-/
theorem algebra_9079_2 : (sin (Real.pi/3 - Real.pi/3)) * (cos Real.pi/3) = 0 := by simp