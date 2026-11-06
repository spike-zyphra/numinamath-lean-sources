import Mathlib

open Real

/- The minimum positive period of the function $y=\cos 2x$ is ____.-/
theorem algebra_9453 {f : ℝ → ℝ} (hf : f = fun x => Real.cos (2 * x)) :
    IsLeast {T | 0 < T ∧ f = fun x => f (x + T)} (Real.pi) := by
--   To find the minimum positive period of the function $y=\cos 2x$, we need to understand how the period of the cosine function changes with its argument. The standard period of the cosine function, $\cos x$, is $2\pi$. When the argument of the cosine function is multiplied by a constant, the period of the function is divided by the absolute value of that constant. Therefore, for $y=\cos 2x$, the period is given by:
-- \[
-- \text{Period} = \frac{2\pi}{|2|} = \frac{2\pi}{2} = \pi
-- \]
-- Hence, the minimum positive period of the function $y=\cos 2x$ is $\boxed{\pi}$.
  constructor
  -- Verify that π is a postivie period of $y=\cos 2x$.
  . constructor
    . positivity
    ext x
    simp [hf]
    rw [mul_add, cos_periodic]
  -- Prove that π is the least one by contradiction.
  rintro T ⟨htpos, htperiod⟩
  by_contra h
  push_neg at h
  apply_fun (· 0) at htperiod
  simp [hf] at htperiod
  symm at htperiod
  rw [cos_eq_one_iff] at htperiod
  rcases htperiod with ⟨k, hk⟩
  rcases le_or_lt 1 k with hk1 | hk1
  . rify at hk1
    have : 2 * π ≤ (k : ℝ) * (2 * π) := by nlinarith
    linarith
  rcases le_or_lt k (-1) with hkneg1 | hkneg1
  . rify at hkneg1
    have : (k : ℝ) * (2 * π) ≤ -(2 * π) := by nlinarith
    linarith
  interval_cases k
  norm_num at hk
  linarith
