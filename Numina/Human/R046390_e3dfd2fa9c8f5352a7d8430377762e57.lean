import Mathlib

open Real Set
open scoped BigOperators

/- Find the smallest positive period of the function $f(x)=\sqrt{3}\sin x+\cos x$.-/
theorem algebra_9370 {f : ℝ → ℝ} (hf : f = λ x => sqrt 3 * sin x + cos x) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (2 * π) := by
  -- 1. First, let's simplify the given function $f(x)=\sqrt{3}\sin x+\cos x$.
  -- 2. Recall the auxiliary angle formula: $\sin(A+B)=\sin A\cos B+\cos A\sin B$.
  -- 3. We can write $f(x)$ in the form $R\sin(x+\alpha)$, where $R=\sqrt{(\sqrt{3})^2+1^2}=2$ and $\alpha=\arctan\left(\frac{1}{\sqrt{3}}\right)=\frac{\pi}{6}$.
  -- 4. Therefore, $f(x)=2\sin\left(x+\frac{\pi}{6}\right)$.
  have two_mul_sin_x_add_pi_div_six (x : ℝ) : 2 * sin (x + π / 6) = sqrt 3 * sin x + cos x := by
    rw [sin_add, cos_pi_div_six, sin_pi_div_six]
    ring
  constructor
  -- 5. The general formula for the period of a sine-like function is $T=\frac{2\pi}{B}$, where $B$ is the coefficient of $x$ within the sine function.
  --6. In our case, $B=1$.
  . constructor
    . positivity
    simp [hf]
  --7. Hence, the period $T=\frac{2\pi}{1}=2\pi$.
  rintro T ⟨htpos, htperiod⟩
  by_contra h
  push_neg at h
  specialize htperiod
  apply_fun (· (π / 2 - π / 6)) at htperiod
  simp [hf] at htperiod
  rw [← two_mul_sin_x_add_pi_div_six, ← two_mul_sin_x_add_pi_div_six] at htperiod
  simp at htperiod
  rw [sin_eq_one_iff] at htperiod
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
