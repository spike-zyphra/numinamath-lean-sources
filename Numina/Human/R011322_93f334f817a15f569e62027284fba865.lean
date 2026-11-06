import Mathlib

open Real Set
open scoped BigOperators
/-Given the function $f(x)=2 \sin x- \sin 2x+ \sqrt{3}$, which of the following statements is incorrect? (   ).

A: There are two zeros in $[-\pi ,\pi ]$.

B: The graph of $f(x)$ is symmetric about the point $(\pi , \sqrt{3})$.

C: The minimum value of $f(x)$ is $- \sqrt{3}$.

D: The maximum value of $f(x)$ is $ \frac{5 \sqrt{3}}{2}$.-/
theorem algebra_8675 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x - sin (2 * x) + sqrt 3) :
    IsLeast (range f) (-sqrt 3) ↔ False := by
  constructor
  · -- Assume -√3 is the least element in the range of f
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨x, hx⟩
    have hfx : f x = -sqrt 3 := hx
    rw [hf] at hfx
    simp at hfx
    have h1 : sin (2 * x) = 2 * sin x * cos x := by rw [sin_two_mul]
    rw [h1] at hfx
    have h2 : sin x * (1 - cos x) = -sqrt 3 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h3 : sin x ^ 2 * (1 - cos x) ^ 2 = 3 := by
      have h4 : sin x * (1 - cos x) = -sqrt 3 := h2
      have h5 : (sin x * (1 - cos x)) ^ 2 = 3 := by
        rw [h4]
        have hsq : (sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
        linarith
      nlinarith [sq_nonneg (sin x), sq_nonneg (1 - cos x), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (sin x - sqrt 3 / 2), sq_nonneg (cos x + 1 / 2), sq_nonneg (cos x - 1)]
  · -- Proof of False implies anything
    intro h
    cases h