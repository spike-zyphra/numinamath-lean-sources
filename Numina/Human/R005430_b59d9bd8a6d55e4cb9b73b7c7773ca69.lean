import Mathlib

open Finset

/-Let $f(x)=1+x+x^{2}+\cdots+x^{100}$. Find $f^{\prime}(1)$.-/
theorem calculus_608262 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑ i ∈ range 101, x ^ i) :
deriv f 1 = 5050 := by
-- Compute the derivative of $f$ using deriv_sum
  have df : ∀ x, deriv f x = ∑ i ∈ range 101, i * x ^ (i - 1) := by
    intro x; rw [funext_iff.mpr hf, deriv_sum]; apply sum_congr rfl
    intros; rw [deriv_pow]; intros; apply differentiableAt_pow
-- Plug in $x=1$ to compute $f'(1)=5050$
  rw [df]; simp; norm_num