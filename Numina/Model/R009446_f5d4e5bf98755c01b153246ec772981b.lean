import Mathlib

/-
Problem

Given the function $f(x)=x^{2}+x$, find the range of $x$ that satisfies the inequality $f(x-2)+f(x) < 0$.
-/

theorem algebra_9031 {f : ℝ → ℝ} (hf : f = λ x => x^2 + x) :
    ¬ ∃ x, f (x - 2) + f x < 0 := by
  rintro ⟨x, hx⟩
  have hfx : f (x - 2) = (x - 2) ^ 2 + (x - 2) := by
    rw [hf]
  have hfx2 : f x = x ^ 2 + x := by
    rw [hf]
  rw [hfx, hfx2] at hx
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x * (x - 1)), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x * x), sq_nonneg ((x - 2) * (x - 2)), sq_nonneg (2 * x - 1)]