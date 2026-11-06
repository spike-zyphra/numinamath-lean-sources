import Mathlib

/- A function is defined as $f(x) = x^2 - 3x + 4$. What expression can be used to describe $f(2x)$? Express your answer in simplified form in terms of $x$. -/
theorem algebra_20715 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 - 3 * x + 4) :
    ∀ x, f (2 * x) = 4 * x ^ 2 - 6 * x + 4 := by
  intro x
  simp only [hf, add_left_inj]
  ring_nf