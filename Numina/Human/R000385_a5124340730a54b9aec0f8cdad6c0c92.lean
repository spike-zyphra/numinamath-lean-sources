import Mathlib

/- Given that $f(x)$ is an even function, when $x < 0$, $f(x)=x^{2}+x$, find $f(3)=$ ___. -/
theorem algebra_9349 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x) (h₁ : ∀ x < 0, f x = x^2 + x):f 3 = 6 := by
have h1: f 3 = f (-3) := by
  symm
  apply h₀ 3
have h2: f (-3) = 6 := by
  rcases h₁ (-3) with ht1
  have ht2: (-3:ℝ) < 0 := by norm_num
  have: f (-3) = (-3)^2 + -3 := ht1 ht2
  rw [this]
  linarith [norm_num]
rw [h1, h2]