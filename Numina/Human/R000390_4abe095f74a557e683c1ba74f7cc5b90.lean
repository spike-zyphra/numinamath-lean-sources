import Mathlib


/-Given real numbers $a$ and $b$ satisfy $a^3 - b^3 = 4$ and $a^2 + ab + b^2 + a - b = 4$, then $a - b =$ ?-/
theorem algebra_9384 {a b : ℝ} (h₀ : a^3 - b^3 = 4) (h₁ : a^2 + a * b + b^2 + a - b = 4) :
  a - b = 2 := by
  -- Since $a^3 - b^3 = (a - b)(a^2 + ab + b^2) = 4$,
  -- and also $a^2 + ab + b^2 + a - b = 4$,
  have c1 : a^3 - b^3 = (a - b) * (a^2 + a*b + b^2) := by nlinarith
  rw [h₀] at c1
  have c2 : a^2 + a*b + b^2 = 4 - (a - b) := by linarith
  -- thus $(a - b)[4 - (a - b)] = 4$,
  rw [c2] at c1
  -- solving this, we get $a - b = 2$, therefore, the answer is $\boxed{2}$.
  nlinarith
