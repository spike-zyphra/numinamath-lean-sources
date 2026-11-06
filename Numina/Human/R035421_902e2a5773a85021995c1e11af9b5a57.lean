import Mathlib

/- Given $a,b,c \in \mathbb{R}$ satisfying $a+b+c=a^2+b^2+c^2=1$, show that $\frac{-1}{4} \leq ab \leq \frac{4}{9}$.
 -/
theorem inequalities_29447 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 1) :
    -1 / 4 ≤ a * b ∧ a * b ≤ 4 / 9 := by
  -- Rewrite to focus c
  have H₂ := congr_arg (fun x => x ^ 2) h₀

  -- Normalize and align with requirements
  ring_nf at H₂

  -- Apply inequalities to prove the bounds
  constructor <;>
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c)]