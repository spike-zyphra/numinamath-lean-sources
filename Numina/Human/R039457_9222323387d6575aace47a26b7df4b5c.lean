import Mathlib

open Real

/-Given that $f(x)$ is an odd function on $\mathbb{R}$, and $f(x) = -x \log_2 (2 - x)$ when $x \in (-\infty, 0)$, determine the expression for $f(x)$ .-/
theorem algebra_9407 {f : ℝ → ℝ}
(hodd : ∀ x, f x = - f (-x)) (hf : ∀ x < 0, f x = -x * logb 2 (2 - x)) :
∀ x, f x = if x < 0 then -x * logb 2 (2 - x) else -x * logb 2 (2 + x) := by
-- Introduce a variable and split the goal to two cases
  intro x; split; rename_i hx
-- When $x$ is negative, we can apply our assumption directly  
  apply hf; assumption
-- When $x$ is $0$, $f x$ is zero since it is an odd function
  rename_i hx; push_neg at hx; rw [le_iff_eq_or_lt] at hx
  cases hx; rename_i hx; symm at hx; simp [hx]
  have := hodd 0; symm at this
  simp at this; rw [neg_eq_self ℝ] at this; assumption
-- When $x$ is positive, apply the parity of $f$ to prove the final goal
  rename_i hx; rw [hodd, hf]; ring_nf
  linarith