import Mathlib

/- Let $f(x)$ be a function with a period of $4$, and when $x \in [0,4]$, $f(x)=x$. Calculate $f(7.6)$.-/
theorem algebra_9081 {f : ℝ → ℝ} (hper : Function.Periodic f 4)
    (hf : ∀ x ∈ Set.Ico 0 4, f x = x) :
    f 7.6 = 3.6 := by
  -- It's clear that 7.6=3.6+4.
  -- Since $f(x)$ is with a period of $4$, we have $f(7.6)=f(3.6)$.
  -- Since 3.6 is in [0, 4), we have $f(3.6)=3.6$.
  rw [show 7.6 = 3.6 + (4 : ℝ) by norm_num, hper, hf]
  . norm_num
