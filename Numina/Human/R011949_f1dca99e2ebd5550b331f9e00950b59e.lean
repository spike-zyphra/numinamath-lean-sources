import Mathlib

/- 11. Given that the domain of the function $f(x)$ is $\mathbf{R}$, for any real number $x$, it always holds that $f(1+x)=f(3-x)$, and $f(2+x)=-f(1-x)$. Then $f(1)+f(2)+\cdots+f(100)=$ $\qquad$ . -/
theorem algebra_158405 {f : ℝ → ℝ} (h1 : ∀ x, f (1 + x) = f (3 - x)) (h2 : ∀ x, f (2 + x) = -f (1 - x)) :
    ∑ i ∈ Finset.range 100, f (i + 1) = 0 := by
  -- plug in (1 - x) in second equation to get - f(x) = f(3 - x) = f(1+x)
  have h3 (x : ℝ) : f (x + 1) = - f x := by
    specialize h2 (1 - x)
    ring_nf at h2 ⊢
    rw [← h1] at h2
    assumption
  -- so f(x) + f(x + 1) = 0, i.e. in the sum we can pair up odd an evens to zero out, we prove this via genralizing the result to 2n and using induction
  rw [show 100 = 2 * 50 by norm_num]
  generalize 50 = n
  induction' n with m hm
  -- empty sum in base case
  . simp
  -- for inductive case, take out last two terms, use hypothesis and h3 to cancel them all.
  . rw [mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ, hm]
    push_cast
    rw [h3 (2 * m + 1)]
    ring_nf