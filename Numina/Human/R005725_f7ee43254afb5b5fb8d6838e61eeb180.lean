import Mathlib
/- Let $p(x)=x^{2}-x+1$. Let $\alpha$ be a root of $p(p(p(p(x)))$. Find the value of

$$
(p(\alpha)-1) p(\alpha) p(p(\alpha)) p(p(p(\alpha))
$$ -/
theorem algebra_609600 (p : ℝ → ℝ) (hp : p = fun x => x ^ 2 - x + 1) (a : ℝ) (ha : p (p (p (p a))) = 0) : (p a - 1) * p a * p (p a) * p (p (p a)) = -1:= by
  -- Prove that for any real x, (x-1)*x = p(x)-1
  have h1 : ∀ x : ℝ, (x - 1) * x = p x - 1:= by
    intro x
    simp [hp]
    linarith
  -- Apply the above identity to p(a)
  rw [h1 (p a)]
  -- Apply the identity to p(p(a))
  rw [h1 (p (p a))]
  -- Apply the identity to p(p(p(a)))
  specialize h1 (p (p (p a)))
  -- Use the hypothesis ha
  rw [ha] at h1
  -- Apply the final transformation
  rw [h1]
  -- Simplify to complete the proof
  simp
