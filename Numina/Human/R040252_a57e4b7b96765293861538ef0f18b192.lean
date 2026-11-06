import Mathlib

/- Let $p$ be a polynomial with integer coefficients such that $p(-n)<p(n)<n$ for some integer $n$. Prove that $p(-n)<-n$. -/
theorem algebra_237164 {p : Polynomial ℤ} (n : ℤ) (h₁ : p.eval (-n) < p.eval n) (h₂ : p.eval n < n) :
    p.eval (-n) < -n := by
  -- If n ≤ 0, then p(-n) < p(n) < n ≤ -n, so we are done.
  wlog hn : n > 0
  {
    linarith
  }
  -- We assume n > 0.
  -- We have a - b | p(a) - p(b) for all a, b ∈ ℤ.
  -- Apply this to a = n, b = -n.
  -- So p(n) - p(-n) = 2kn for some integer k.
  have ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub n (-n) p
  simp at hk
  -- We have k > 0 and p(-n) = p(n) - 2kn < n - 2n = -n.
  have h : k > 0 := by nlinarith
  nlinarith
