import Mathlib
/- Let $a, b, c$ be nonzero real numbers such that $a+b+c=0$ and $a^{3}+b^{3}+c^{3}=a^{5}+b^{5}+c^{5}$. Find the value of $a^{2}+b^{2}+c^{2}$. -/
theorem algebra_608336 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h1 : a + b + c = 0) (h2 : a ^ 3 + b ^ 3 + c ^ 3 = a ^ 5 + b ^ 5 + c ^ 5) : a ^ 2 + b ^ 2 + c ^ 2 = 6 / 5:= by
  -- Using the identity a³+b³+c³=3abc when a+b+c=0
  have h3 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c:= by
    -- Rewrite a in terms of b and c using a+b+c=0
    replace h1 : a = - b - c:= by linarith
    -- Substitute the expression for a
    subst a
    -- Simplify using ring normalization
    ring_nf
  -- Using the identity a⁵+b⁵+c⁵=-5abc(ab+bc+ca) when a+b+c=0
  have h4 : a ^ 5 + b ^ 5 + c ^ 5 = -5 * a * b * c * (a * b + b * c + c * a):= by
    -- Rewrite a in terms of b and c using a+b+c=0
    replace h1 : a = - b - c:= by linarith
    -- Substitute the expression for a
    subst a
    -- Simplify using ring normalization
    ring_nf
  -- Substitute the identities into the second condition
  rw [h3, h4] at h2
  -- Prove that abc is nonzero (since a, b, c are all nonzero)
  have h5 : a * b * c ≠ 0:= by positivity
  -- Rearrange the equation to get abc(ab+bc+ca+3/5)=0
  replace h2 : a * b * c * (a * b + b * c + c * a + 3 / 5) = 0:= by linarith
  -- Since abc≠0, we must have ab+bc+ca+3/5=0
  simp [h5] at h2
  -- From a+b+c=0, we get (a+b+c)²=0
  replace h1 : (a + b + c) ^ 2 = 0:= by rw [h1] ; simp
  -- Complete the proof using linear arithmetic
  linarith
