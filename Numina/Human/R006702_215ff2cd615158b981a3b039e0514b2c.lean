import Mathlib
/- Let $d$ be a positive natural number and $r$ be a natural number such that $0 \le r < d$.
Suppose $n$ is a natural number such that $n$ gives a remainder of $r$ when divided by $d$.
What remainder does $2n+1$ give when divided by $d$? Show the answer is $(2r+1) \pmod d$. -/
theorem number_theory_640311 (n d r : ℕ) (hr : r < d) (hn : r = n % d) : (2 * n + 1) % d = (2 * r + 1) % d:= by
  -- Prove that n ≡ r [MOD d]
  replace hn : n ≡ r [MOD d]:= by
    subst r
    exact Nat.ModEq.symm (Nat.mod_modEq n d)
  -- Prove that 2 * n ≡ 2 * r [MOD d]
  replace hn : 2 * n ≡ 2 * r [MOD d]:= by exact Nat.ModEq.mul rfl hn
  -- Prove that (2 * n + 1) ≡ (2 * r + 1) [MOD d]
  exact Nat.add_mod_eq_add_mod_right 1 hn

