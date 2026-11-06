import Mathlib

/- What is the remainder when $5^{30}$ is divided by 7?-/
theorem number_theory_23240 : 5^30 % 7 = 1 := by
  -- Since $5^6 \equiv 1 \pmod{7},$ we see that $5^{30} \equiv (5^6)^5 \equiv 1 \pmod{7},$ hence our desired remainder is $\boxed{1}.$
  rw [show 30 = 6 * 5 by norm_num, pow_mul]
  change _ ≡ 1 [MOD 7]
  suffices 5 ^ 6 ≡ 1 [MOD 7] by exact this.pow 5
  --   Let us look at the powers of $5$: \begin{align*}
  -- 5^1 &\equiv 5 \pmod{7} \\
  -- 5^2 &\equiv 4 \pmod{7} \\
  -- 5^3 &\equiv 6 \pmod{7} \\
  -- 5^4 &\equiv 2 \pmod{7} \\
  -- 5^5 &\equiv 3 \pmod{7} \\
  -- 5^6 &\equiv 1 \pmod{7}.
  -- \end{align*}
  norm_num [Nat.ModEq]
