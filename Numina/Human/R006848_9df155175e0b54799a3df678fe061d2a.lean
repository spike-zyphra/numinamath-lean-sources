import Mathlib
/- Let $x$ be an integer, $a$ be a non-negative integer, and $b$ be a positive integer. Suppose that $x^b - 1 > 1$. (This condition means that either $x \ge 3$ and $b \ge 1$, or $x=2$ and $b \ge 2$.) Show that the remainder when $x^a$ is divided by $x^b - 1$ is equal to $x^r$, where $r$ is the remainder of $a$ when divided by $b$ (that is, $a = qb + r$ for some integer $q$, with $0 \le r < b$). -/
theorem algebra_641696 (x : ℤ) (a b : ℕ) (hb : b > 0) (h : x ^ b - 1 > 1) : x ^ a ≡ x ^ (a % b) [ZMOD x ^ b - 1]:= by
  -- Define r as the remainder when a is divided by b
  set r:= a % b with hr
  clear_value r
  -- Prove that a is congruent to r modulo b
  have hr1 : a ≡ r [MOD b]:= by subst r ; exact Nat.ModEq.symm (Nat.mod_modEq a b)
  -- Establish that a is greater than or equal to r (since r is the remainder)
  have hr2 : a ≥ r:= by subst r ; exact Nat.mod_le a b
  -- Convert the modular congruence to divisibility: b divides (a - r)
  replace hr1 : b ∣ a - r:= by exact (Nat.modEq_iff_dvd' hr2).mp (id (Nat.ModEq.symm hr1))
  -- Extract the quotient q such that a - r = b * q
  rcases hr1 with ⟨q, hq⟩
  -- Rewrite the equation as a = b * q + r (division algorithm)
  replace hq : a = b * q + r:= by omega
  -- Substitute the expression for a into the goal
  subst a
  clear hr hr2
  -- Simplify the ring expression
  ring_nf
  -- Rewrite x^(b*q) as (x^b)^q using the power rule
  rw [show x ^ (b * q) = (x ^ b) ^ q by exact pow_mul x b q]
  -- Prove that x^b ≡ 1 (mod x^b - 1), which is the key modular relationship
  have g1 : x ^ b ≡ 1 [ZMOD -1 + x ^ b]:= by
    -- Show that (x^b - 1) divides (x^b - 1), hence x^b ≡ 1 (mod x^b - 1)
    suffices -1 + x ^ b ∣ x ^ b - 1 by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) this)
    use 1
    ring
  -- Apply the power rule to the congruence: (x^b)^q ≡ 1^q (mod x^b - 1)
  replace g1 : (x ^ b) ^ q ≡ 1 ^ q [ZMOD -1 + x ^ b]:= by exact Int.ModEq.pow q g1
  simp at g1
  -- Multiply both sides by x^r: (x^b)^q * x^r ≡ 1 * x^r (mod x^b - 1)
  replace g1 : (x ^ b) ^ q * x ^ r ≡ 1 * x ^ r [ZMOD -1 + x ^ b]:= by exact Int.ModEq.mul g1 rfl
  simp at g1
  -- This gives us the final result: x^a ≡ x^r (mod x^b - 1)
  exact g1
