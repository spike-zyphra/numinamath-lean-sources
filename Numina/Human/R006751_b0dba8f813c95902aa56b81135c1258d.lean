import Mathlib
/- Theorem: Let $k$ be a positive integer and let the base $a=2$. Compute the greatest common divisor of $a^{2k} - 1$ and $a^{3k} - 1$. Show that the answer is $a^k - 1$. -/
theorem algebra_640792 (k : ℕ) (hk : k > 0) : Int.gcd (2 ^ (2 * k) - 1) (2 ^ (3 * k) - 1) = 2 ^ k - 1:= by
  -- Rewrite 2*k as k*2 for easier manipulation
  rw [show 2 * k = k * 2 by omega]
  -- Rewrite 3*k as k*3 for easier manipulation
  rw [show 3 * k = k * 3 by omega]
  -- Apply power multiplication rule: (2^k)^2 = 2^(k*2)
  rw [show (2 : ℤ) ^ (k * 2) = (2 ^ k) ^ 2 by exact pow_mul 2 k 2]
  -- Apply power multiplication rule: (2^k)^3 = 2^(k*3)
  rw [show (2 : ℤ) ^ (k * 3) = (2 ^ k) ^ 3 by exact pow_mul 2 k 3]
  -- Substitute a = 2^k to simplify the expressions
  set a:= (2 : ℤ) ^ k with ha
  -- Clear the definition to work with a as a general variable
  clear_value a
  -- Factor a^2 - 1 as difference of squares: (a-1)(a+1)
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring]
  -- Factor a^3 - 1 using sum of cubes formula: (a-1)(a^2+a+1)
  rw [show a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) by ring]
  -- Apply gcd multiplication property: gcd((a-1)*b, (a-1)*c) = |a-1| * gcd(b,c)
  rw [show ((a - 1) * (a + 1)).gcd ((a - 1) * (a ^ 2 + a + 1)) = (a - 1).natAbs * Int.gcd (a + 1) (a ^ 2 + a + 1) by exact Int.gcd_mul_left (a - 1) (a + 1) (a ^ 2 + a + 1)]
  -- Prove that |a-1| = 2^k - 1
  have g1 : (a - 1).natAbs = 2 ^ k - 1:= by
    -- Substitute back a = 2^k
    subst a
    -- Convert to integer arithmetic
    zify
    -- Simplify field operations
    field_simp
    -- Show that 2^k > 0, which implies 2^k - 1 ≥ 0
    suffices 2 ^ k > 0 by linarith
    -- 2^k is always positive
    positivity
  -- Prove that gcd(a+1, a^2+a+1) = 1 (they are coprime)
  have g2 : Int.gcd (a + 1) (a ^ 2 + a + 1) = 1:= by
    -- Show coprimality instead of direct gcd calculation
    suffices IsCoprime (a + 1) (a ^ 2 + a + 1) by exact Int.gcd_eq_one_iff_coprime.mpr this
    -- Expand the definition of coprimality
    simp [IsCoprime]
    -- Provide Bezout coefficients: (-a) * (a+1) + 1 * (a^2+a+1) = 1
    use -a, 1
    -- Verify the linear combination equals 1
    ring_nf
  -- Apply our proven lemmas g1 and g2
  rw [g1, g2]
  -- Simplify: (2^k - 1) * 1 = 2^k - 1
  simp
