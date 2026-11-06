import Mathlib
/- Let $P_0$ and $S_0$ be non-negative integers. Let $X_D$ be an integer digit (from 0 to 9). Let $a$ be a positive integer.
Let $N_k$ be the sequence of integers defined by the formula $N_k = P_640977 \cdot 10^{k+a} + X_D \cdot \frac{10^k-1}{9} \cdot 10^a + S_0$ for $k \ge 0$. (If $k=0$, the term $X_D \cdot \frac{10^k-1}{9} \cdot 10^a$ is zero. This definition means $N_k$ corresponds to the number formed by concatenating the decimal representation of $P_0$, then $k$ repetitions of digit $X_D$, then $S_0$ written as an $a$-digit number, potentially with leading zeros).
Let $m$ be a prime number, $m \neq 3$.
Show that if $m$ divides $(9P_0+X_D) \cdot 10^a$ and $m$ divides $(X_D \cdot 10^a - 9S_0)$, then $N_k$ is divisible by $m$ for all non-negative integers $k$. -/
theorem number_theory_640977 (a m p s d : ℕ) (hm : Nat.Prime m) (hm1 : m ≠ 3) (hd : d < 10) (h1 : m ∣ (9 * p + d) * 10 ^ a) (h2 : (↑m : ℤ) ∣ d * 10 ^ a - 9 * s) : ∀ k : ℕ, m ∣ p * 10 ^ (k + a) + d * ((10 ^ k - 1) / 9) * 10 ^ a + s:= by
  -- Introduce k as a parameter
  intro k
  -- Define x as the expression we want to prove is divisible by m
  set x:= p * 10 ^ (k + a) + d * ((10 ^ k - 1) / 9) * 10 ^ a + s with hx
  -- Clear the definition to work with the expression directly
  clear_value x
  -- Show that m is coprime with 3
  replace hm1 : Nat.Coprime m 3:= by
    -- 3 is prime
    have g : Nat.Prime 3:= by decide
    -- Use the fact that distinct primes are coprime
    exact (Nat.coprime_primes hm g).mpr hm1
  -- Show that m is coprime with 3^2 = 9
  replace hm1 : Nat.Coprime m (3 ^ 2):= by exact Nat.Coprime.pow_right 2 hm1
  -- Simplify the coprime condition
  simp at hm1
  -- Strategy: show m divides 9*x, then use coprimality to conclude m divides x
  suffices m ∣ 9 * x by exact Nat.Coprime.dvd_of_dvd_mul_left hm1 this
  -- Show that 10^k is positive
  have g1 : 10 ^ k > 0:= by positivity
  -- Show that 10^k ≥ 1
  replace g1 : 10 ^ k ≥ 1:= by omega
  -- Expand 9*x to get a form that uses our hypotheses
  have h3 : 9 * x = 9 * p * 10 ^ (k + a) + d * (10 ^ k - 1) * 10 ^ a + 9 * s:= by
    -- Substitute the definition of x
    subst x
    -- Show that 9 * d * ((10^k - 1) / 9) * 10^a = d * (10^k - 1) * 10^a
    suffices 9 * d * ((10 ^ k - 1) / 9) * 10 ^ a = d * (10 ^ k - 1) * 10 ^ a by linarith
    -- Rearrange the expression
    rw [show 9 * d * ((10 ^ k - 1) / 9) * 10 ^ a = (9 * ((10 ^ k - 1) / 9)) * d * 10 ^ a by ring]
    -- Show that 9 * ((10^k - 1) / 9) = 10^k - 1
    suffices 9 * ((10 ^ k - 1) / 9) = (10 ^ k - 1) by rw [this] ; ring
    -- Show that 10 ≡ 1 (mod 9)
    have g : 10 ≡ 1 [MOD 9]:= by rfl
    -- Raise both sides to power k
    replace g : 10 ^ k ≡ 1 ^ k [MOD 9]:= by exact Nat.ModEq.pow k g
    -- Simplify 1^k = 1
    simp at g
    -- Convert congruence to divisibility: 9 ∣ 10^k - 1
    replace g : 9 ∣ 10 ^ k - 1:= by
      exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm g))
    -- Use omega to solve the arithmetic
    omega
  -- Convert to integers for easier manipulation
  zify at h3 ⊢
  -- Simplify fractions
  field_simp at h3
  -- Rearrange the expression to match our hypotheses
  rw [show 9 * (↑p : ℤ) * 10 ^ (k + a) + ↑d * (10 ^ k - 1) * 10 ^ a + 9 * ↑s = (9 * p + d) * 10 ^ a * 10 ^ k + -1 * (d * 10 ^ a - 9 * s) by ring_nf] at h3
  -- Convert hypothesis h1 to integers
  zify at h1
  -- Show that m divides (9*p + d) * 10^a * 10^k
  replace h1 : (↑m : ℤ) ∣ (9 * ↑p + ↑d) * (10 : ℤ) ^ a * 10 ^ k:= by exact Dvd.dvd.mul_right h1 (10 ^ k)
  -- Show that m divides -1 * (d * 10^a - 9 * s)
  replace h2 : (↑m : ℤ) ∣ (-1) * (↑d * 10 ^ a - 9 * ↑s):= by exact Dvd.dvd.mul_left h2 (-1)
  -- Use the rearranged expression
  rw [h3]
  -- Apply the divisibility property: if m divides both terms, it divides their sum
  exact (Int.dvd_add_right h1).mpr h2
