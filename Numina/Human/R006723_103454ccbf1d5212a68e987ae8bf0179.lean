import Mathlib
/- Let $q_0$ and $r_0$ be fixed positive integers such that $q_640547 > 1$.
A four-digit number $N$ has its first digit $d$ and its remaining part as a three-digit number $m$. So $N = 1000d + m$.
When $N$ is divided by $m$, the quotient is $q_0$ and the remainder is $r_0$.
Determine all possible values for $N$.
Show that the set of all possible values of $N$ is
$\{ 1000d + m_d \mid d \in \{1, \dots, 9\} \text{ where } m_d = \frac{1000d - r_0}{q_0-1} \text{ such that } (1000d - r_0) \text{ is divisible by } (q_0-1) \text{, and } m_d \text{ is an integer satisfying } 100 \le m_d \le 999 \text{ and } r_640547 < m_d \}$. -/
theorem number_theory_640547 (q r n m d : ℕ) (hq : q > 1) (hr : 0 < r ∧ r < m) (hn : n = 1000 * d + m) (hd : 1 ≤ d ∧ d ≤ 9) (hm : 100 ≤ m ∧ m ≤ 999) : (n / m = q ∧ n % m = r) ↔ (q - 1 ∣ 1000 * d - r ∧ m = (1000 * d - r) / (q - 1)):= by
  -- Split the proof into two directions
  constructor
  .
    -- First direction: assume n / m = q and n % m = r, prove the explicit formula
    intro h
    rcases h with ⟨h1, h2⟩
    -- n = m * (n / m) + n % m by definition of division
    have h3 : n = m * (n / m) + n % m:= by exact Eq.symm (Nat.div_add_mod n m)
    -- Substitute the given values into h3
    rw [h1, h2, hn] at h3
    -- Rearranging gives 1000 * d - r = m * q - m
    replace h3 : 1000 * d - r = m * q - m:= by omega
    -- Show m * q - m = m * (q - 1)
    have g : m * q - m = m * (q - 1):= by
      -- Set p = q - 1
      set p:= q - 1 with hp
      -- Clear the value of p for further manipulation
      clear_value p
      -- Express q in terms of p
      replace hp : q = p + 1:= by omega
      -- Substitute and simplify
      rw [hp]
      ring_nf
      omega
    -- Substitute back into h3
    rw [g] at h3
    -- Prove both required conditions
    refine ⟨?_, ?_⟩
    .
      -- Show q - 1 divides 1000 * d - r
      use m
      linarith
    .
      -- Show m = (1000 * d - r) / (q - 1)
      rw [h3]
      replace hq : q - 1 > 0:= by omega
      exact Eq.symm (Nat.mul_div_left m hq)
  .
    -- Second direction: assume the explicit formula, prove n / m = q and n % m = r
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨k, hk⟩
    replace hq : q - 1 > 0:= by omega
    -- Substitute the divisibility condition into h2
    rw [hk] at h2
    -- Simplify the division
    rw [show (q - 1) * k / (q - 1) = k by exact Nat.mul_div_right k hq] at h2
    -- Substitute k = m
    subst k
    -- Rearranging gives 1000 * d - r + m = (q - 1) * m + m
    replace hk : 1000 * d - r + m = (q - 1) * m + m:= by omega
    -- Simplify (q - 1) * m + m = (q - 1 + 1) * m
    rw [show (q - 1) * m + m = (q - 1 + 1) * m by ring] at hk
    -- Simplify q - 1 + 1 = q
    rw [show q - 1 + 1 = q by omega] at hk
    -- Rearranging gives 1000 * d + m = q * m + r
    replace hk : 1000 * d + m = q * m + r:= by omega
    -- Substitute into hn
    rw [hk] at hn
    -- Prove both required conditions
    refine ⟨?_, ?_⟩
    .
      -- Show n / m = q
      refine Nat.div_eq_of_lt_le (by linarith) (by linarith)
    .
      -- Show n % m = r
      subst n
      refine Nat.mul_add_mod_of_lt (by linarith)
