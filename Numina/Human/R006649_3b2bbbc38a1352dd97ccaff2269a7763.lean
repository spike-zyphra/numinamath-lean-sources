import Mathlib
/- Let $m$ and $k$ be positive integers. Let $\varphi$ denote Euler's totient function. Show that $\varphi(m^k) = m^{k-1} \varphi(m)$. -/
theorem number_theory_639668 (m k : ℕ) (hm : m > 0) (hk : k > 0) : Nat.totient (m ^ k) = m ^ (k - 1) * Nat.totient m:= by
  -- Helper lemma: Prove by induction that φ(m^(k+1)) = m^k * φ(m) for all k
  have h1 : ∀ k : ℕ, Nat.totient (m ^ (k + 1)) = m ^ k * Nat.totient m:= by
    intro k
    induction k with
    -- Base case: k = 0
    | zero =>
      simp
    -- Inductive step: Prove for k + 1 assuming it holds for k
    | succ k ih =>
      -- Use the relationship between totient of product and GCD
      have h1:= Nat.totient_gcd_mul_totient_mul m (m ^ (k + 1))
      -- Prove that gcd(m, m^(k+1)) = m
      have h2 : Nat.gcd m (m ^ (k + 1)) = m:= by
        suffices m ∣ m ^ (k + 1) by exact Nat.gcd_eq_left this
        use m ^ k
        ring
      rw [h2] at h1
      -- Rearrange multiplication terms
      rw [show m.totient * (m ^ (k + 1)).totient * m = m.totient * ((m ^ (k + 1)).totient * m) by ring] at h1
      -- Use positivity of totient function
      have h3:= Nat.totient_pos.2 hm
      -- Apply cancellation law
      replace h1 : (m * m ^ (k + 1)).totient = ((m ^ (k + 1)).totient * m):= by exact Nat.eq_of_mul_eq_mul_left h3 h1
      -- Simplify exponents
      rw [show m * m ^ (k + 1) = m ^ (k + 1 + 1) by ring_nf] at h1
      rw [h1, ih]
      ring
  -- Apply the helper lemma with k-1 to prove the main theorem
  specialize h1 (k - 1)
  rw [show k - 1 + 1 = k by omega] at h1
  rw [h1]
