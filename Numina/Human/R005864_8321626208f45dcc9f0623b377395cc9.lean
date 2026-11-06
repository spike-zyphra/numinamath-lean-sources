import Mathlib
/- Let $p, q, r$ be primes such that $2 p+3 q=6 r$. Find $p+q+r$. -/
theorem number_theory_610353 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (h : 2 * p + 3 * q = 6 * r) : p + q + r = 7:= by
  -- Prove that 3 divides 6r by rewriting 6 as 3*2
  have h1 : 3 ∣ 6 * r:= by
    rw [show 6 = 3 * 2 by omega]
    rw [show 3 * 2 * r = 3 * (2 * r) by omega]
    simp
  -- Substitute the original equation into h1
  rw [←h] at h1
  -- Prove that 3 divides 3q (trivial)
  have h2 : 3 ∣ 3 * q:= by simp
  -- Since 3 divides 2p + 3q and 3 divides 3q, 3 must divide 2p
  replace h1 : 3 ∣ 2 * p:= by exact (Nat.dvd_add_iff_left h2).mpr h1
  -- By prime divisibility, if 3 divides 2p, then either 3 divides 2 or 3 divides p
  replace h1 : 3 ∣ 2 ∨ 3 ∣ p:= by refine (Nat.Prime.dvd_mul (by decide)).mp h1
  -- Split into two cases based on whether 3 divides 2 or 3 divides p
  rcases h1 with h1 | h1
  -- Case 1: 3 divides 2 (impossible)
  .
    by_contra _
    omega
  -- Case 2: 3 divides p
  .
    -- Since p is prime and 3 divides p, either 3 = 1 or 3 = p
    replace h1 : 3 = 1 ∨ 3 = p:= by exact (Nat.dvd_prime hp).mp h1
    simp at h1
    -- From h1, we know p = 3
    rw [←h1] at h
    simp at h
    -- Prove that 6 divides 6r (trivial)
    have h3 : 6 ∣ 6 * r:= by simp
    -- Substitute the simplified equation into h3
    rw [←h] at h3
    simp at h3
    -- Since 6 divides 3q, there exists k such that 3q = 6k
    replace h3 : ∃ k : ℕ, 3 * q = 6 * k:= by exact h3
    rcases h3 with ⟨k, hk⟩
    -- Simplify to get q = 2k, meaning 2 divides q
    replace hk : q = k * 2:= by omega
    replace hk : 2 ∣ q:= by rw [hk] ; simp
    -- Since q is prime and 2 divides q, either 2 = 1 or 2 = q
    replace hk : 2 = 1 ∨ 2 = q:= by exact (Nat.dvd_prime hq).mp hk
    simp at hk
    -- From hk, we know q = 2
    rw [←hk] at h
    simp at h
    -- Use linear arithmetic to complete the proof
    linarith
