import Mathlib
/- Let $b$ be an integer such that $b \equiv 2 \pmod 5$. Let $N$ be a positive integer such that $N \equiv 1 \pmod 4$. Determine the remainder when $b^N$ is divided by $5$. Show that the answer is $2$. -/
theorem number_theory_641443 (b : ℤ) (N : ℕ) (hb : b ≡ 2 [ZMOD 5]) (h1 : N ≡ 1 [MOD 4]) : b ^ N ≡ 2 [ZMOD 5]:= by

  -- Prove that N cannot be zero using contradiction
  have h2 : N ≠ 0:= by
    by_contra H
    subst N
    simp [Nat.ModEq] at h1

  -- Convert the modular equivalence N ≡ 1 (mod 4) to divisibility form: 4 | (N-1)
  replace h1 : 4 ∣ N - 1:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))

  -- Express N in terms of some integer k: N = 4k + 1
  rcases h1 with ⟨k, hk⟩
  replace hk : N = 4 * k + 1:= by omega
  subst N

  -- Use the fact that b ≡ 2 (mod 5) to show b^(4k+1) ≡ 2^(4k+1) (mod 5)
  replace hb : b ^ (4 * k + 1) ≡ 2 ^ (4 * k + 1) [ZMOD 5]:= by exact Int.ModEq.pow (4 * k + 1) hb

  -- Rewrite 2^(4k+1) as 2^(4k) * 2
  rw [show (2 : ℤ) ^ (4 * k + 1) = 2 ^ (4 * k) * 2 by ring_nf] at hb

  -- Use the power rule to rewrite 2^(4k) as (2^4)^k
  rw [show (2 : ℤ) ^ (4 * k) = (2 ^ 4) ^ k by exact pow_mul 2 4 k] at hb
  simp at hb

  -- Prove that 16 ≡ 1 (mod 5)
  have h3 : 16 ≡ 1 [ZMOD 5]:= by rfl

  -- Show that 16^k ≡ 1^k (mod 5)
  replace h3 : 16 ^ k ≡ 1 ^ k [ZMOD 5]:= by exact Int.ModEq.pow k h3
  simp at h3

  -- Multiply both sides by 2 to show 16^k * 2 ≡ 1 * 2 (mod 5)
  replace h3 : 16 ^ k * 2 ≡ 1 * 2 [ZMOD 5]:= by exact Int.ModEq.mul h3 rfl
  simp at h3

  -- Complete the proof using transitivity of modular equivalence
  exact Int.ModEq.trans hb h3
