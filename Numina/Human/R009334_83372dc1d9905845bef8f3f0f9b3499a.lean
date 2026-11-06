import Mathlib
/- A sequence is defined by $a_{0}=1$ and $a_{n}=2^{a_{n-1}}$ for $n \geq 1$. What is the last digit (in base 10) of $a_{15}$ ? -/
theorem number_theory_611066 (a : ℕ → ℕ) (h0 : a 0 = 1) (hn : ∀ n, a (n + 1) = 2 ^ a n) : a 15 ≡ 6 [MOD 10]:= by
  -- First, we prove that all terms in the sequence are at least 1
  have h1 : ∀ n : ℕ, a n ≥ 1:= by
    intro n
    induction n with
    | zero =>
      simp
      linarith
    | succ n _ =>
      simp
      rw [hn n]
      exact Nat.one_le_two_pow

  -- We prove that a₁₃ ≥ 2
  have h2 : a 13 ≥ 2:= by
    rw [hn 12]
    specialize h1 12
    refine Nat.le_self_pow (by omega) 2

  -- We prove that 4 divides a₁₄
  have h3 : 4 ∣ a 14:= by
    rw [hn 13]
    rw [show a 13 = a 13 - 2 + 2 by omega]
    rw [show 2 ^ (a 13 - 2 + 2) = 2 ^ (a 13 - 2) * 2 ^ 2 by ring]
    simp

  -- Restate the divisibility as an existential statement: a₁₄ = 4k for some k
  replace h3 : ∃ k : ℕ, a 14 = 4 * k:= by exact h3
  rcases h3 with ⟨k, hk⟩

  -- Prove that 6^(n+1) ≡ 6 (mod 10) for all n
  have h3 : ∀ n : ℕ, 6 ^ (n + 1) ≡ 6 [MOD 10]:= by
    intro n
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [show 6 ^ (n + 1 + 1) = 6 ^ (n + 1) * 6 by ring]
      replace ih : 6 ^ (n + 1) * 6 ≡ 6 * 6 [MOD 10]:= by exact Nat.ModEq.mul ih rfl
      exact ih

  -- Calculate a₁₅ using the recurrence relation
  rw [hn 14]
  rw [hk]

  -- Rewrite 2^(4k) as (2^4)^k = 16^k
  rw [show 2 ^ (4 * k) = (2 ^ 4) ^ k by exact Nat.pow_mul 2 4 k]
  simp

  -- Show that 16 ≡ 6 (mod 10)
  have h4 : 16 ≡ 6 [MOD 10]:= by rfl

  -- Therefore 16^k ≡ 6^k (mod 10)
  replace h4 : 16 ^ k ≡ 6 ^ k [MOD 10]:= by exact Nat.ModEq.pow k h4

  -- Prove that k > 0
  have h5 : k > 0:= by
    by_contra H
    simp at H
    subst k
    simp at hk
    specialize h1 14
    linarith

  -- Use the fact that 6^k ≡ 6 (mod 10) for k ≥ 1
  specialize h3 (k - 1)
  rw [show k - 1 + 1 = k by omega] at h3

  -- Conclude that a₁₅ = 16^k ≡ 6^k ≡ 6 (mod 10)
  exact Nat.ModEq.trans h4 h3
