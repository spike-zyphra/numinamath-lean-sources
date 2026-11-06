import Mathlib
/- Let $e$ be a non-zero even natural number. Compute the value of $580^e \pmod 7$. Show the answer is 1. -/
theorem algebra_637334 (e : ℕ) (h1 : e ≠ 0) (h2 : Even e) : 580 ^ e ≡ 1 [MOD 7]:= by
  -- Deconstruct the Even hypothesis into k where e = 2k
  rcases h2 with ⟨k, rfl⟩
  -- Rewrite k + k as 2 * k using ring arithmetic
  rw [show k + k = 2 * k by ring]
  -- Use the power multiplication rule: (580^2)^k = 580^(2k)
  rw [show 580 ^ (2 * k) = (580 ^ 2) ^ k by exact Nat.pow_mul 580 2 k]
  -- Simplify expressions
  simp
  -- Apply modular arithmetic: 336400^k ≡ 1^k (mod 7)
  have h2 : 336400 ^ k ≡ 1 ^ k [MOD 7]:= by exact Nat.pow_mod 336400 k 7
  -- Simplify the congruence
  simp at h2
  -- Complete the proof using the simplified congruence
  exact h2
