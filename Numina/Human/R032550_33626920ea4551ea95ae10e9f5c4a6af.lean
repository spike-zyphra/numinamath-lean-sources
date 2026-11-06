import Mathlib
/- Find the last two digits of $1032^{1032}$. Express your answer as a two-digit number. -/
theorem number_theory_608584 : 1032 ^ 1032 ≡ 76 [MOD 100]:= by
  -- Define m as 1032 and remember this definition with hm
  set m:= 1032 with hm
  -- Clear the specific value of m to work with it symbolically
  clear_value m
  -- Prove that m is congruent to 32 modulo 100
  have h1 : m ≡ 32 [MOD 100]:= by rw [hm] ; rfl
  -- Use the property that if a ≡ b (mod n), then a^k ≡ b^k (mod n)
  replace h1 : m ^ m ≡ 32 ^ m [MOD 100]:= by exact Nat.ModEq.pow m h1
  -- Define k as 257 and remember this definition with hk
  set k:= 257 with hk
  -- Clear the specific value of k to work with it symbolically
  clear_value k
  -- Prove that m = 4k + 4 (1032 = 4 × 257 + 4)
  have hmk : m = 4 * k + 4:= by linarith
  -- Prove that 32^(4t+1) ≡ 32 (mod 100) for all natural numbers t
  have h2 : ∀ t : ℕ, 32 ^ (4 * t + 1) ≡ 32 [MOD 100]:= by
    intro t
    -- Prove by induction on t
    induction t with
    -- Base case: t = 0
    | zero =>
      simp
      rfl
    -- Inductive step: assume true for t, prove for t+1
    | succ t ih =>
      -- Rewrite 4(t+1)+1 as (4t+1)+4
      rw [show 4 * (t + 1) + 1 = 4 * t + 1 + 4 by ring]
      -- Use the property that a^(b+c) = a^b × a^c
      rw [show 32 ^ (4 * t + 1 + 4) = (32 ^ (4 * t + 1)) * 32 ^ 4 by ring]
      -- Apply the induction hypothesis with multiplication
      replace ih : 32 ^ (4 * t + 1) * 32 ^ 4 ≡ 32 * 32 ^ 4 [MOD 100]:= by exact Nat.ModEq.mul ih rfl
      exact ih
  -- Define a as 32 and remember this definition with ha
  set a:= 32 with ha
  -- Clear the specific value of a to work with it symbolically
  clear_value a
  -- Apply the lemma h2 with t = k (257)
  specialize h2 k
  -- Multiply both sides by a^3
  replace h2 : a ^ (4 * k + 1) * a ^ 3 ≡ a * a ^ 3 [MOD 100]:= by exact Nat.ModEq.mul h2 rfl
  -- Simplify the left side using exponent rules
  rw [show a ^ (4 * k + 1) * a ^ 3 = a ^ (4 * k + 4) by ring] at h2
  -- Substitute m = 4k + 4
  rw [←hmk] at h2
  -- Simplify the right side using exponent rules
  rw [show a * a ^ 3 = a ^ 4 by ring] at h2
  -- Combine previous results to show m^m ≡ a^4 (mod 100)
  replace h2 : m ^ m ≡ a ^ 4 [MOD 100]:= by exact Nat.ModEq.trans h1 h2
  -- Calculate that 32^4 ≡ 76 (mod 100)
  have h3 : a ^ 4 ≡ 76 [MOD 100]:= by
    rw [ha]
    rfl
  -- Conclude that 1032^1032 ≡ 76 (mod 100)
  exact Nat.ModEq.trans h2 h3
