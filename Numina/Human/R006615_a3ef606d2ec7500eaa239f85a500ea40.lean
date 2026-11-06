import Mathlib
/- Let $X$ be a positive integer. Show that the last two digits of $2011^{\left(2010^X\right.)}$ are 01. -/
theorem algebra_639231 (n : ℕ) (hn : n > 0) : 2011 ^ (2010 ^ n) ≡ 1 [MOD 100]:= by
  -- First, we establish that 2010 divides 2010^n (trivially true for n > 0)
  have h1 : 2010 ∣ 2010 ^ n:= by refine dvd_pow_self 2010 (by omega)
  -- Since 10 divides 2010, we have 10 ∣ 2010
  have h2 : 10 ∣ 2010:= by omega
  -- By transitivity, 10 divides 2010^n
  replace h1 : 10 ∣ 2010 ^ n:= by exact dvd_trans h2 h1
  clear h2
  -- Extract the factor: 2010^n = 10*k for some k
  rcases h1 with ⟨k, hk⟩
  rw [hk]
  -- Reduce 2011 modulo 100: 2011 ≡ 11 (mod 100)
  have g1 : 2011 ≡ 11 [MOD 100]:= by rfl
  -- Apply the congruence to the power: 2011^(10*k) ≡ 11^(10*k) (mod 100)
  replace g1 : 2011 ^ (10 * k) ≡ 11 ^ (10 * k) [MOD 100]:= by exact Nat.ModEq.pow (10 * k) g1
  -- It suffices to show that 11^(10*k) ≡ 1 (mod 100)
  suffices 11 ^ (10 * k) ≡ 1 [MOD 100] by exact Nat.ModEq.trans g1 this
  -- Rewrite using power laws: 11^(10*k) = (11^10)^k
  rw [show 11 ^ (10 * k) = (11 ^ 10) ^ k by rw [Nat.pow_mul]]
  simp
  -- Compute 11^10 = 25937424601 ≡ 1 (mod 100)
  have g2 : 25937424601 ≡ 1 [MOD 100]:= by rfl
  -- Apply the congruence to the k-th power: (11^10)^k ≡ 1^k (mod 100)
  replace g2 : 25937424601 ^ k ≡ 1 ^ k [MOD 100]:= by exact Nat.ModEq.pow k g2
  simp at g2
  exact g2
