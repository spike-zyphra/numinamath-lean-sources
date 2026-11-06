import Mathlib
/- What is the remainder when $2011^{(2011^{(2011^{(2011^{2011})})})}$ is divided by $19$ ?

$\textbf{(A)}\ 5 \qquad\textbf{(B)}\ 4 \qquad\textbf{(C)}\ 3 \qquad\textbf{(D)}\ 2 \qquad\textbf{(E)}\ 1$ -/
theorem number_theory_90837 : (2011 ^ (2011 ^ (2011 ^ (2011 ^ 2011)))) ≡ 5 [MOD 19]:= by
  -- First, we establish that 2011 ≡ 1 (mod 3)
  have h1 : 2011 ≡ 1 [MOD 3]:= by rfl
  -- Define a as 2011^2011 for cleaner notation
  set a:= 2011 ^ 2011
  clear_value a
  -- Using modular arithmetic properties, 2011^a ≡ 1^a ≡ 1 (mod 3)
  replace h1 : 2011 ^ a ≡ 1 ^ a [MOD 3]:= by exact Nat.ModEq.pow a h1
  simp at h1
  -- Establish that 2011^a is positive
  have g1 : 2011 ^ a > 0:= by positivity
  replace g1 : 2011 ^ a ≥ 1:= by linarith
  -- Convert modular congruence to divisibility statement: 3 divides (2011^a - 1)
  replace h1 : 3 ∣ 2011 ^ a - 1:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm h1))
  -- Extract k such that 2011^a - 1 = 3k
  rcases h1 with ⟨k, hk⟩
  -- Rewrite 2011^a as 3k + 1
  replace hk : 2011 ^ a = 3 * k + 1:= by omega
  rw [hk]
  clear hk g1
  -- Establish that 2011^3 ≡ 1 (mod 9)
  have h1 : 2011 ^ 3 ≡ 1 [MOD 9]:= by rfl
  -- Using modular arithmetic properties for powers
  replace h1 : (2011 ^ 3) ^ k ≡ 1 ^ k [MOD 9]:= by exact Nat.ModEq.pow k h1
  -- Simplify the expression using power rules
  rw [show (2011 ^ 3) ^ k = 2011 ^ (3 * k) by exact Eq.symm (Nat.pow_mul 2011 3 k)] at h1
  simp at h1
  -- Define m as 2011 for cleaner notation
  set m:= 2011 with hm
  clear_value m
  -- Rewrite the expression using power rules
  rw [show m ^ (3 * k + 1) = m ^ (3 * k) * m by ring_nf]
  -- Apply modular arithmetic to the product
  replace h1 : m ^ (3 * k) * m ≡ 1 * m [MOD 9]:= by exact Nat.ModEq.mul h1 rfl
  simp at h1
  -- Establish that m^(3*k) is positive
  have g1 : m ^ (3 * k) > 0:= by positivity
  replace g1 : m ^ (3 * k) ≥ 1:= by linarith
  -- Apply the inequality to the product
  replace g1 : m ^ (3 * k) * m ≥ 1 * m:= by exact Nat.mul_le_mul_right m g1
  simp at g1
  -- Establish that m ≡ 4 (mod 9)
  have h2 : m ≡ 4 [MOD 9]:= by rw [hm] ; rfl
  -- Combine congruences to get m^(3*k) * m ≡ 4 (mod 9)
  replace h1 : m ^ (3 * k) * m ≡ 4 [MOD 9]:= by exact Nat.ModEq.trans h1 h2
  -- Convert to divisibility statement: 9 divides (m^(3*k)*m - 4)
  replace h1 : 9 ∣ m ^ (3 * k) * m - 4:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))
  -- Extract l such that m^(3*k)*m - 4 = 9l
  rcases h1 with ⟨l, hl⟩
  -- Rewrite m^(3*k)*m as 9l + 4
  replace hl : m ^ (3 * k) * m = 9 * l + 4:= by omega
  rw [hl]
  clear hl g1 h2
  ring_nf
  rw [show l * 9 = 9 * l by ring_nf]
  -- Establish that m ≡ 16 (mod 19)
  have h1 : m ≡ 16 [MOD 19]:= by rw [hm] ; rfl
  -- Apply power properties to get m^4 ≡ 16^4 (mod 19)
  have h2 : m ^ 4 ≡ 16 ^ 4 [MOD 19]:= by exact Nat.ModEq.pow 4 h1
  -- Establish that 16^4 ≡ 5 (mod 19)
  have h3 : 16 ^ 4 ≡ 5 [MOD 19]:= by rfl
  -- Combine congruences to get m^4 ≡ 5 (mod 19)
  replace h2 : m ^ 4 ≡ 5 [MOD 19]:= by exact Nat.ModEq.trans h2 h3
  clear h3
  -- Square both sides to get m^8 ≡ 25 (mod 19)
  have h3 : m ^ 4 * m ^ 4 ≡ 5 * 5 [MOD 19]:= by exact Nat.ModEq.mul h2 h2
  ring_nf at h3
  -- Multiply by m to get m^9 ≡ 25*16 (mod 19)
  replace h3:= Nat.ModEq.mul h3 h1
  ring_nf at h3
  -- Establish that 400 ≡ 1 (mod 19)
  have h4 : 400 ≡ 1 [MOD 19]:= by rfl
  -- Combine congruences to get m^9 ≡ 1 (mod 19)
  replace h3 : m ^ 9 ≡ 1 [MOD 19]:= by exact Nat.ModEq.trans h3 h4
  clear h4
  -- Apply power properties to get (m^9)^l ≡ 1^l ≡ 1 (mod 19)
  replace h3 : (m ^ 9) ^ l ≡ 1 ^ l [MOD 19]:= by exact Nat.ModEq.pow l h3
  simp at h3
  -- Simplify using power rules
  rw [show (m ^ 9) ^ l = m ^ (9 * l) by exact Eq.symm (Nat.pow_mul m 9 l)] at h3
  -- Rewrite 5 as 5*1 for the final step
  rw [show 5 = 5 * 1 by ring_nf]
  -- Combine m^4 ≡ 5 (mod 19) and m^(9*l) ≡ 1 (mod 19) to get the final result
  exact Nat.ModEq.mul h2 h3
