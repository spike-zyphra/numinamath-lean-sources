import Mathlib
/- 3. (17th Japan Mathematical Olympiad) Find the tens digit of $11^{12^{13}}$ (where $11^{12^{3}}$ represents 11 to the power of $12^{13}$) -/
theorem number_theory_190500 : 11 ^ (12 ^ 13) / 10 ≡ 2 [MOD 10]:= by
  -- Establish that 11^10 ≡ 1 (mod 100)
  have h1 : 11 ^ 10 ≡ 1 [MOD 100]:= by rfl
  -- Establish that 12^13 ≡ 2 (mod 10)
  have h2 : 12 ^ 13 ≡ 2 [MOD 10]:= by rfl
  -- Prove that 12^13 ≥ 2 using the omega tactic
  have g1 : 12 ^ 13 ≥ 2:= by omega
  -- Convert the modular congruence to a divisibility statement: 10 divides (12^13 - 2)
  replace h2 : 10 ∣ 12 ^ 13 - 2:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm h2))
  -- Extract the quotient k where 12^13 - 2 = 10k
  rcases h2 with ⟨k, hk⟩
  -- Rewrite as 12^13 = 10k + 2
  replace hk : 12 ^ 13 = 10 * k + 2:= by omega
  -- Define t as 12^13 for cleaner notation
  set t:= 12 ^ 13
  -- Clear the specific value of t to work with it symbolically
  clear_value t
  -- Substitute the value of t in the expression 11^t
  replace hk : 11 ^ t = 11 ^ (10 * k + 2):= by rw [hk]
  -- Use the power rule to split 11^(10k+2) into 11^(10k) * 11^2
  rw [show 11 ^ (10 * k + 2) = 11 ^ (10 * k) * 11 ^ 2 by ring_nf] at hk
  -- Use the power of power rule: 11^(10k) = (11^10)^k
  rw [show 11 ^ (10 * k) = (11 ^ 10) ^ k by exact (Nat.pow_mul 11 10 k)] at hk
  -- Apply modular congruence to powers: (11^10)^k ≡ 1^k (mod 100)
  replace h1 : (11 ^ 10) ^ k ≡ 1 ^ k [MOD 100]:= by exact Nat.ModEq.pow k h1
  -- Simplify expressions
  simp at h1 hk
  -- Multiply both sides of the congruence by 121 (which is 11^2)
  replace h1 : 25937424601 ^ k * 121 ≡ 1 * 121 [MOD 100]:= by exact Nat.ModEq.mul h1 rfl
  -- Simplify the right side of the congruence
  simp at h1
  -- Now we have: 25937424601^k * 121 ≡ 21 (mod 100)
  replace h1 : 25937424601 ^ k * 121 ≡ 21 [MOD 100]:= by exact h1
  -- Prove that 25937424601^k > 0
  replace g1 : 25937424601 ^ k > 0:= by positivity
  -- Strengthen the inequality to 25937424601^k ≥ 1
  replace g1 : 25937424601 ^ k ≥ 1:= by linarith
  -- Convert the modular congruence to a divisibility statement
  replace h1 : 100 ∣ 25937424601 ^ k * 121 - 21:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))
  -- Extract the quotient l where 25937424601^k * 121 - 21 = 100l
  rcases h1 with ⟨l, hl⟩
  -- Rewrite as 25937424601^k * 121 = 100l + 21
  replace hl : 25937424601 ^ k * 121 = 100 * l + 21:= by omega
  -- Substitute this into our expression for 11^t
  rw [hl] at hk
  -- Use hk in our main goal
  rw [hk]
  -- Clean up unnecessary hypotheses
  clear g1 hl hk
  -- Calculate (100l + 21)/10 = 10l + 2
  rw [show (100 * l + 21) / 10 = 10 * l + 2 by refine Nat.div_eq_of_lt_le (by omega) (by omega)]
  -- Establish that 10 ≡ 0 (mod 10)
  have g1 : 10 ≡ 0 [MOD 10]:= by rfl
  -- Multiply both sides by l: 10l ≡ 0l (mod 10)
  replace g1 : 10 * l ≡ 0 * l [MOD 10]:= by exact Nat.ModEq.mul g1 rfl
  -- Simplify the right side
  simp at g1
  -- Add 2 to both sides: 10l + 2 ≡ 0 + 2 (mod 10)
  replace g1 : 10 * l + 2 ≡ 0 + 2 [MOD 10]:= by exact Nat.ModEq.add g1 rfl
  -- Simplify to get 10l + 2 ≡ 2 (mod 10)
  simp at g1
  -- Complete the proof that 11^(12^13)/10 ≡ 2 (mod 10)
  exact g1
