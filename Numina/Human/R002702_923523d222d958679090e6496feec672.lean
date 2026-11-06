import Mathlib
/- What are the last two digits of $7^{9^{9^{9}}}$? -/
theorem number_theory_101946 : 7 ^ (9 ^ (9 ^ 9)) ≡ 7 [MOD 100]:= by
  -- Define m as 9^(9^9) for easier reference
  set m:= 9 ^ (9 ^ 9) with hm
  clear_value m
  -- Establish that 9 is congruent to 1 modulo 4
  have h1 : 9 ≡ 1 [MOD 4]:= by rfl
  -- Define n as 9^9 for easier reference
  set n:= 9 ^ 9 with hn
  clear_value n
  -- Use the property that if a ≡ b [MOD m], then a^n ≡ b^n [MOD m]
  replace h1 : 9 ^ n ≡ 1 ^ n [MOD 4]:= by exact Nat.ModEq.pow n h1
  -- Simplify 1^n to 1
  simp at h1
  -- Substitute m back into the equation
  rw [←hm] at h1
  -- Prove that m is greater than 0
  have h2 : m > 0:= by
    subst m
    positivity
  -- Strengthen the inequality to m ≥ 1
  replace h2 : m ≥ 1:= by omega
  -- Convert the modular congruence to a divisibility statement
  replace h1 : 4 ∣ m - 1:= by exact (Nat.modEq_iff_dvd' h2).mp (id (Nat.ModEq.symm h1))
  -- Express the divisibility as an explicit equation with a natural number k
  replace h1 : ∃ k : ℕ, m - 1 = 4 * k:= by exact h1
  -- Extract k from the existential statement
  rcases h1 with ⟨k, hk⟩
  -- Rewrite m in terms of k
  replace hk : m = 4 * k + 1:= by omega
  -- Clean up unnecessary hypotheses
  clear hm hn
  -- Substitute the expression for m
  subst m
  -- Rewrite 7^(4k+1) as 7 * 7^(4k)
  rw [show 7 ^ (4 * k + 1) = 7 * (7 ^ (4 * k)) by ring]
  -- Use the property that (a^b)^c = a^(b*c)
  rw [show 7 ^ (4 * k) = (7 ^ 4) ^ k by exact Nat.pow_mul 7 4 k]
  -- Establish that 7^4 ≡ 1 [MOD 100]
  have h1 : 7 ^ 4 ≡ 1 [MOD 100]:= by rfl
  -- Apply the power property of modular congruence
  replace h1 : (7 ^ 4) ^ k ≡ 1 ^ k [MOD 100]:= by exact Nat.ModEq.pow k h1
  -- Simplify 1^k to 1
  simp at h1 ⊢
  -- Multiply both sides by 7
  replace h1 : 7 * 2401 ^ k ≡ 7 * 1 [MOD 100]:= by exact Nat.ModEq.mul rfl h1
  -- Simplify the right side
  simp at h1
  -- Complete the proof
  exact h1
