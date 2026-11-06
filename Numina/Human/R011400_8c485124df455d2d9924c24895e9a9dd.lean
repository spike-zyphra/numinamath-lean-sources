import Mathlib

/- Prove that there exist infinitely many pairs of relatively prime positive integers $a, b>1$ for which $a+b$ divides $a^{b}+b^{a}$. -/
theorem number_theory_245952 :
    {(a, b) : ℕ × ℕ | a > 1 ∧ b > 1 ∧ a.Coprime b ∧ a + b ∣ a ^ b + b ^ a}.Infinite := by
  -- We show that (2n + 3, 2n + 5) satisfies the property for all n ∈ ℕ
  apply Set.infinite_of_injective_forall_mem (f := fun n ↦ (2 * n + 3, 2 * n + 5))
  -- Verify that the function is injective so that it indeed generates infinitely many pairs
  . intro n m h
    simp at h
    exact h
  -- Now we show that (2n + 3, 2n + 5) satisfies the property
  -- 1. (2n + 3, 2n + 5) are coprime
  -- 2. (2n + 3) + (2n + 5) ∣ (2n + 3) ^ (2n + 5) + (2n + 5) ^ (2n + 3)
  intro n
  simp
  constructor
  . -- 1. (2n + 3, 2n + 5) are coprime
    -- We show that 2n + 5 ≡ 2 [MOD 2n + 3]
    -- So gcd(2n + 3, 2n + 5) = gcd(2n + 3, 2) = 1
    have h₁ : 2 * n + 5 ≡ 2 [MOD 2 * n + 3] := Nat.ModEq.symm (Nat.modEq_of_dvd (by simp; ring_nf; simp))
    suffices H : (2 * n + 3).Coprime 2 by
      rw [Nat.Coprime, Nat.gcd_comm] at H ⊢
      rwa [Nat.ModEq.gcd_eq h₁]
    simp
    exact ⟨n + 1, by ring⟩
  . -- 2. (2n + 3) + (2n + 5) ∣ (2n + 3) ^ (2n + 5) + (2n + 5) ^ (2n + 3)
    -- Cast to ℤ for convenience
    zify
    -- We have
    -- h : (2n + 3) + (2n + 5) ∣ (2n + 3) ^ (2n + 5) - (2n + 3) ^ (2n + 3)
    -- Because (2n + 3) ^ 2 - 1 = ((2n + 3) + (2n + 5)) * (n + 1)
    have h : (2 * n + 3 + (2 * n + 5) : ℤ) ∣ (2 * n + 3) ^ (2 * n + 5) - (2 * n + 3) ^ (2 * n + 3) := by
      rw [pow_succ, pow_succ]
      use (2 * n + 3) ^ (2 * n + 3) * (n + 1)
      ring
    -- k : (2n + 3) + (2n + 5) ∣ (2n + 3) ^ (2n + 3) + (2n + 5) ^ (2n + 3)
    -- Because a + b ∣ a ^ n + b ^ n if n is odd
    have k : (2 * n + 3 + (2 * n + 5) : ℤ) ∣ (2 * n + 3) ^ (2 * n + 3) + (2 * n + 5) ^ (2 * n + 3) := Odd.add_dvd_pow_add_pow _ _ ⟨n + 1, by ring⟩
    convert dvd_add h k using 1
    ring
