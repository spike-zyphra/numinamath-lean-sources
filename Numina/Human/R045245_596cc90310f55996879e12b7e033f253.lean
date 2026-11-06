import Mathlib

/- Without using a calculator, find the largest prime factor of $15^4+2\times15^2+1-14^4$. -/
theorem algebra_10704 : IsGreatest {p | p.Prime ∧ p ∣ (15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4)} 211 := by
  -- We may not use the power of calculator.
  simp only [IsGreatest, upperBounds, Set.mem_setOf]
  -- A factorization of the given quantity.
  have h : 2 * 2 * 3 * 5 * 211 = 15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4 := by
    calc
      2 * 2 * 3 * 5 * 211 = ((15 - 14) * (15 + 14) + 1) * (2 * 211) := by norm_num
      _ = (15 ^ 2 - 14 ^ 2 + 1) * (2 * 211) := by nth_rewrite 2 [mul_comm]; rw [Nat.sq_sub_sq]
      _ = (15 ^ 2 + 1 - 14 ^ 2) * (15 ^ 2 + 1 + 14 ^ 2) := by norm_num
      _ = (15 ^ 2 + 1) ^ 2 - (14 ^ 2) ^ 2 := by rw [Nat.sq_sub_sq, mul_comm]
      _ = (15 ^ 2) ^ 2 + 2 * 15 ^ 2 * 1 + 1 - (14 ^ 2) ^ 2 := by rw [add_pow_two, Nat.one_pow]
      _ = 15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4 := by rw [mul_one, <-Nat.pow_mul, <-Nat.pow_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  . -- Prove that 211 is a prime. We need decide (according to the solution, no more stpes provided.)
    exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
  . -- Prove that 211 divides 15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4.
    rw [h.symm]
    apply Nat.dvd_mul_left
  . -- Prove that any prime divisor of the quantity is not more than 211.
    rw [h.symm]
    have g : Nat.primeFactorsList (2 * 2 * 3 * 5 * 211) = [2, 2, 3, 5, 211] := by
      -- We need native_decide to show that 2, 3, 5, 211 are primes.
      native_decide
    intro a ⟨h₀, h₁⟩
    have h₂ : 2 * 2 * 3 * 5 * 211 ≠ 0 := by
      norm_num
    rw [(Nat.mem_primeFactorsList_iff_dvd h₂ h₀).symm, g] at h₁
    clear h g h₀ h₂
    -- Now we have a ∈ [2, 2, 3, 5, 211].
    simp at h₁
    obtain h₁ | h₁ | h₁ | h₁ := h₁
    all_goals
      rw [h₁]
      try norm_num
