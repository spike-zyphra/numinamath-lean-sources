import Mathlib
open Nat Real Finset Set
noncomputable section

/-8. The product of all the factors of $5^{15}$ is $5^{P}$. What is the value of $P$ ?-/
theorem number_theory_600014 (P : ℕ) (h : ∏ x ∈ (Nat.divisors (5^15)), x = 5^P) : P = 120 := by
  have h₁ : P = 120 := by
    rw [show (∏ x ∈ Nat.divisors (5 ^ 15), x) = 5 ^ 120 by
      rw [show (5 : ℕ) ^ 15 = 5 ^ 15 by rfl]
      rw [Nat.divisors_prime_pow (by decide : Nat.Prime 5)]
      -- Compute the product of all divisors.
      simp [Finset.prod_range_succ', Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    ] at h
    -- Compare the exponents.
    apply Nat.pow_right_injective (by norm_num : 1 < 5)
    linarith
  exact h₁