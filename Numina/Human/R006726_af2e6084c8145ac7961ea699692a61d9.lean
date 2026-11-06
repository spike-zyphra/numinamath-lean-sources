import Mathlib
open Finset Set Nat
noncomputable section

/-Let $k$ be a non-negative integer. Let $N$ be the value $(3^k+3^{k+1})(3^{k+1}+3^{k+2})(3^{k+2}+3^{k+3})(3^{k+3}+3^{k+4})$.
Determine the remainder when the number of positive divisors of $N$ is divided by $1000$. Show that this remainder is $(36k+63) \pmod{1000}$.-/
theorem number_theory_640586 (k : ℕ) :
    ((3^k + 3^(k+1)) * (3^(k+1) + 3^(k+2)) * (3^(k+2) + 3^(k+3)) *
    (3^(k+3) + 3^(k+4))).divisors.card % 1000 = (36 * k + 63) % 1000 := by
  -- Define $N$.
  let N := (3^k + 3^(k+1)) * (3^(k+1) + 3^(k+2)) * (3^(k+2) + 3^(k+3)) * (3^(k+3) + 3^(k+4))

  -- Simplify the expression for $N$ to obtain the prime factorization $N = 2^8 * 3^(4*k+6)$.
  have hN_factor : N = 2^8 * 3^(4*k + 6) := by
    -- Simplify each factor, e.g., $3^k + 3^(k+1) = 2^2 * 3^k$.
    have h1 : 3^k + 3^(k+1) = 2^2 * 3^k := by
      rw [Nat.pow_succ]
      have : 4 = 2^2 := rfl
      rw [← this]
      ring
    have h2 : 3^(k+1) + 3^(k+2) = 2^2 * 3^(k+1) := by
      have : k+2 = k + 1 + 1 := rfl
      rw [this]
      rw [Nat.pow_succ 3 (k + 1)]
      have : 4 = 2^2 := rfl
      rw [← this]
      ring
    have h3 : 3^(k+2) + 3^(k+3) = 2^2 * 3^(k+2) := by
      have : k + 3 = k + 2 + 1 := rfl
      rw [this]
      rw [Nat.pow_succ 3 (k + 2)]
      have : 4 = 2^2 := rfl
      rw [← this]
      ring
    have h4 : 3^(k+3) + 3^(k+4) = 2^2 * 3^(k+3) := by
      have : k + 4 = k + 3 + 1 := rfl
      rw [this]
      rw [Nat.pow_succ 3 (k + 3)]
      have : 4 = 2^2 := rfl
      rw [← this]
      ring
    -- Substitute the simplified factors into $N$.
    unfold N
    rw [h1, h2, h3, h4]
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc]
    ring

  -- Calculate the number of positive divisors of $N$, $d(N) = (8+1) * ((4*k+6)+1) = 9 * (4*k+7) = 36*k + 63$.
  have h_divisors : N.divisors.card = 36 * k + 63 := by
    rw [hN_factor]
    -- Use prime factorization to calculate the number of divisors.
    have hN_nonzero : 2^8 * 3^(4*k + 6) ≠ 0 := by
      apply Nat.mul_ne_zero
      · exact pow_ne_zero 8 (by norm_num)
      · exact pow_ne_zero (4*k + 6) (by norm_num)
    have : (2^8 * 3^(4*k + 6)).divisors.card = ∏ x ∈ (2^8 * 3^(4*k + 6)).primeFactors, ((2^8 * 3^(4*k + 6)).factorization x + 1) := by
      apply Nat.card_divisors hN_nonzero
    rw [this]
    have h_prime_factors : (2^8 * 3^(4*k + 6)).primeFactors = {2, 3} := by
      rw [Nat.primeFactors_mul]
      · have h_nezero1: 4 * k + 6 ≠ 0 := by omega
        have h_nezero2: 8 ≠ 0 := by linarith
        rw [Nat.primeFactors_pow , Nat.primeFactors_pow ]
        have h_p2 : Nat.Prime 2 := by norm_num
        have h_p3 : Nat.Prime 3 := by norm_num
        simp [Nat.Prime.primeFactors h_p2,Nat.Prime.primeFactors h_p3]
        rfl
        exact h_nezero1
        exact h_nezero2
      · exact pow_ne_zero 8 (by norm_num)
      · exact pow_ne_zero (4*k + 6) (by norm_num)
    rw [h_prime_factors]
    -- Calculate the factorization of $N$.
    have h_factorization_2 : (2^8 * 3^(4*k + 6)).factorization 2 = 8 := by
      rw [Nat.factorization_mul, Nat.factorization_pow, Nat.factorization_pow]
      simp
      · norm_num
      · exact pow_ne_zero 8 (by norm_num)
      · exact pow_ne_zero (4*k + 6) (by norm_num)
    have h_factorization_3 : (2^8 * 3^(4*k + 6)).factorization 3 = 4*k + 6 := by
      rw [Nat.factorization_mul, Nat.factorization_pow, Nat.factorization_pow]
      simp
      · norm_num
      · exact pow_ne_zero 8 (by norm_num)
      · exact pow_ne_zero (4*k + 6) (by norm_num)
    -- Substitute the factorization.
    have : ∏ x ∈ ({2, 3} : Finset ℕ), ((2^8 * 3^(4*k + 6)).factorization x + 1) = (8 + 1) * ((4*k + 6) + 1) := by
      rw [Finset.prod_pair]
      · rw [h_factorization_2, h_factorization_3]
      · norm_num
    -- Simplify the expression.
    have h₁: 8 + 1 = 9 := by norm_num
    have h₂: 4 * k + 6 + 1 = 4 * k + 7 := by ring
    have h₃: 9 * (4 * k + 7) = 36 * k + 63 := by ring
    rw [this, h₁, h₂, h₃]

  -- Prove that $d(N) mod 1000 = (36*k + 63) mod 1000$.
  have h_mod : N.divisors.card % 1000 = (36 * k + 63) % 1000 := by
    rw [h_divisors]

  -- Final goal.
  exact h_mod
