import Mathlib

/- (1453, 3019) -/
abbrev number_theory_4962_solution : (ℕ × ℕ) := (1453, 3019)

/-
Find the prime numbers $ p $ and $ q $ such that their product $ n = p \times q = 4386607 $ and the value of Euler's totient function $ \phi(n) = 4382136 $.
-/
theorem number_theory_4962 :
    number_theory_4962_solution.1 < number_theory_4962_solution.2 ∧
    Nat.Prime number_theory_4962_solution.1 ∧
    Nat.Prime number_theory_4962_solution.2 ∧
    number_theory_4962_solution.1 * number_theory_4962_solution.2 = 4386607 ∧
    Nat.totient (number_theory_4962_solution.1 * number_theory_4962_solution.2) = 4382136 := by
  set p := number_theory_4962_solution.1
  set q := number_theory_4962_solution.2
  have hlt : p < q := by linarith
  have hpp : p.Prime := by norm_num
  have hqp : q.Prime := by norm_num
  have hmul : p * q = 4386607 := by norm_num


  have ht : (p*q).totient = 4382136 := by
    -- φ (p * q) = φ p * φ q
    rw [Nat.totient_mul ((Nat.coprime_primes hpp hqp).mpr (show p ≠ q by simp))]
    -- φ p = p - 1
    rw [(Nat.totient_eq_iff_prime (show 0 < p by linarith)).mpr hpp]
    -- φ q = q - 1
    rw [(Nat.totient_eq_iff_prime (show 0 < q by linarith)).mpr hqp]
    norm_num

  exact ⟨hlt, hpp, hqp, hmul, ht⟩
