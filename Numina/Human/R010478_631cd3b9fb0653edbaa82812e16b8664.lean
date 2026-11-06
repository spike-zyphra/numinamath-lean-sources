import Mathlib

/- 107. Prove that the equation


$$

x^{2}+x+1=p y

$$


has solutions in integers $(x, y)$ for infinitely many primes $p$. -/
theorem number_theory_276731 :
    ∀ n:ℕ, ∃ p > n, Nat.Prime p ∧ ∃ x y : ℤ, x^2 + x + 1 = p * y := by
  -- Suppose that the equation x^2+x+1=py has integer solutions (x,y) only for a finite number of prime numbers, with some maximum n​.
  by_contra h
  simp at h
  obtain ⟨n,h⟩ := h
  by_cases n > 1
  case neg h_n =>
    apply h 3 (by linarith) Nat.prime_three 1 1
    simp
  case pos h_n =>
    -- Let P be the product of all primes less than n.
    let P : ℕ := ∏ p ∈ (n+1).primesBelow, id p
    -- Then the number P^2+P+1 is not divisible by any prime below n and, consequently, has a prime divisor q greater than n. 
    have h_not_divisible (p:ℕ) (h_prime: Nat.Prime p) (h_le_n: p ≤ n): ¬ p ∣ (P^2 + P + 1) := by
      intro h
      have h_p_dvd_P : p ∣ P := by
        unfold P
        apply Finset.dvd_prod_of_mem
        apply Nat.mem_primesBelow.mpr
        constructor
        . linarith
        . exact h_prime
      have h_p_dvd_P_sq : p ∣ P^2 + P := by
        apply Nat.dvd_add _ h_p_dvd_P
        apply dvd_pow h_p_dvd_P (by trivial)
      apply (Nat.dvd_add_right h_p_dvd_P_sq).mp at h
      aesop
    have : P^2+P+1 ≠ 1 := by
      suffices : P ≠ 0
      . simp
        exact this
      unfold P
      intro h
      apply Finset.prod_eq_zero_iff.mp at h
      simp at h
      apply Nat.mem_primesBelow.mp at h
      apply Nat.not_prime_zero
      simp_all
    obtain ⟨q, h_q_prime, y, h_eq ⟩ := Nat.exists_prime_and_dvd this
    -- Thus, the equation x^2+x+1=qy has an integer solution (P,(P^2+P+1)/q). This leads to a contradiction.
    apply h q ?gt_n h_q_prime P y (by norm_cast)
    case gt_n =>
      by_contra h
      simp at h
      specialize h_not_divisible q h_q_prime h
      apply h_not_divisible
      use y