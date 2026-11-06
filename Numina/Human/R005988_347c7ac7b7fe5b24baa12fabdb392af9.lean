import Mathlib

/-If a positive integer multiple of 864 is picked randomly, with each multiple having the same probability of being picked, what is the probability that it is divisible by 1944 ?-/
theorem number_theory_60864 (a b : ℕ) (ha : a = 864) (hb : b = 1944) :
  (a.gcd b : ℚ) / b = 1 / 9 := by
  -- Factorize $a = 864$ and $b = 1944$ into prime factors.
  have h_a_factorization : a = 2^5 * 3^3 := by omega
  have h_b_factorization : b = 2^3 * 3^5 := by omega

  -- Compute $gcd(a, b)$.
  have h_gcd : a.gcd b = 2^3 * 3^3 := by
    rw [h_a_factorization,h_b_factorization]
    simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_assoc]

  -- Compute the probability $gcd(a, b) / b = 1/9$.
  have h_probability : (a.gcd b : ℚ) / b = 1 / 9 := by
    rw [h_gcd, hb,]
    norm_num
  exact h_probability