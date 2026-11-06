import Mathlib

open Nat

/- Prove that the product of the last digit of the number $2^{n}$ and the sum of all the digits of this number, except the last one, is divisible by 3.

# -/
theorem number_theory_184975 (n : ℕ) :
    3 ∣ (2 ^ n % 10) * (Nat.digits 10 (2^n - 2 ^ n % 10)).sum := by
  -- Take care of the n = 0 case first
  have zero_or_pos : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
  rcases zero_or_pos with n_zero | n_pos
  · -- n is zero
    subst n
    simp
  -- n is positive
  -- It suffices to show divisibility by replacing sum of digits with just the number
  suffices 3 ∣ (2 ^ n % 10) * (2 ^ n - 2 ^ n % 10) by
    have prime_three : _ := Nat.prime_three
    -- 3 divides the left or right ractor
    apply Prime.dvd_or_dvd (by rw [← irreducible_iff_nat_prime, irreducible_iff_prime] at prime_three; tauto) at this
    -- Casework on which factor
    rcases this with h | h
    · apply dvd_mul_of_dvd_left
      tauto
    rw [three_dvd_iff] at h
    apply dvd_mul_of_dvd_right
    tauto
  -- Casework on parity of n
  rcases even_or_odd n with n_even | n_odd
  · -- n is even
    -- 2 ^ n is 1 mod 3
    have mod3 : 2 ^ n % 3 = 1 := by
      apply mod_eq_of_modEq _ (by linarith)
      rcases n_even with ⟨x, hx⟩
      rw [← two_mul] at hx
      rw [hx, pow_mul, show 1 = 1 ^ x by simp]
      apply ModEq.pow _
      norm_num
      rw [modEq_iff_dvd]
      omega
    -- 2 ^ n is 4 or 6 mod 10
    have mod10 : 2 ^ n % 10 = 4 ∨ 2 ^ n % 10 = 6 := by
      rcases n_even with ⟨x, hx⟩
      have : 1 ≤ x := by linarith
      rw [← two_mul] at hx
      rw [hx, pow_mul]
      norm_num
      -- Use induction starting at x = 1
      clear hx
      induction x, this using le_induction with
      | base => simp
      | succ m hm ih=> omega
    rcases mod10 with h | h
    · -- 4 mod 10
      apply dvd_mul_of_dvd_right
      omega
    -- 6 mod 10
    -- This case is easy because 3 ∣ 6
    apply dvd_mul_of_dvd_left
    omega
  -- n is odd
  -- 2 ^ n is 2 mod 3
  have mod3 : 2 ^ n % 3 = 2 := by
    rcases n_odd with ⟨x, hx⟩
    rw [hx, pow_add, pow_mul, mul_mod, pow_mod]
    norm_num
  -- 2 ^ n is 2 or 8 mod 10
  have mod10 : 2 ^ n % 10 = 2 ∨ 2 ^ n % 10 = 8 := by
    rcases n_odd with ⟨x, hx⟩
    rw [hx, pow_add, pow_mul]
    norm_num
    clear hx
    induction x with
    | zero => simp
    | succ x ih => omega
  rcases mod10 with h | h
  all_goals
    apply dvd_mul_of_dvd_right
    omega