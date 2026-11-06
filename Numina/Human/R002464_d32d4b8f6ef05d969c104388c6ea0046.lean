import Mathlib
/--
PROBLEM:
Kiana has two older twin brothers. The product of their three ages is 128.  What is the sum of their three ages?
-/
theorem number_theory_1210 (kiana brother : ℕ) (holder : kiana < brother) (hprod : kiana * brother * brother = 128) : kiana + brother + brother = 18 := by
  rw [mul_assoc] at hprod
  --  The twins could be $2^0 = 1, 2^1 = 2, 2^2 = 4, 2^3 = 8$ years of age
  -- Just by considering the divisors of $128$, the twins must have age $2$ raised to some power not more than $7$.
  have : ∃ (b : ℕ), b ≤ 7 ∧ brother = 2 ^ b := by
    rw [← Nat.dvd_prime_pow Nat.prime_two]
    simp
    rw [← hprod, ← mul_assoc]
    exact Nat.dvd_mul_left _ _
  rcases this with ⟨b, hb, rfl⟩
  -- Similarly, Kiana's age is two raised to some power not more than $7$.
  have : ∃ (k : ℕ), k ≤ 7 ∧ kiana = 2 ^ k := by
    rw [← Nat.dvd_prime_pow Nat.prime_two]
    simp
    rw [← hprod]
    exact Nat.dvd_mul_right _ _
  rcases this with ⟨k, hk, rfl⟩
  -- The product of the ages of the siblings is now a sum in terms of their powers
  have hprod :=
    calc
      2 ^ (k + b * 2) = 2 ^ k * (2 ^ b * 2 ^ b) := by ring
      _ = 128 := hprod
      _ = 2 ^ 7 := by simp
  have one_lt_two : 1 < 2 := by norm_num
  have hprod : k + b * 2 = 7 := by apply le_antisymm <;> rw [← Nat.pow_le_pow_iff_right one_lt_two] <;> linarith
  -- Kiana's age being less than the ages of her brothers gives the same inequality on the powers.
  have holder' : k < b := by rwa [← Nat.pow_lt_pow_iff_right one_lt_two]
  -- Now considering the magnitude of the ages of the older brothers, we obtain a better bound that $b ≤ 3$, where $b$ is the power of $2$ in the age of the older brothers.
  have : b ≤ 3 := by
    -- This is because on the one hand that the square of $2^b$ is less than $128$.
    have : b * 2 ≤ 7 := by linarith
    -- and then on the other hand that the square of $b*2$ is even, so it can't be $7$ itself
    have not_seven : b * 2 ≠ 7 := by
      intro contra
      have : 2 ∣ 7 := Dvd.intro_left b contra
      norm_num at this
    have : b * 2 ≤ 6 := by
      apply Nat.le_of_lt_succ
      exact Nat.lt_of_le_of_ne this not_seven
    linarith
  interval_cases b
  -- Let $k$ be the power of $2$ in Kiana's age.
  -- It is not possible that $b=0$ because kiana is younger than her brothers.
  · linarith
  -- It is not possible that $b=1$ because then $k=5$, but kiana is younger than her brothers.
  · linarith
  -- It is not possible that $b=2$ because then $k=3$, but kiana is younger than her brothers.
  · linarith
  -- This leaves $b=3$ and $k=1$, so that the ages of the siblings are $2, 8, 8$, summing to $18$.
  · linarith