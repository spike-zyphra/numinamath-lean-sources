import Mathlib

-- Show that (a^2 + a * b - 6 * b^2 - 2 * a - 16 * b - 8 : ℤ) = 0
-- is equivalent to a = 2 * b + 4.
lemma lemma_1 (a b : ℕ) : (a^2 + a * b - 6 * b^2 - 2 * a - 16 * b - 8 : ℤ) = 0 ↔ a = 2 * b + 4 := by
  symm
  constructor
  -- If a = 2 * b + 4 then the equality holds.
  · intro eq
    simp [eq]
    ring
  intro h
  -- (a^2 + a * b - 6 * b^2 - 2 * a - 16 * b - 8 : ℤ) = 0 is equivalent to
  -- (2 * a + b - 2 : ℤ)^2 = (5 * b + 6)^2.
  have h2 : (2 * a + b - 2 : ℤ) ^ 2 = (5 * b + 6) ^ 2 := by linarith
  -- We get |2 * a + b - 2| = |5 * b + 6|.
  rw [sq_eq_sq_iff_abs_eq_abs] at h2
  -- 2 * a + b - 2 ≥ 0 and 5 * b + 6 ≥ 0 so we get
  -- 2 * a + b - 2 = 5 * b + 6.
  rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by positivity)] at h2
  zify
  -- We get 2 * a = 4 * b + 8, a = 2 * b + 4.
  linarith

/- 3. Find all pairs of natural numbers $a$ and $b$, for which out of the four statements:
1) $a^{2}+4 a+3$ is divisible by $b$;
2) $a^{2}+a b-6 b^{2}-2 a-16 b-8=0$;
3) $a+2 b+1$ is divisible by 4;
4) $a+6 b+1$ is a prime number

three are true, and one is false. -/
theorem number_theory_227428 (a b : ℕ) :
    [b ∣ a^2 + 4 * a + 3, (a^2 + a * b - 6 * b^2 - 2 * a - 16 * b - 8 : ℤ) = 0, 4 ∣ a + 2 * b + 1, Nat.Prime (a + 6 * b + 1)].count False = 1
      ↔ (a = 6 ∧ b = 1) ∨ (a = 18 ∧ b = 7) := by
  constructor
  swap
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    -- Assume that a = 6 and b = 1 and show that exactly one statement is false.
    · norm_num
    -- Assume that a = 18 and b = 7 and show that exactly one statement is false.
    · norm_num
  -- Use lemma_1 to replace (a^2 + a * b - 6 * b^2 - 2 * a - 16 * b - 8 : ℤ) = 0 with a = 2 * b + 4.
  rw [lemma_1]
  intro h
  -- Consider two cases: 4 ∣ a + 2 * b + 1 and ¬ (4 ∣ a + 2 * b + 1).
  by_cases h3 : 4 ∣ a + 2 * b + 1
  · -- If 4 ∣ a + 2 * b + 1 then a ≠ 2 * b + 4.
    have h2 : a ≠ 2 * b + 4 := by
      -- Show that a = 2 * b + 4 implies ¬ (4 ∣ a + 2 * b + 1).
      contrapose! h3
      -- We have a + 2 * b + 1 = 4 * b + 5.
      rw [show a + 2 * b + 1 = 4 * b + 5 by rw [h3]; ring]
      omega
    -- Show that a + 6 * b + 1 is not prime.
    have h4 : ¬ Nat.Prime (a + 6 * b + 1) := by
      -- 4 is not prime. So assume a + 6 * b + 1 ≠ 4.
      by_cases heq : a + 6 * b + 1 = 4
      · rw [heq]
        norm_num
      -- It is enough to show that 4 divides a + 6 * b + 1.
      apply Nat.not_prime_of_dvd_of_ne (m := 4) _ (by norm_num)
      · symm
        exact heq
      -- We have a + 6 * b + 1 = (a + 2 * b + 1) + 4 * b and 4 ∣ a + 2 * b + 1 implies
      -- that 4 ∣ a + 6 * b + 1.
      · omega
    -- We have at least 2 false statement. So the case 4 ∣ a + 2 * b + 1 is impossible.
    simp [h2, h3, h4, List.count_cons] at h
    split_ifs at h <;> norm_num at h
  -- If ¬ (4 ∣ a + 2 * b + 1) then
  -- b ∣ a ^ 2 + 4 * a + 3 ∧ a = 2 * b + 4 ∧ Nat.Prime (a + 6 * b + 1)
  -- (because only one statement could be false).
  have ⟨h1, h2, h4⟩ : b ∣ a ^ 2 + 4 * a + 3 ∧ a = 2 * b + 4 ∧ Nat.Prime (a + 6 * b + 1) := by
    contrapose h
    simp_rw [Decidable.not_and_iff_or_not ] at h
    rcases h with h | h | h <;> simp [h3, h, List.count_cons] <;> split_ifs <;> norm_num
  clear h h3
  -- Replace a with 2 * b + 4 everywhere.
  subst a
  -- We have (2 * b + 4)^2 + 4 * (2 * b + 4) + 3 = b * (4 * b + 24) + 35 so
  -- b ∣ b * (4 * b + 24) + 35 implies that b ∣ 35.
  rw [show (2 * b + 4)^2 + 4 * (2 * b + 4) + 3 = b * (4 * b + 24) + 35 by ring] at h1
  rw [Nat.dvd_add_right (by use 4 * b + 24)] at h1
  -- b is a divisor of 35, so b = 1, 5, 7, or 35.
  have hb : b ∈ (35).divisors := by simp [h1]
  simp [show (35 : ℕ).divisors = {1, 5, 7, 35} from rfl] at hb
  -- Consider all possible values of b and find values for which 2 * b + 4 + 6 * b + 1 is prime.
  rcases hb with rfl | rfl | rfl | rfl <;> norm_num at h4 <;> norm_num